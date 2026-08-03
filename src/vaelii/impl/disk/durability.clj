;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.disk.durability
  "Durability management for the disk backend.  Each disk store/kv registers itself
  here on open; one daemon fsyncs every registrant on a tick (default 3 s), and one
  JVM shutdown hook closes them all on exit.  Without it, a crash between manual
  fsyncs loses everything since the last one.

  Registration is capability-based — callers hand in `{:fsync :close :label}` (plus an
  optional `{:compact :dead-ratio}` for background compaction), so this namespace does
  not depend on the stores it drives (which would cycle).

  Config (system properties): `vaelii.disk.sync-ms` (tick interval, 0 disables the
  daemon), `vaelii.disk.auto-compact` (off with `false`/`0`/`off`),
  `vaelii.disk.compact-dead-ratio` (default 0.5),
  `vaelii.disk.compact-min-interval-ms` (default 300000)."
  (:require [taoensso.trove :as trove])
  (:import [java.util.concurrent Executors ExecutorService ScheduledExecutorService TimeUnit]))

(defn- prop-long [k default]
  (if-let [s (System/getProperty k)] (Long/parseLong s) default))

(defn- prop-double [k default]
  (if-let [s (System/getProperty k)] (Double/parseDouble s) default))

(defn- fsync-interval-ms [] (prop-long "vaelii.disk.sync-ms" 3000))
(defn auto-compact?
  "Is background/opportunistic compaction enabled (`vaelii.disk.auto-compact`)?  Public
  because the close path consults the same switch the tick does — one knob, not two."
  []
  (not (#{"0" "false" "off" "no"} (System/getProperty "vaelii.disk.auto-compact"))))

(defn compact-dead-ratio
  "The dead-ratio a log must reach to be worth compacting
  (`vaelii.disk.compact-dead-ratio`, default 0.5).  Public for the same reason."
  []
  (prop-double "vaelii.disk.compact-dead-ratio" 0.5))
(defn- compact-min-interval-ms [] (prop-long "vaelii.disk.compact-min-interval-ms" 300000))

(defonce ^:private registry (atom {}))
(defonce ^:private next-id (atom 0))
(defonce ^:private scheduler (atom nil))
(defonce ^:private shutdown-hook (atom nil))
(defonce ^:private compaction-executor (atom nil))
(defonce ^:private compaction-in-flight (atom #{}))
(defonce ^:private last-compact-ms (atom {}))
(defonce ^:private compaction-paused (atom false))

(defn pause-compaction!
  "Suspend the daemon's background auto-compaction across every registered backend.
  For a bulk load, whose monotonic delta accumulation trips the dead-ratio trigger
  repeatedly and would rewrite a growing multi-GB index mid-load — stalling the writer
  on the backend lock each time — pause for the load's duration and let the next tick
  compact once afterwards.  Idempotent; pair with `resume-compaction!`, or wrap the load
  in `call-with-compaction-paused`.  Only the daemon's automatic firing is gated: a
  manual `compact!` and the dead-ratio bookkeeping are untouched."
  [] (reset! compaction-paused true))

(defn resume-compaction!
  "Re-enable background auto-compaction paused by `pause-compaction!`.  The next flush
  tick compacts any backend whose dead ratio has crossed the threshold."
  [] (reset! compaction-paused false))

(defn call-with-compaction-paused
  "Run `thunk` with background auto-compaction paused, resuming on the way out (even on
  throw).  A no-op in effect when no disk backend is registered."
  [thunk]
  (pause-compaction!)
  (try (thunk) (finally (resume-compaction!))))

(defn- fsync-one-safely [{:keys [fsync label]}]
  (try (fsync {:fsync? true})
       (catch Throwable t
         (trove/log! {:level :error :msg (str "disk-durability fsync of " label " failed: "
                                              (.getMessage t))}))))

(defn- close-one-safely! [{:keys [close label]}]
  (try (close)
       (catch Throwable t
         (trove/log! {:level :error :msg (str "disk-durability close of " label " failed: "
                                              (.getMessage t))}))))

(defn- ensure-compaction-executor! ^ExecutorService []
  (or @compaction-executor
      (let [ex (Executors/newSingleThreadExecutor
                (reify java.util.concurrent.ThreadFactory
                  (newThread [_ r] (doto (Thread. r "disk-auto-compactor") (.setDaemon true)))))]
        (reset! compaction-executor ex)
        ex)))

(defn- submit-compaction! [id label compact-fn ratio threshold]
  (swap! compaction-in-flight conj id)
  (.submit (ensure-compaction-executor!)
           ^Runnable
           (fn []
             (try
               ;; The store can close between the tick that queued this and the executor
               ;; reaching it — the executor is single-threaded, so a task waits behind
               ;; every task before it, and `close-dir!` deregisters BEFORE closing the
               ;; log.  This check honours that signal and skips the task with a log
               ;; line saying why.
               ;;
               ;; It is the *early* skip, not the airtight one: it runs outside the
               ;; store's own lock, so a close can still land between here and
               ;; `compact!` acquiring it.  What closes that window is the store — the
               ;; disk KV consults its closed flag after taking its lock
               ;; (`vaelii.impl.disk.kv/compact!`), and the record store's compaction
               ;; throws on its closed idx before any temp or marker is written.  A
               ;; task already INSIDE `compact!` needs neither: it holds the store
               ;; lock, which is exactly what `close!` blocks on.
               (if-not (contains? @registry id)
                 (trove/log! {:level :debug
                              :msg (str "disk-durability skipping the queued auto-compaction of "
                                        label " — it closed before the queue reached it")})
                 (do
                   (trove/log! {:level :info
                                :msg (format "disk-durability auto-compacting %s — dead ratio %.2f ≥ %.2f"
                                             label ratio threshold)})
                   (compact-fn)))
               (catch Throwable t
                 (trove/log! {:level :error :msg (str "disk-durability auto-compact of " label
                                                      " failed: " (.getMessage t))}))
               (finally
                 (swap! last-compact-ms assoc id (System/currentTimeMillis))
                 (swap! compaction-in-flight disj id))))))

(defn- maybe-compact! []
  (when (and (auto-compact?) (not @compaction-paused))
    (let [now       (System/currentTimeMillis)
          interval  (compact-min-interval-ms)
          threshold (compact-dead-ratio)]
      (doseq [[id {:keys [compact dead-ratio label]}] @registry
              :when (and compact dead-ratio
                         (not (contains? @compaction-in-flight id))
                         (>= (- now (get @last-compact-ms id 0)) interval))]
        (let [ratio (try (double (dead-ratio)) (catch Throwable _ 0.0))]
          (when (>= ratio threshold)
            (submit-compaction! id label compact ratio threshold)))))))

(defn- fsync-all []
  ;; top-level guard: scheduleAtFixedRate permanently suppresses a task that throws,
  ;; so swallow everything and let the next tick retry.
  (try
    (doseq [entry (vals @registry)] (fsync-one-safely entry))
    (maybe-compact!)
    (catch Throwable t
      (trove/log! {:level :error :msg (str "disk-durability fsync tick failed: "
                                           (.getName (class t)))}))))

(defn- close-all! [] (doseq [entry (vals @registry)] (close-one-safely! entry)))

(defn- start-scheduler! [interval-ms]
  (when (and (pos? interval-ms) (nil? @scheduler))
    (let [ex (Executors/newSingleThreadScheduledExecutor
              (reify java.util.concurrent.ThreadFactory
                (newThread [_ r] (doto (Thread. r "disk-durability-syncer") (.setDaemon true)))))]
      (.scheduleAtFixedRate ex ^Runnable fsync-all interval-ms interval-ms TimeUnit/MILLISECONDS)
      (reset! scheduler ex))))

(defn- install-shutdown-hook! []
  (when (nil? @shutdown-hook)
    (let [t (Thread. ^Runnable close-all! "disk-durability-shutdown")]
      (.addShutdownHook (Runtime/getRuntime) t)
      (reset! shutdown-hook t))))

(defn register!
  "Register a disk backend with the durability manager.  Entry keys: `:fsync` (fn
  `[{:keys [fsync?]}]`, required), `:close` (fn `[]`, required), `:label` (string,
  required), and optionally `:compact` (fn `[]`) + `:dead-ratio` (fn `[]` → double)
  for background compaction.  Returns an id for `deregister!`; starts the scheduler
  and installs the shutdown hook on first registration."
  [{:keys [fsync close label] :as entry}]
  (assert (fn? fsync) ":fsync must be a fn")
  (assert (fn? close) ":close must be a fn")
  (assert (string? label) ":label must be a string")
  (let [id (swap! next-id inc)]
    (swap! registry assoc id entry)
    (install-shutdown-hook!)
    (start-scheduler! (fsync-interval-ms))
    id))

(defn deregister!
  "Remove a registered backend.  Idempotent."
  [id]
  (when id (swap! registry dissoc id)))

(defn stop!
  "Stop the schedulers (REPL/test teardown).  Leaves the shutdown hook installed."
  []
  (when-let [ex @scheduler] (.shutdown ^ScheduledExecutorService ex) (reset! scheduler nil))
  (when-let [cx @compaction-executor] (.shutdown ^ExecutorService cx) (reset! compaction-executor nil)))

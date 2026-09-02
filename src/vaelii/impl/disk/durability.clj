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
  daemon), `vaelii.disk.auto-compact`, `vaelii.disk.compact-dead-ratio` (default 0.5),
  `vaelii.disk.compact-min-interval-ms` (default 300000).  Every one is read through
  `vaelii.impl.config`, which owns their domains and refuses a value outside one —
  and the two the tick reads are why `config/check!` runs at the open: a refusal *here*
  lands inside `fsync-all`'s `catch Throwable` below, which logs a class name every
  three seconds and leaves auto-compaction dead."
  (:require [clojure.string :as str]
            [taoensso.trove :as trove]
            [vaelii.impl.config :as config])
  (:import [java.util.concurrent Executors ExecutorService ScheduledExecutorService TimeUnit]))

(defn auto-compact?
  "Is background/opportunistic compaction enabled (`vaelii.disk.auto-compact`)?  Public
  because the close path consults the same switch the tick does — one knob, not two."
  []
  (config/disk-auto-compact?))

(defn compact-dead-ratio
  "The dead-ratio a log must reach to be worth compacting
  (`vaelii.disk.compact-dead-ratio`, default 0.5).  Public for the same reason."
  []
  (config/disk-compact-dead-ratio))

(defonce ^:private registry (atom {}))
(defonce ^:private next-id (atom 0))
(defonce ^:private scheduler (atom nil))
(defonce ^:private shutdown-hook (atom nil))
(defonce ^:private compaction-executor (atom nil))
(defonce ^:private compaction-in-flight (atom #{}))
(defonce ^:private last-compact-check-ms
  ;; `{registrant-id ms}` — when each backend's dead ratio was last **asked for**, which
  ;; is what `vaelii.disk.compact-min-interval-ms` throttles.  Asking is not free: a
  ;; record store answers it by scanning every `.idx` in full under the kind lock
  ;; (`record-store/kind-dead-ratio`), so a stamp taken only where a compaction *fired*
  ;; would leave a store that never crosses the threshold paying that scan on every
  ;; three-second tick, for the life of the process.  Stamped before the ratio is read
  ;; and again when a compaction finishes, so the interval floors the probe and the
  ;; rewrite alike.
  (atom {}))
(defonce ^:private compaction-paused (atom false))
(defonce ^:private compaction-stopped
  ;; Set by `stop!` under `lifecycle`, cleared by the next `register!` under the same
  ;; monitor.  Without it a tick already inside `submit-compaction!` when `stop!` ran
  ;; read the executor atom `stop!` had just nil'd and built a **replacement** nobody
  ;; holds a reference to — so `stop!`'s contract ("the schedulers are stopped") was
  ;; false the moment it returned, and the new executor lived until JVM exit.  A flag
  ;; rather than a non-nil tombstone in the executor atom, because the atom's nil is
  ;; also what "not started yet" looks like and the two must stay distinguishable.
  (atom false))

;; The monitor the three process-wide singletons above — the scheduler, the compaction
;; executor and the shutdown hook — are created and torn down under.  A check-then-act on
;; each atom alone is not enough: two `register!`s racing the first one would each build a
;; ticker over the one registry, so every registrant is fsynced twice a tick and only one
;; of the two tickers is reachable by `stop!` — the loser runs for the life of the
;; process.  One monitor rather than one apiece, because `register!` reaches two of the
;; three and `stop!` shuts two down, so what has to be serialized is the *set*.
(defonce ^:private lifecycle (Object.))

;; Notified whenever an id leaves `compaction-in-flight`; waited on by
;; `await-compaction-quiescent!`.  Its own monitor rather than `lifecycle`: a waiter
;; holds this one for the whole join, and holding `lifecycle` there would block every
;; `register!` in the process behind one directory's close.
(defonce ^:private ^Object quiescence (Object.))

(defn- leave-flight! [id]
  (swap! compaction-in-flight disj id)
  (locking quiescence (.notifyAll quiescence)))

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
  (try (fsync {})
       (catch Throwable t
         (trove/log! {:level :error :msg (str "disk-durability fsync of " label " failed: "
                                              (.getMessage t))}))))

(defn- close-one-safely! [{:keys [close label]}]
  (try (close)
       (catch Throwable t
         (trove/log! {:level :error :msg (str "disk-durability close of " label " failed: "
                                              (.getMessage t))}))))

(defn- ensure-compaction-executor!
  "The compaction executor, built on first use — or **nil** once `stop!` has run and
  before the next `register!`, which is the point: the tick that loses the race with
  `stop!` gets here after the atom was nil'd, and must skip rather than build the
  replacement that made `stop!` a lie.  Checked under `lifecycle`, the monitor `stop!`
  sets the flag under, so the two cannot interleave."
  ^ExecutorService []
  (or @compaction-executor
      (locking lifecycle
        (when-not @compaction-stopped
          (or @compaction-executor
              (let [ex (Executors/newSingleThreadExecutor
                        (reify java.util.concurrent.ThreadFactory
                          (newThread [_ r] (doto (Thread. r "disk-auto-compactor")
                                             (.setDaemon true)))))]
                (reset! compaction-executor ex)
                ex))))))

(defn- submit-compaction! [id label compact-fn ratio threshold]
  ;; The id goes in flight **before** the submit, so the tick three seconds from now
  ;; cannot queue a second rewrite of a backend whose first one has not started.  Which
  ;; makes the refused submit the case to handle: `stop!` can shut the executor between
  ;; the probe and here, the task then never runs, its `finally` never clears the id, and
  ;; `maybe-compact!` skips a backend that is in flight — so that backend would go
  ;; un-compacted for the life of the process, over one rejected submit.
  ;;
  ;; Every path out of the in-flight set goes through `leave-flight!`, because the set is
  ;; also what `await-compaction-quiescent!` waits on: an id dropped without the notify
  ;; leaves a closing directory waiting out its whole timeout for a task that finished.
  (swap! compaction-in-flight conj id)
  (try
    (if-let [ex (ensure-compaction-executor!)]
      (.submit
       ex
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
           ;; `compact!` acquiring it.  What closes that window differs by store, and
           ;; only one of the two closes it on its own.  The disk KV does: it holds
           ;; its lock for the whole of `compact!` and consults its closed flag after
           ;; taking it, so a task already inside it blocks the close rather than
           ;; racing it.  **The record store does not**, and by design — its rewrite
           ;; phase runs lock-free over a private read handle so an O(bytes) copy does
           ;; not stall the kind's reads and writes, which means a task inside
           ;; `compact!` holds no lock a `close!` blocks on and is still appending to
           ;; `sentexes.log.compact` by name when the directory's OS lock is released.  What
           ;; closes it for that store is the close itself: `backend/close-dir!`
           ;; aborts the rewrite and then waits here, through
           ;; `await-compaction-quiescent!`, before it releases the lock.
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
             ;; re-stamped at the *end* of the rewrite, so the floor is measured from
             ;; when the backend was last left alone rather than from when the probe
             ;; that queued this ran
             (swap! last-compact-check-ms assoc id (System/currentTimeMillis))
             (leave-flight! id)))))
      ;; stopped between the probe and here: skip, and leave nothing in flight — the
      ;; same bookkeeping the rejected submit below owes, for the same reason
      (do (leave-flight! id)
          (trove/log! {:level :debug
                       :msg (str "disk-durability not queuing the auto-compaction of "
                                 label " — the compaction executor is stopped")})
          nil))
    (catch Throwable t
      (leave-flight! id)
      (trove/log! {:level :warn
                   :msg (str "disk-durability could not queue the auto-compaction of "
                             label ": " (.getMessage t))})
      nil)))

(defn- maybe-compact!
  "One pass over the registrants: probe each backend's dead ratio and queue a rewrite
  where it has crossed the threshold.

  **`vaelii.disk.compact-min-interval-ms` gates the probe, not just the rewrite.**  A
  ratio is a measurement a store has to take, and the record store takes it by scanning
  every `.idx` in full under the kind lock — so gating only the rewrite would leave a
  store whose ratio never crosses the threshold paying that scan on every tick, which is
  the tick that exists to fsync.  Stamping the probe makes the interval a floor on both,
  and the cost of that is detection latency bounded by the same interval — which is
  what the floor already promised the rewrite."
  []
  (when (and (auto-compact?) (not @compaction-paused))
    (let [now       (System/currentTimeMillis)
          interval  (config/disk-compact-min-interval-ms)
          threshold (compact-dead-ratio)]
      (doseq [[id {:keys [compact dead-ratio label]}] @registry
              :when (and compact dead-ratio
                         (not (contains? @compaction-in-flight id))
                         (>= (- now (get @last-compact-check-ms id 0)) interval))]
        (swap! last-compact-check-ms assoc id now)
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

(def ^:private close-phases
  "The order `close-all!` closes registrants in, lowest first.

    :image   a derived structure written out *whole* on close and stamped against
             another component's live state — the mapped index snapshot.  It has to be
             written while that component is still open, so it goes first
    :store   a component owning a WAL and file handles, closed after

  Registration order says nothing about this dependency: the registry holds every
  directory at once, a record store registers when its KB's `:records` axis resolves and
  the snapshot writer only after the whole KB value exists.  Closing in insertion order
  therefore closes the records out from under the image's own stamp, which throws — and
  the throw is caught and logged, so the image is simply never written.  `close-dir!`
  runs the same two phases explicitly for one directory; this is the JVM-shutdown path."
  {:image 0 :store 1})

(defn- close-all! []
  ;; `sort-by` is stable, so registrants within a phase keep their registration order
  (doseq [entry (sort-by #(close-phases (:phase % :store) 1) (vals @registry))]
    (close-one-safely! entry)))

(defn- start-scheduler! [interval-ms]
  (when (and (pos? interval-ms) (nil? @scheduler))
    (locking lifecycle
      (when (nil? @scheduler)
        (let [ex (Executors/newSingleThreadScheduledExecutor
                  (reify java.util.concurrent.ThreadFactory
                    (newThread [_ r] (doto (Thread. r "disk-durability-syncer")
                                       (.setDaemon true)))))]
          (.scheduleAtFixedRate ex ^Runnable fsync-all interval-ms interval-ms
                                TimeUnit/MILLISECONDS)
          (reset! scheduler ex))))))

(defn- install-shutdown-hook! []
  (when (nil? @shutdown-hook)
    (locking lifecycle
      (when (nil? @shutdown-hook)
        (let [t (Thread. ^Runnable close-all! "disk-durability-shutdown")]
          (.addShutdownHook (Runtime/getRuntime) t)
          (reset! shutdown-hook t))))))

(defn register!
  "Register a disk backend with the durability manager.  Entry keys: `:fsync` (fn of one
  argument, required — the tick hands it an options map, which it passes empty), `:close`
  (fn `[]`, required), `:label` (string, required), optionally `:compact` (fn `[]`) +
  `:dead-ratio` (fn `[]` → double) for background compaction, and optionally `:phase`
  (`close-phases`, `:store` by default) for shutdown ordering.  Returns an id for
  `deregister!`; starts the scheduler and installs the shutdown hook on first
  registration, both under `lifecycle` so concurrent first registrations install one
  apiece rather than one each.

  The shape check is an `ex-info` rather than an `assert` because `clojure.core/assert`
  is **elidable**: with `*assert*` false a registrant with no `:close` would register
  cleanly and then be silently skipped on shutdown, which is the whole of what this
  namespace does for it."
  [{:keys [fsync close label phase] :as entry}]
  (doseq [[k v pred what] [[:fsync fsync fn?     "a fn"]
                           [:close close fn?     "a fn"]
                           [:label label string? "a string"]]]
    (when-not (pred v)
      (throw (ex-info (str "a durability registrant's " k " must be " what ", got "
                           (pr-str v))
                      {:type :bad-registrant :key k :value v :label label}))))
  (when-not (or (nil? phase) (contains? close-phases phase))
    (throw (ex-info (str "unknown durability :phase " (pr-str phase) " — want "
                         (str/join " or " (map pr-str (sort-by close-phases
                                                               (keys close-phases)))))
                    {:type :bad-registrant :key :phase :value phase :label label})))
  (let [id (swap! next-id inc)]
    (swap! registry assoc id entry)
    (install-shutdown-hook!)
    ;; under `lifecycle` for the reason `stop!` sets it there: a registration is a
    ;; declaration that this process is using disk again, and it un-stops the compactor
    ;; the same way it restarts the ticker below
    (locking lifecycle (reset! compaction-stopped false))
    (start-scheduler! (config/disk-sync-ms))
    id))

(defn deregister!
  "Remove a registered backend.  Idempotent."
  [id]
  (when id (swap! registry dissoc id)))

(def ^:private quiesce-timeout-ms
  "How long `await-compaction-quiescent!` waits before giving up and saying so.  Long
  enough that no honest rewrite hits it — an aborted one stops at its next frame check
  and a KV rewrite is bounded by the live key count — and short enough that a wedged
  compactor does not hang a close forever.  Not a config knob: a caller that has to tune
  this has a bug behind it, and the log line names which store."
  30000)

(defn await-compaction-quiescent!
  "Block until none of `ids` has an auto-compaction in flight.  Returns true when they
  are quiet, false on the timeout (logged, naming the ids that would not settle).

  **What it is for.**  The compaction executor runs a rewrite on its own thread, and the
  record store's rewrite phase deliberately holds no lock while it does — so a caller
  that is about to hand the directory to somebody else (`backend/close-dir!`, before
  `lock/release!`) cannot learn from any lock that the rewrite is done.  It has to ask
  here.  Pair it with the store's own `abort-compaction!`: the abort is what makes the
  wait short, this is what makes it correct.

  Waiting on `compaction-in-flight` rather than on the executor itself, because the
  executor is process-wide and one directory's close has no business joining another
  directory's rewrite.  The set is read under the same monitor the notify takes, so a
  task that finishes between the read and the wait cannot be missed."
  ([ids] (await-compaction-quiescent! ids quiesce-timeout-ms))
  ([ids timeout-ms]
   (let [ids (set (remove nil? ids))]
     (if (empty? ids)
       true
       (let [deadline (+ (System/currentTimeMillis) (long timeout-ms))]
         (locking quiescence
           (loop []
             (let [busy (filterv ids @compaction-in-flight)
                   left (- deadline (System/currentTimeMillis))]
               (cond
                 (empty? busy) true
                 (not (pos? left))
                 (do (trove/log!
                      {:level :error
                       :msg (str "disk-durability waited " timeout-ms
                                 "ms for the auto-compaction of " (pr-str busy)
                                 " to finish and it has not — proceeding, so a rewrite"
                                 " may still be writing this directory's temp files")})
                     false)
                 :else (do (.wait quiescence left) (recur)))))))))))

(defn stop!
  "Stop the schedulers (REPL/test teardown).  Leaves the shutdown hook installed.  Under
  the same monitor the starts take, so a `register!` racing this either installs before it
  or re-installs after it, never half-way through it.

  The stopped flag is the half a `reset!` to nil cannot do: a tick already inside
  `submit-compaction!` reads the nil'd atom, and without the flag it builds a
  *replacement* executor — one nothing holds a reference to, so `stop!` returned having
  stopped nothing.  Cleared by the next `register!`, which is what a REPL teardown
  followed by a fresh open looks like."
  []
  (locking lifecycle
    (reset! compaction-stopped true)
    (when-let [ex @scheduler]
      (.shutdown ^ScheduledExecutorService ex)
      (reset! scheduler nil))
    (when-let [cx @compaction-executor]
      (.shutdown ^ExecutorService cx)
      (reset! compaction-executor nil))))

;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.disk.backend
  "The durable-store entry point: open (once per directory) a `DiskRecordStore` and/or a
  `KvIndexStore` over a `DiskKvBackend`, take the single-writer lock, and wire what was
  opened to the durability daemon.

  **The two halves open independently.**  A KB's records and its index are chosen on
  separate axes (`vaelii.impl.kb`), and only one of the combinations that reach here
  wants both: `:disk` is durable records *and* a durable index, while `:disk-memory` /
  `:disk-dense` / `:disk-columnar` keep the derived index in RAM and want the record store
  alone — no index log, no index WAL, nothing written to the directory but the records.  So each
  component is opened on first use rather than as a pair, and the registry records which
  ones a directory actually has.  A directory opened both ways in one JVM therefore
  shares its record store across both KBs and hands the RAM-index one no durable index
  at all.

  A process-global registry keyed by canonical directory mirrors the memory backend's
  space registry: two KBs constructed over the same directory share one set of
  stores — so a KB \"restarted\" over the same directory in one JVM (the recovery
  tests) sees the durable records the first wrote, with its own fresh taxonomy/TMS, and
  the file handles + durability registration + lock are taken once rather than leaking
  across the suite's hundreds of KB constructions.  A true cross-JVM restart opens the
  directory fresh and rebuilds the RAM state from the durable logs."
  (:require [clojure.java.io :as io]
            [taoensso.trove :as trove]
            [vaelii.impl.disk.durability :as dur]
            [vaelii.impl.disk.kv :as dkv]
            [vaelii.impl.disk.lock :as lock]
            [vaelii.impl.disk.record-store :as drs]
            [vaelii.impl.kv :as kv]))

;; canonical dir -> {:dir d :records <RecordStore>? :index <KvIndexStore>? :dur-ids {kind id}}
;; — the component keys are present only for what was actually opened.
(defonce ^:private stores (atom {}))

(defn canonical-dir
  "`dir`'s canonical path — the identity a directory's stores are keyed by, and what
  anything else keying state off a disk KB's directory (the derived index's shared
  state, `vaelii.impl.kb`) must key on too, so two spellings of one directory are one
  KB rather than two."
  [dir]
  (.getCanonicalPath (io/file dir)))

(defn- open-component!
  "Open one durable component of `dir` and register it with the durability daemon.
  Returns `[store dur-id]`."
  [dir kind]
  (case kind
    :records (let [rec (drs/open-record-store dir)]
               [rec (dur/register! {:fsync      (fn [{:keys [fsync?]}] (drs/fsync rec fsync?))
                                    :close      (fn [] (drs/close! rec))
                                    :compact    (fn [] (drs/compact! rec))
                                    :dead-ratio (fn [] (drs/dead-ratio rec))
                                    :label      (str "disk-records " dir)})])
    :index   (let [kvb (dkv/open-kv-backend dir)]
               [(kv/->KvIndexStore kvb)
                (dur/register! {:fsync      (fn [{:keys [fsync?]}] (dkv/fsync kvb fsync?))
                                :close      (fn [] (dkv/close! kvb))
                                :compact    (fn [] (dkv/compact! kvb))
                                :dead-ratio (fn [] (dkv/dead-ratio kvb))
                                :label      (str "disk-index " dir)})])
    ;; A fork's record-level bookkeeping (`vaelii.impl.overlay.store`): tombstones and
    ;; released premise marks, which are the overlay's own state and so must be exactly as
    ;; durable as its records.  Its own WAL in a subdirectory, so a directory holding a
    ;; fork is still an ordinary disk KB plus one extra log — and a directory that has
    ;; never been forked never grows one.
    :overlay-meta (let [kvb (dkv/open-kv-backend (str dir "/overlay-meta"))]
                    [kvb
                     (dur/register! {:fsync      (fn [{:keys [fsync?]}] (dkv/fsync kvb fsync?))
                                     :close      (fn [] (dkv/close! kvb))
                                     :compact    (fn [] (dkv/compact! kvb))
                                     :dead-ratio (fn [] (dkv/dead-ratio kvb))
                                     :label      (str "overlay-meta " dir)})])))

(defn- store-for
  "The `kind` (`:records` / `:index`) store for `dir`, opened once per canonical
  directory.  The directory's single-writer lock is taken by whichever component opens
  first and released once, by `close-dir!`.

  Opening is serialized on the registry rather than done inside a `swap!`: a retried
  `swap!` would open a second set of file handles for the same logs and leak the first."
  [dir kind]
  (let [cdir (canonical-dir dir)]
    (or (get-in @stores [cdir kind])
        (locking stores
          (or (get-in @stores [cdir kind])
              ;; "first" is *does this JVM already hold the lock*, not *is the registry
              ;; entry empty*.  A directory's entry can exist without a store behind it —
              ;; `register-index-snapshot!` makes one — and reading the entry instead
              ;; would leave such a directory unlocked, with nothing to say so.
              (let [first? (not (lock/held? cdir))]
                (when first? (lock/acquire! cdir))
                (try
                  (let [[store dur-id] (open-component! cdir kind)]
                    (swap! stores update cdir
                           #(-> (or % {:dir cdir :dur-ids {}})
                                (assoc kind store)
                                (assoc-in [:dur-ids kind] dur-id)))
                    store)
                  (catch Throwable t
                    ;; the lock this call took is nobody else's, and nothing is
                    ;; registered to release it later — drop it rather than hold the
                    ;; directory for the JVM's life over a failed open
                    (when first? (lock/release! cdir))
                    (throw t)))))))))

(defn records-for
  "The durable `RecordStore` for `dir`.  Opens no index — the record half alone is what
  a RAM-index mode (`:disk-memory`, `:disk-dense`, `:disk-columnar`) wants durable."
  [dir]
  (store-for dir :records))

(defn index-for
  "The durable `IndexStore` for `dir` — the `KvIndexStore` over a write-ahead-logged
  `DiskKvBackend`."
  [dir]
  (store-for dir :index))

(defn overlay-meta-for
  "The durable `KvBackend` holding a fork's record-level bookkeeping for `dir`
  (`vaelii.impl.overlay.mount`).  Opened only for a directory that actually hosts a
  fork's overlay."
  [dir]
  (store-for dir :overlay-meta))

(defn register-index-snapshot!
  "Register `save-fn` (a thunk) as `dir`'s derived-index snapshot writer.

  A derived index is not one of the components above — nothing here opens it, and it has
  no file handle to close — but the *image* of it is written to this directory and has to
  be written by whoever last held it, while the records it is stamped against are still
  open.  So it hangs off the directory's registry entry and runs at the front of
  `close-dir!`, and on JVM shutdown through the durability daemon.

  Idempotent per directory: `open-kb` runs for every KB constructed over a directory and
  they all share one index, so the first registration is the one that stands."
  [dir save-fn]
  (let [cdir (canonical-dir dir)]
    (locking stores
      (when-not (get-in @stores [cdir :snapshot])
        (let [id (dur/register! {:fsync (fn [_] nil)      ; an image is not a WAL — no tick
                                 :close save-fn
                                 :label (str "index-snapshot " cdir)})]
          (swap! stores update cdir
                 #(-> (or % {:dir cdir :dur-ids {}})
                      (assoc :snapshot save-fn)
                      (assoc-in [:dur-ids :snapshot] id))))))))

(def ^:private components [:records :index :overlay-meta])

(defn- close-component!
  "Attempt one component close, returning nil on success or the Throwable it threw.
  A component close fsyncs and can compact, so it can fail (a full disk), and a
  failure must not stop `close-dir!`: every component still gets its close attempt,
  and the lock release + registry removal run regardless.  The failure is logged here
  with its component named, and the first one is rethrown once the directory is
  genuinely released."
  [label thunk]
  (try (thunk) nil
       (catch Throwable t
         (trove/log! {:level :error
                      :msg (str "disk backend: close of " label " failed: "
                                (.getMessage t))})
         t)))

(defn opened
  "What is currently open for `dir`: the subset of `#{:records :index :overlay-meta}` this
  JVM holds stores for.  Empty when the directory has never been opened (or has been
  closed)."
  [dir]
  (let [e (@stores (canonical-dir dir))]
    (set (filter #(some? (get e %)) components))))

(defn close-dir!
  "Close and forget the stores for `dir`: fsync + close whichever components are open,
  deregister them from the durability daemon, and release the lock.  For explicit
  shutdown and test teardown — ordinary operation leaves the stores open for the JVM's
  life (the shutdown hook closes them).

  This is what `vaelii.core/close!` exists for — handing the directory to another
  process without exiting the JVM — so an unclean close must not defeat it: every
  component gets its close attempt, the lock release and the registry removal run even
  when one throws, and the first component failure is rethrown *after* that cleanup.
  The caller learns the close did not complete cleanly, and the directory is still
  released either way."
  [dir]
  (let [cdir (canonical-dir dir)]
    (locking stores
      (when-let [{:keys [records index overlay-meta snapshot dur-ids]} (@stores cdir)]
        ;; the image first: it is stamped against the records, so it has to be written
        ;; while they are still open, and a failure to write one must not stop the close
        (when snapshot
          (try (snapshot)
               (catch Throwable t
                 (trove/log! {:level :warn
                              :msg (str "disk backend: the index snapshot for " cdir
                                        " was not written (" (.getMessage t)
                                        ") — the next open rebuilds from the records")}))))
        (doseq [id (vals dur-ids)] (dur/deregister! id))
        (let [failures (into []
                             (keep identity)
                             [(when records
                                (close-component! (str "disk-records " cdir)
                                                  #(drs/close! records)))
                              (when index
                                (close-component! (str "disk-index " cdir)
                                                  #(dkv/close! (:backend index))))
                              (when overlay-meta
                                (close-component! (str "overlay-meta " cdir)
                                                  #(dkv/close! overlay-meta)))])]
          (lock/release! cdir)
          (swap! stores dissoc cdir)
          (when-first [t failures] (throw t)))))))

(defn disk-dir
  "The directory a disk KB lives in.  `:dir` names it explicitly; otherwise it derives
  from the space numbers under a base (`vaelii.disk.dir`, else `<tmpdir>/vaelii-disk`), so
  the record/index space pair the other backends key on still names a distinct store."
  [{:keys [dir record-space index-space] :or {record-space 0 index-space 1}}]
  (or dir
      (let [base (or (System/getProperty "vaelii.disk.dir")
                     (str (System/getProperty "java.io.tmpdir") "/vaelii-disk"))]
        (str base "/space-" record-space "-" index-space))))

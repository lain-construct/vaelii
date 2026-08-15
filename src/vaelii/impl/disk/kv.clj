;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.disk.kv
  "The index store on disk — a `KvBackend` (`vaelii.impl.kv`) over a durable
  write-ahead log.

  The index is derived state (small next to the records, and `reindex` can rebuild it
  from the records alone), so the disk KV keeps the whole key→value map in RAM — a `Long` at
  each counter key, a set at each set key, exactly the shape `MemoryKvBackend` holds —
  and durably logs every mutation to a `kv.log` of length-prefixed nippy frames.  Reads
  are the in-RAM map, so `kv-members` / `kv-intersect` are the same reference /
  `set-intersection` operations the memory backend does — the disk only buys durability.

  **Logical (op) logging.**  A frame is the write op itself — `[:add-to-set k m]`, `[:remove-from-set k
  m]`, `[:put k v]`, `[:delete k]`, `[:increment k]`, `[:decrement k]` — not the resulting value.  A
  set-add logs the one added member, O(1), so a bulk load of N members into one root
  writes O(N) WAL bytes; new-value logging re-serialized the size-i set on the i-th add
  and cost O(N²).  On open the log replays by folding each frame through `kv/apply-op`, the
  same function that applies a live op.  `compact!` rewrites the log as one `[:put k v]`
  op per live key, so every frame — ordinary or post-compaction — is a uniform op and
  the reader needs no snapshot-vs-delta discrimination; it also bounds replay length and
  reclaims the delta frames (compaction is this store's snapshot cadence).

  Crash-safety: `scan-log` truncates a torn tail on open (a partial op frame is dropped
  whole, never half-applied), and compaction rewrites the log crash-safely
  (`files/recover-log-compaction!`).  All log writes hold the backend lock (the RAF file
  pointer is shared)."
  (:require [clojure.set :as set]
            [taoensso.trove :as trove]
            [vaelii.impl.disk.durability :as dur]
            [vaelii.impl.disk.files :as f]
            [vaelii.impl.kv :as kv]))

(defn- apply-ops!
  "Apply write ops: fold them into the RAM map, append one frame **per op** to the WAL,
  publish the new map, and return the per-op replies.  Logical (op) logging, not
  new-value logging: a `:add-to-set` frame carries the one added member, O(1), never the
  grown set — so a bulk load of N members into one root writes O(N) WAL bytes, not
  O(N²).

  **The whole read-compute-publish is under the lock.**  Single-writer covers the other
  *writers*, and it is not what this lock is for: `compact!` snapshots `@data` inside the
  lock and then rewrites the log to match, and it runs on the durability daemon's
  compaction executor — a thread the single-writer contract says nothing about.  Reading
  `@data` before acquiring and publishing after releasing left two windows on that
  thread.  A compaction landing in either one writes the log from a map that is missing
  this write (so the WAL holds the frame and the rewritten log does not, and the next
  open replays an index the running one disagrees with), or, after `kv-clear!`, restores
  the whole pre-clear map over a log that was just truncated.  The clear case is the one
  that bites: `reindex` is clear-plus-rebuild, and a large reindex is exactly when a
  compaction is queued."
  [{:keys [data log lock frames]} ops]
  (locking lock
    (let [[m1 replies]
          (reduce (fn [[m rs] op]
                    (let [[m' r] (kv/apply-op m op)]
                      [m' (conj rs r)]))
                  [@data []] ops)]
      (doseq [op ops] (f/append-record! log op))
      (vswap! frames + (count ops))
      (reset! data m1)
      replies)))

;; `closed` (a volatile boolean, written and read under `lock`) is `compact!`'s guard:
;; the durability daemon's queued-task check runs outside this store's lock, so a close
;; can land between that check and `compact!` acquiring the lock — see `compact!`.
(defrecord DiskKvBackend [dir data log log-path lock frames closed damaged]
  kv/KvBackend
  (kv-get  [_ k]   (get @data k))
  (kv-put  [b k v] (apply-ops! b [[:put k v]]) nil)
  (kv-delete  [b k]   (apply-ops! b [[:delete k]]) nil)
  (kv-increment [b k]   (first (apply-ops! b [[:increment k]])))
  (kv-decrement [b k]   (first (apply-ops! b [[:decrement k]])))
  (kv-add-to-set [b k m] (apply-ops! b [[:add-to-set k m]]) nil)
  (kv-remove-from-set [b k m] (apply-ops! b [[:remove-from-set k m]]) nil)
  (kv-members [_ k] (get @data k #{}))
  ;; a read is the in-RAM map, so membership is the hash lookup the memory backend does —
  ;; the log buys durability, never a different read cost
  (kv-member? [_ k m] (contains? (get @data k) m))
  (kv-count    [_ k] (count (get @data k)))
  (kv-intersect [_ ks]
    (if (empty? ks)
      #{}
      (let [m @data] (apply set/intersection (map #(get m % #{}) ks)))))
  (kv-batch [b ops] (apply-ops! b ops))

  ;; the RAM map is already the portable shape; the install goes through the ordinary
  ;; op path so every entry is durably logged, batched so a replay is not one fsync-able
  ;; write per entry.
  (kv-entries [_] (seq @data))
  (kv-load [b entries]
    (doseq [batch (partition-all 10000 entries)]
      (apply-ops! b (mapv (fn [[k v]] [:put k v]) batch)))
    nil)

  ;; the publish is inside the lock for `apply-ops!`'s reason, and more sharply here: a
  ;; compaction between the truncate and the publish snapshots the *pre-clear* map and
  ;; writes every entry of it back over the log this just emptied
  (kv-clear! [_]
    (locking lock
      (f/truncate! log)
      (vreset! frames 0)
      (reset! data {}))
    nil))

(defn open-kv-backend
  "Open a `DiskKvBackend` rooted at `dir/index`, replaying `kv.log` into the RAM map
  (recovering any interrupted compaction and truncating a torn tail first)."
  [dir]
  (let [root     (str dir "/index")
        _        (f/ensure-dir! root)
        _        (f/assert-format! root)
        log-path (str root "/kv.log")]
    (f/recover-log-compaction! log-path)
    ;; read before anything is written, and drop it: the marker describes a store nobody
    ;; holds, so it cannot survive into a session that appends
    (let [clean (f/read-clean-marker root)
          _     (f/remove-clean-marker! root)
          log   (f/open-log log-path)
          ;; The marker records the length the WAL *closed* at, so a file that is any
          ;; other length now was not closed as this log: a tail lost to a short
          ;; restore or a partial copy, most likely of a compacted log — one flat
          ;; `[:put]` per key in hash order, where the lost keys are arbitrary and the
          ;; batch-seal counter may well be among the survivors.  The tail walk below
          ;; still finds a clean frame boundary and replays what remains; the flag is
          ;; how the open gate knows that what remains is not everything.
          damaged? (let [expected (get clean "kv")]
                     (and (integer? expected)
                          (not= (long expected) (f/log-length log))))]
      ;; The replay owns the handle until it hands it to the record it returns.  A frame
      ;; `kv/apply-op` does not recognize, or an `:increment` over a key holding a set,
      ;; throws out of `scan-log` — and the caller (`backend/store-for`) answers a failed
      ;; open by releasing the *directory lock*, so leaking this would give the lock back
      ;; while this JVM still held an open handle on `kv.log`, the one state `close-dir!`
      ;; is written to prevent.  `open-record-store` guards its opens the same way.
      (try
        (f/truncate-log! log (first (f/log-tail-offset-from log (get clean "kv"))))
        (let [m      (volatile! {})
              frames (volatile! 0)]
          (f/scan-log log (fn [_ op]
                            (vswap! frames inc)
                            (vswap! m (fn [mm] (first (kv/apply-op mm op))))))
          (->DiskKvBackend root (atom @m) log log-path (Object.) frames (volatile! false)
                           damaged?))
        (catch Throwable t
          (try (f/close! log) (catch Throwable _ nil))
          (throw t))))))

(defn fsync
  "fsync the WAL.  `fsync?` false drains to the page cache without the fsync."
  [{:keys [log lock]} fsync?]
  (when fsync? (locking lock (f/force! log false))))

(defn dead-ratio
  "The delta-accumulation ratio: `1 - live-keys / frames-written`, the fraction of the
  WAL that a compaction would collapse.  Under logical logging each op is one frame, so
  a key touched K times since the last snapshot carries K-1 frames a `[:put k v]`
  snapshot would fold away; `frames` drops to the live-key count on `compact!`, so this
  reads 0 immediately after and climbs as deltas accumulate against the live footprint."
  ^double [{:keys [data frames]}]
  (let [fr (long @frames)]
    (if (pos? fr) (max 0.0 (- 1.0 (/ (double (count @data)) (double fr)))) 0.0)))

(defn compact!
  "Crash-safely rewrite the WAL as one `[:put k v]` op frame per live key — the
  snapshot that collapses every accumulated delta chain.  Every frame in the log,
  post-compaction or ordinary, is thus a uniform op replayed by the same `kv/apply-op`
  fold, so the reader needs no snapshot-vs-delta discrimination.  Holds the lock, so
  writers wait; the RAM map is untouched, so reads never block.

  A closed store is skipped, and the flag is consulted **after the lock is acquired**:
  the durability daemon's queued-task guard reads its registry outside this lock, so a
  `close!` can land between that check and this lock — and compacting a closed log
  fails *late*, the temp and its commit marker already on disk with the delete that
  clears them never reached, which the next open would replay as a crash-interrupted
  compaction.  Under the lock there is no window: `close!` sets the flag holding the
  same lock, so a compaction that acquires it either runs against a store that stays
  open until it finishes, or sees the flag and writes nothing."
  [{:keys [data log log-path lock frames closed]}]
  (locking lock
    (if @closed
      (trove/log! {:level :debug
                   :msg (str "disk kv: compact! of " log-path
                             " skipped — the store is closed")})
      (let [{:keys [tmp marker]} (f/log-compact-paths log-path)
            snapshot @data
            tlog     (f/open-log tmp)]
        ;; A failure **before the marker** takes the temp with it: the original stays
        ;; authoritative, and `f/open-log` seeks to `.length`, so a temp left behind is
        ;; one the next compaction in this session opens and appends to — the replay
        ;; would then put back keys deleted in between.  A failure **after** it must
        ;; leave both alone: the marker is the commit point, `replay-temp-onto-raf!`
        ;; truncates the live log before copying, and deleting the temp there would
        ;; destroy the only complete copy.  The next open finds the marker and finishes
        ;; the replay, which is what the marker is for.
        (let [committed? (volatile! false)]
          (try
            (doseq [[k v] snapshot] (f/append-record! tlog [:put k v]))
            (f/force! tlog false)
            (f/close! tlog)
            (f/write-commit-marker! marker {:log log-path})
            (vreset! committed? true)
            (f/replay-temp-onto-raf! log tmp)
            (f/delete-log-compact-temps! marker tmp)
            (vreset! frames (count snapshot))
            (catch Throwable t
              (f/close! tlog)
              (when-not @committed? (f/delete-log-compact-temps! marker tmp))
              (throw t))))))))

(defn close!
  "Compact if the deltas have earned it, flush durably, record the length the WAL closed
  at, and close it.  The next open skips the torn-tail walk while that length still
  agrees.

  **Why compact here.** Opening this store is a replay: every frame is thawed and folded
  through `kv/apply-op`, so the open costs the *frame count*, not the live-key count. A
  bulk load leaves those far apart — 5.81M frames against 2.01M live keys on a 300k-fact
  KB, a 0.65 dead ratio — and a compaction collapses each key's delta chain to the one
  `[:put k v]` a replay actually needs. Closing is the moment to pay for it: the writer
  is done, and the cost lands once instead of on every subsequent open.

  Gated on the *same* switch and threshold the background tick uses
  (`vaelii.impl.disk.durability`), so a store closed just after a compaction does not
  rewrite its log for nothing, and one knob turns both off.

  **The WAL is released and the flag is set whatever the compaction or the flush did.**
  Both can fail — a full disk — and `backend/close-dir!` releases the directory's OS
  lock on a failed close as deliberately as on a clean one; a store left with `closed`
  false and its RAF still open is then one a queued auto-compaction will still try to
  rewrite, over a directory another process may already hold."
  [{:keys [dir log lock closed] :as b}]
  (try
    (when (and (dur/auto-compact?) (>= (dead-ratio b) (dur/compact-dead-ratio)))
      (compact! b))
    (fsync b true)
    (f/write-clean-marker! dir {"kv" (locking lock (f/log-length log))})
    (finally
      (locking lock
        ;; under the same lock `compact!` consults it, so no compaction can start against
        ;; the closed log
        (vreset! closed true)
        (f/close! log)))))

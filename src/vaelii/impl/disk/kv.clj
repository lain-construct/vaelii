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
  and cost O(N²).  On open the log replays by folding each frame through `apply-op`, the
  same function that applies a live op.  `compact!` rewrites the log as one `[:put k v]`
  op per live key, so every frame — ordinary or post-compaction — is a uniform op and
  the reader needs no snapshot-vs-delta discrimination; it also bounds replay length and
  reclaims the delta frames (compaction is this store's snapshot cadence).

  Crash-safety: `scan-log` truncates a torn tail on open (a partial op frame is dropped
  whole, never half-applied), and compaction rewrites the log crash-safely
  (`files/recover-log-compaction!`).  All log writes hold the backend lock (the RAF file
  pointer is shared)."
  (:require [clojure.set :as set]
            [vaelii.impl.disk.durability :as dur]
            [vaelii.impl.disk.files :as f]
            [vaelii.impl.kv :as kv]))

(defn- apply-op
  "Apply one write op to map `m`, returning `[m' reply]`.  Only :increment/:decrement carry a
  reply (the post-op counter value); the rest reply nil.  The op is also the WAL frame
  (logical logging), and replay folds the log through this same function."
  [m [op k a]]
  (case op
    :put  [(assoc m k a) nil]
    :delete  [(dissoc m k) nil]
    :increment (let [v (inc (long (get m k 0)))] [(assoc m k v) v])
    :decrement (let [v (dec (long (get m k 0)))] [(assoc m k v) v])
    :add-to-set [(update m k (fnil conj #{}) a) nil]
    :remove-from-set (let [s (disj (get m k) a)]
                       [(if (empty? s) (dissoc m k) (assoc m k s)) nil])))

(defn- apply-ops!
  "Apply write ops: fold them into the RAM map, append one frame **per op** to the WAL,
  publish the new map, and return the per-op replies.  Logical (op) logging, not
  new-value logging: a `:add-to-set` frame carries the one added member, O(1), never the
  grown set — so a bulk load of N members into one root writes O(N) WAL bytes, not
  O(N²).  Single-writer, so the read-compute-publish is race-free."
  [{:keys [data log lock frames]} ops]
  (let [[m1 replies]
        (reduce (fn [[m rs] op]
                  (let [[m' r] (apply-op m op)]
                    [m' (conj rs r)]))
                [@data []] ops)]
    (locking lock
      (doseq [op ops] (f/append-record! log op))
      (vswap! frames + (count ops)))
    (reset! data m1)
    replies))

(defrecord DiskKvBackend [dir data log log-path lock frames]
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

  (kv-clear! [_]
    (locking lock (f/truncate! log) (vreset! frames 0))
    (reset! data {})
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
          log   (f/open-log log-path)]
      (f/truncate-log! log (first (f/log-tail-offset-from log (get clean "kv"))))
      (let [m      (volatile! {})
            frames (volatile! 0)]
        (f/scan-log log (fn [_ op]
                          (vswap! frames inc)
                          (vswap! m (fn [mm] (first (apply-op mm op))))))
        (->DiskKvBackend root (atom @m) log log-path (Object.) frames)))))

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
  post-compaction or ordinary, is thus a uniform op replayed by the same `apply-op`
  fold, so the reader needs no snapshot-vs-delta discrimination.  Holds the lock, so
  writers wait; the RAM map is untouched, so reads never block."
  [{:keys [data log log-path lock frames]}]
  (locking lock
    (let [{:keys [tmp marker]} (f/log-compact-paths log-path)
          snapshot @data
          tlog     (f/open-log tmp)]
      (doseq [[k v] snapshot] (f/append-record! tlog [:put k v]))
      (f/force! tlog false)
      (f/close! tlog)
      (f/write-commit-marker! marker {:log log-path})
      (f/replay-temp-onto-raf! log tmp)
      (f/delete-log-compact-temps! marker tmp)
      (vreset! frames (count snapshot)))))

(defn close!
  "Compact if the deltas have earned it, flush durably, record the length the WAL closed
  at, and close it.  The next open skips the torn-tail walk while that length still
  agrees.

  **Why compact here.** Opening this store is a replay: every frame is thawed and folded
  through `apply-op`, so the open costs the *frame count*, not the live-key count. A
  bulk load leaves those far apart — 5.81M frames against 2.01M live keys on a 300k-fact
  KB, a 0.65 dead ratio — and a compaction collapses each key's delta chain to the one
  `[:put k v]` a replay actually needs. Closing is the moment to pay for it: the writer
  is done, and the cost lands once instead of on every subsequent open.

  Gated on the *same* switch and threshold the background tick uses
  (`vaelii.impl.disk.durability`), so a store closed just after a compaction does not
  rewrite its log for nothing, and one knob turns both off."
  [{:keys [dir log lock] :as b}]
  (when (and (dur/auto-compact?) (>= (dead-ratio b) (dur/compact-dead-ratio)))
    (compact! b))
  (fsync b true)
  (f/write-clean-marker! dir {"kv" (locking lock (f/log-length log))})
  (locking lock (f/close! log)))

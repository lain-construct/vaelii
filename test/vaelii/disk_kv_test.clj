(ns vaelii.disk-kv-test
  "The on-disk `KvBackend` adapter (`vaelii.impl.disk.kv`): a durable write-ahead log
  over an in-RAM key→value map.  Exercised directly for a close→reopen persistence
  round-trip, WAL compaction, and torn-tail crash recovery.  The full `KvBackend`
  contract is covered by `kv-backend-test`'s suite-backend arm under
  `VAELII_TEST_BACKEND=disk`; here the concern is durability."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.impl.disk.files :as f]
            [vaelii.impl.disk.kv :as dkv]
            [vaelii.impl.kv :as kv])
  (:import [java.io RandomAccessFile]
           [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]))

(defn- tmpdir ^String []
  (str (Files/createTempDirectory "vaelii-dkv-" (into-array FileAttribute []))))

(defn- rm-rf! [^String dir]
  (doseq [f (reverse (file-seq (java.io.File. dir)))] (.delete ^java.io.File f)))

(defn- with-tmp [f]
  (let [dir (tmpdir)]
    (try (f dir) (finally (rm-rf! dir)))))

(deftest persistence-round-trip
  (with-tmp
    (fn [dir]
      (let [b (dkv/open-kv-backend dir)]
        (kv/kv-increment b [:c :n]) (kv/kv-increment b [:c :n])   ; counter -> 2
        (kv/kv-add-to-set b [:s 1] 1970) (kv/kv-add-to-set b [:s 1] :rule) (kv/kv-add-to-set b [:s 1] 'foo)
        (kv/kv-put b [:v :a] {:x 1})
        (dkv/close! b))
      (testing "a reopen replays the WAL into an identical map"
        (let [b (dkv/open-kv-backend dir)]
          (is (= 2 (kv/kv-get b [:c :n])) "the counter replays to its last value")
          (is (= #{1970 :rule 'foo} (kv/kv-members b [:s 1])) "set + member types survive")
          (is (= 3 (kv/kv-count b [:s 1])))
          (is (= {:x 1} (kv/kv-get b [:v :a])))
          (dkv/close! b))))))

(deftest srem-tombstones-replay-as-absent
  (with-tmp
    (fn [dir]
      (let [b (dkv/open-kv-backend dir)]
        (kv/kv-add-to-set b [:s 1] 'a) (kv/kv-add-to-set b [:s 1] 'b)
        (kv/kv-remove-from-set b [:s 1] 'a) (kv/kv-remove-from-set b [:s 1] 'b)   ; empties -> key removed
        (kv/kv-put b [:s 2] :keep)
        (kv/kv-delete b [:s 2])                                 ; explicit delete
        (dkv/close! b))
      (let [b (dkv/open-kv-backend dir)]
        (is (= #{} (kv/kv-members b [:s 1])) "an emptied set replays as absent")
        (is (nil? (kv/kv-get b [:s 2])) "a deleted key replays as absent")
        (dkv/close! b)))))

(deftest compaction-collapses-overwrites-preserving-state
  (with-tmp
    (fn [dir]
      (let [b (dkv/open-kv-backend dir)]
        (try
          (dotimes [_ 200] (kv/kv-increment b [:c :n]))          ; 200 frames, one live key
          (dotimes [i 50] (kv/kv-add-to-set b [:s 1] i))          ; 50 frames, one live key
          (is (> (dkv/dead-ratio b) 0.9) "heavy overwrite left a mostly-dead WAL")
          (let [n     (kv/kv-get b [:c :n])
                s     (kv/kv-members b [:s 1])]
            (dkv/compact! b)
            (is (< (dkv/dead-ratio b) 1.0e-9) "compaction collapsed to one frame per key")
            (testing "the map is untouched by compaction"
              (is (= n (kv/kv-get b [:c :n])))
              (is (= s (kv/kv-members b [:s 1])))))
          (finally (dkv/close! b))))
      (testing "the compacted WAL still replays to the same state"
        (let [b (dkv/open-kv-backend dir)]
          (is (= 200 (kv/kv-get b [:c :n])))
          (is (= (set (range 50)) (kv/kv-members b [:s 1])))
          (dkv/close! b))))))

(deftest batch-and-clear-persist-and-replay
  (with-tmp
    (fn [dir]
      (let [b (dkv/open-kv-backend dir)]
        (let [replies (kv/kv-batch b [[:increment [:n]] [:increment [:n]] [:add-to-set [:s] 'x]
                                      [:decrement [:n]] [:put [:v] :hi] [:remove-from-set [:s] 'x]])]
          (is (= [1 2 nil 1 nil nil] replies) "incr/decr replies align positionally"))
        (dkv/close! b))
      (testing "the whole batch replays from the WAL"
        (let [b (dkv/open-kv-backend dir)]
          (is (= 1 (kv/kv-get b [:n])))
          (is (= :hi (kv/kv-get b [:v])))
          (is (zero? (kv/kv-count b [:s])) "the sadd/srem cancelled to empty")
          (testing "kv-clear! wipes everything, and the wipe survives a reopen"
            (kv/kv-clear! b)
            (dkv/close! b)
            (let [b2 (dkv/open-kv-backend dir)]
              (is (nil? (kv/kv-get b2 [:n])))
              (is (nil? (kv/kv-get b2 [:v])))
              (dkv/close! b2))))))))

(deftest set-overwrite-and-negative-counter-round-trip
  (with-tmp
    (fn [dir]
      (let [b (dkv/open-kv-backend dir)]
        (kv/kv-add-to-set b [:k] 'a) (kv/kv-add-to-set b [:k] 'b)
        (kv/kv-put b [:k] #{'x 'y 'z})              ; overwrite the whole set at the key
        (dotimes [_ 5] (kv/kv-decrement b [:c]))         ; a counter driven negative
        (dkv/close! b))
      (let [b (dkv/open-kv-backend dir)]
        (is (= #{'x 'y 'z} (kv/kv-members b [:k])) "kv-put overwrote, not merged")
        (is (= -5 (kv/kv-get b [:c])) "a negative counter round-trips")
        (dkv/close! b)))))

(deftest compact-then-write-then-reopen-is-consistent
  (with-tmp
    (fn [dir]
      (let [b (dkv/open-kv-backend dir)]
        (dotimes [i 30] (kv/kv-add-to-set b [:big] i))
        (dotimes [_ 30] (kv/kv-increment b [:c]))
        (dkv/compact! b)                            ; collapse the churn
        (kv/kv-add-to-set b [:big] 999)                   ; then write more onto the compacted WAL
        (kv/kv-increment b [:c])
        (dkv/close! b))
      (testing "writes after a compaction replay correctly on reopen"
        (let [b (dkv/open-kv-backend dir)]
          (is (= (conj (set (range 30)) 999) (kv/kv-members b [:big])))
          (is (= 31 (kv/kv-get b [:c])))
          (is (= (kv/kv-members b [:big]) (kv/kv-intersect b [[:big]])) "sinter agrees after reopen")
          (dkv/close! b))))))

(deftest torn-wal-tail-recovers-on-reopen
  (with-tmp
    (fn [dir]
      (let [b (dkv/open-kv-backend dir)]
        (kv/kv-put b [:v :a] :one)
        (kv/kv-put b [:v :b] :two)
        (dkv/close! b))
      (let [log (str dir "/index/kv.log")]
        (with-open [raf (RandomAccessFile. log "rw")]
          (.seek raf (.length raf))
          (.writeInt raf 999999)                 ; a frame prefix promising bytes never written
          (.write raf (byte-array 8))))
      (testing "reopen truncates the torn tail and keeps the durable entries"
        (let [b (dkv/open-kv-backend dir)]
          (is (= :one (kv/kv-get b [:v :a])))
          (is (= :two (kv/kv-get b [:v :b])))
          (dkv/close! b))))))

(deftest a-clean-close-compacts-so-the-next-open-replays-live-keys-only
  ;; Opening this store is a replay, so it costs the *frame* count — and a load leaves
  ;; frames far above live keys.  Closing is when to collapse that, once, rather than
  ;; paying it back on every open.  (Measured on a 300k-fact KB: 5.81M frames against
  ;; 2.01M live keys, and the open went 19.3s → 6.5s.)
  (with-tmp
    (fn [dir]
      (let [b (dkv/open-kv-backend dir)]
        (dotimes [i 12] (kv/kv-put b [:v :k] i))          ; 12 frames, 1 live key
        (kv/kv-put b [:v :other] :x)
        (is (> (dkv/dead-ratio b) 0.5) "the fixture did not accumulate deltas")
        (dkv/close! b))
      (let [b (dkv/open-kv-backend dir)]
        (testing "the state is exactly what it was"
          (is (= 11 (kv/kv-get b [:v :k])))
          (is (= :x (kv/kv-get b [:v :other]))))
        (testing "and the replay is now one frame per live key"
          (is (= (count @(:data b)) @(:frames b)))
          (is (zero? (dkv/dead-ratio b))))
        (dkv/close! b)))))

(deftest a-clean-close-that-has-nothing-to-collapse-leaves-the-log-alone
  (with-tmp
    (fn [dir]
      (let [b (dkv/open-kv-backend dir)]
        (dotimes [i 8] (kv/kv-put b [:v i] i))            ; 8 frames, 8 live keys
        (is (zero? (dkv/dead-ratio b)))
        (dkv/close! b))
      (let [before (.length (java.io.File. (str dir "/index/kv.log")))
            b      (dkv/open-kv-backend dir)]
        (dkv/close! b)
        (is (= before (.length (java.io.File. (str dir "/index/kv.log"))))
            "a close with a clean log rewrote it for nothing")))))

(deftest the-clean-marker-tracks-the-wal-and-never-outlives-a-session
  (with-tmp
    (fn [dir]
      (let [root (str dir "/index")
            b    (dkv/open-kv-backend dir)]
        (kv/kv-put b [:v :a] 1)
        (is (nil? (f/read-clean-marker root)) "the marker must not exist while the store is open")
        (dkv/close! b)
        (is (= (.length (java.io.File. (str root "/kv.log"))) (get (f/read-clean-marker root) "kv"))
            "a clean close records the length it closed at"))
      ;; and a crash after that close invalidates it by length alone
      (with-open [raf (RandomAccessFile. (str dir "/index/kv.log") "rw")]
        (.seek raf (.length raf))
        (.writeInt raf 999999)
        (.write raf (byte-array 8)))
      (let [b (dkv/open-kv-backend dir)]
        (is (= 1 (kv/kv-get b [:v :a])) "the stale marker was believed over the bytes")
        (dkv/close! b)))))

(defn- log-bytes ^long [dir]
  (with-open [raf (RandomAccessFile. (str dir "/index/kv.log") "r")]
    (.length raf)))

(deftest write-amplification-is-linear-in-members
  ;; The contract for logical (op) logging: adding the i-th member to one set logs the
  ;; member alone, not the size-i set, so a bulk load of N members writes O(N) WAL bytes.
  ;; New-value logging re-serialized the grown set on every add — O(N²), bytes/member
  ;; growing ∝ N — and would fail this gate.
  (letfn [(load-bytes [n]
            (let [dir (tmpdir)]
              (try
                (let [b (dkv/open-kv-backend dir)]
                  (try (dotimes [i n] (kv/kv-add-to-set b [:functor-root 'p] i))
                       (log-bytes dir)
                       (finally (dkv/close! b))))
                (finally (rm-rf! dir)))))]
    (let [n     5000
          per-1 (/ (double (load-bytes n)) n)
          per-2 (/ (double (load-bytes (* 2 n))) (* 2 n))]
      (is (< (/ per-2 per-1) 1.3)
          (str "bytes/member should stay ~constant for a linear WAL; O(N²) would roughly "
               "double it. Got " (format "%.1f" per-1) " B/member at " n
               " vs " (format "%.1f" per-2) " at " (* 2 n))))))

(deftest mixed-ops-across-mid-run-compaction-replay-identically
  ;; Replay equivalence under op-logging: a mix of sadd/srem/incr/decr/set/del, with a
  ;; forced compaction in the middle, reconstructs the identical map on reopen.  The
  ;; ops after the compaction fold onto its `[:put k v]` snapshots.
  (with-tmp
    (fn [dir]
      (let [b     (dkv/open-kv-backend dir)
            live  (try
                    (kv/kv-add-to-set b [:s 1] 'a) (kv/kv-add-to-set b [:s 1] 'b) (kv/kv-add-to-set b [:s 1] 'c)
                    (kv/kv-increment b [:c]) (kv/kv-increment b [:c])
                    (kv/kv-put b [:v] {:k 1})
                    (dkv/compact! b)                       ; snapshot mid-run
                    (kv/kv-remove-from-set b [:s 1] 'b)               ; then keep mutating
                    (kv/kv-add-to-set b [:s 2] 'z)
                    (kv/kv-decrement b [:c])
                    (kv/kv-put b [:v] {:k 2})              ; overwrite a snapshotted key
                    (kv/kv-delete b [:s 2])                   ; delete a post-snapshot key
                    {[:s 1] (kv/kv-members b [:s 1])
                     [:s 2] (kv/kv-members b [:s 2])
                     [:c]   (kv/kv-get b [:c])
                     [:v]   (kv/kv-get b [:v])}
                    (finally (dkv/close! b)))]
        (testing "reopen reconstructs the live map across the mid-run compaction"
          (let [b (dkv/open-kv-backend dir)]
            (is (= (get live [:s 1]) (kv/kv-members b [:s 1])) "srem folded onto the snapshot")
            (is (= #{} (kv/kv-members b [:s 2])) "the post-snapshot add+del cancels")
            (is (= (get live [:c]) (kv/kv-get b [:c])) "incr×2 then decr → 1")
            (is (= {:k 2} (kv/kv-get b [:v])) "the post-snapshot overwrite wins")
            (is (= (get live [:v]) (kv/kv-get b [:v])))
            (dkv/close! b)))))))

(deftest partial-op-frame-at-tail-is-dropped-whole
  ;; A torn op frame at the tail (truthful length prefix, truncated payload) is dropped
  ;; entire on reopen — the op is never half-applied, so no set is left partially built.
  (with-tmp
    (fn [dir]
      (let [b (dkv/open-kv-backend dir)]
        (kv/kv-add-to-set b [:s 1] 'a) (kv/kv-add-to-set b [:s 1] 'b)
        (dkv/close! b))
      (let [log (str dir "/index/kv.log")]
        (with-open [raf (RandomAccessFile. log "rw")]
          (.seek raf (.length raf))
          (.writeInt raf 64)                     ; promises 64 payload bytes
          (.write raf (byte-array 10))))         ; only 10 present -> a torn op frame
      (testing "reopen recovers to the last complete op; the torn op is not applied"
        (let [b (dkv/open-kv-backend dir)]
          (is (= #{'a 'b} (kv/kv-members b [:s 1])) "both complete sadd ops survive, no partial")
          (dkv/close! b))))))

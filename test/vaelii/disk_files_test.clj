;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.disk-files-test
  "The disk substrate (`vaelii.impl.disk.files`) tested directly — the frame/slot
  primitives, torn-tail recovery, and the crash-safe compaction recovery branches the
  full-suite gate never reaches because it never crashes mid-operation."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.impl.disk.files :as f])
  (:import [java.io File]
           [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]))

(defn- tmpdir ^String []
  (str (Files/createTempDirectory "vaelii-files-" (into-array FileAttribute []))))

(defn- rm-rf! [^String dir]
  (doseq [f (reverse (file-seq (File. dir)))] (.delete ^File f)))

(defn- with-tmp [f]
  (let [dir (tmpdir)]
    (try (f dir) (finally (rm-rf! dir)))))

(defn- exists? [^String path] (.exists (File. path)))

;; ---- frames -------------------------------------------------------------

(deftest frames-round-trip-every-token-type
  (with-tmp
    (fn [dir]
      (let [log (f/open-log (str dir "/t.log"))
            vals [{:a 1 :sym 'foo :kw :bar}
                  #{1 2 3}
                  '(nested (list -7) "string")
                  [1.5 -3 0 :k 'S nil]
                  "a bare string"]
            offs (mapv #(f/append-record! log %) vals)]
        (testing "each value thaws back identical from its offset"
          (doseq [[o v] (map vector offs vals)]
            (is (= v (f/read-record log o)))))
        (is (nil? (f/read-record log -1)) "a negative offset reads nil")
        (is (nil? (f/read-record log (f/log-length log))) "an at-EOF offset reads nil")
        ;; `read-record-sized` is the hot path: a caller holding the slot already knows
        ;; the payload length, so it reads the payload alone — one positional read, with
        ;; neither a seek nor a re-read of the length prefix.  It must agree with
        ;; `read-record` frame for frame, or every paged record is subtly wrong.
        (testing "read-record-sized agrees with read-record on every frame"
          (loop [os offs, vs vals]
            (when (seq os)
              (let [o    (first os)
                    ;; the payload length is the next frame's offset (or EOF) minus
                    ;; this frame's offset and its 4-byte prefix — what a slot records
                    next (or (second os) (f/log-length log))
                    len  (- next o 4)]
                (is (= (first vs) (f/read-record-sized log o len)))
                (recur (rest os) (rest vs))))))
        (testing "and refuses what it cannot read rather than guessing"
          (is (nil? (f/read-record-sized log -1 10)) "a negative offset")
          (is (nil? (f/read-record-sized log 0 0))   "a zero length — no real frame is empty")
          (is (nil? (f/read-record-sized log (f/log-length log) 8)) "a payload past EOF"))
        (f/close! log)))))

;; ---- slots --------------------------------------------------------------

(deftest slots-read-write-tombstone-and-gaps
  (with-tmp
    (fn [dir]
      (let [idx (f/open-idx (str dir "/t.idx"))]
        (f/write-slot! idx 0 100 20 0 0)
        (f/write-slot! idx 5 200 30 0 0)          ; leaves 1..4 as a zero-filled gap
        (testing "written slots read back; gap slots read as nil"
          (is (= 100 (:offset (f/read-slot idx 0))))
          (is (= 30 (:length (f/read-slot idx 5))))
          (is (nil? (f/read-slot idx 2)) "a zero-filled gap reads as unwritten")
          (is (nil? (f/read-slot idx 99)) "past EOF reads as unwritten"))
        (testing "max-slot-id / slot-count reflect the high-water mark"
          (is (= 5 (f/max-slot-id idx)))
          (is (= 6 (f/slot-count idx))))
        (testing "a tombstone keeps its slot (so max-slot-id, hence next-id, is stable)"
          (f/tombstone-slot! idx 5)
          (is (:tombstone? (f/read-slot idx 5)))
          (is (= 5 (f/max-slot-id idx)) "tombstoning does not lower the high-water mark"))
        (f/close! idx)))))

(deftest scan-idx-yields-only-live-slots
  (with-tmp
    (fn [dir]
      (let [idx (f/open-idx (str dir "/t.idx"))]
        (f/write-slot! idx 0 10 5 0 0)
        (f/write-slot! idx 3 20 5 0 0)
        (f/write-slot! idx 7 30 5 (f/premise-flags true) 0)
        (f/tombstone-slot! idx 3)                 ; live: 0,7 ; gaps 1,2,4,5,6 ; tombstone 3
        (let [seen (atom [])]
          (f/scan-idx! idx (fn [id _ _ flags] (swap! seen conj [id flags])))
          (is (= #{0 7} (set (map first @seen))) "only live slots, no tombstones or gaps")
          (testing "the scan carries each slot's flags, so an open reads them once"
            (is (= {0 nil, 7 true} (into {} (map (fn [[id fl]] [id (f/slot-premise fl)]))
                                         @seen))
                "an unannotated slot says nothing; an annotated one says what it says")))
        (f/close! idx)))))

(deftest premise-flags-round-trip-through-a-slot
  (testing "the two bits: a slot says premise, says not-premise, or does not say"
    (is (= true  (f/slot-premise (f/premise-flags true))))
    (is (= false (f/slot-premise (f/premise-flags false))))
    (is (nil? (f/slot-premise 0))
        "0 — what every slot written before the bit existed holds — is unknown, not false"))
  (with-tmp
    (fn [dir]
      (let [idx (f/open-idx (str dir "/t.idx"))]
        (f/write-slot! idx 1 10 5 (f/premise-flags true) 0)
        (f/write-slot! idx 2 20 5 (f/premise-flags false) 0)
        (f/write-slot! idx 3 30 5 0 0)
        (is (= [true false nil]
               (map #(f/slot-premise (:flags (f/read-slot idx %))) [1 2 3])))
        (f/close! idx)))))

;; ---- log recovery -------------------------------------------------------

(deftest scan-log-finds-the-torn-tail
  (with-tmp
    (fn [dir]
      (let [path (str dir "/t.log")
            log  (f/open-log path)
            _    (f/append-record! log {:v 1})
            _    (f/append-record! log {:v 2})
            good-end (f/log-length log)]
        (.seek log (f/log-length log))
        (.writeInt log 999999)                    ; a prefix promising bytes never written
        (.write log (byte-array 8))
        (testing "scan-log returns the offset just past the last intact frame"
          (is (= good-end (f/scan-log log (fn [_ _] nil)))))
        (f/truncate-log! log (f/scan-log log (fn [_ _] nil)))
        (is (= good-end (f/log-length log)) "truncate-log! drops the torn tail")
        (f/close! log)))))

;; ---- the length-only tail walk ------------------------------------------
;; `log-tail-offset` is what the open path uses instead of `scan-log`.  It must agree
;; with `scan-log` wherever `scan-log` was right, and it must keep working where
;; `scan-log` could not: on a log this build cannot decode.

(defn- append-raw-frame!
  "Append `[len][payload]` directly — a frame whose bytes we choose, so a test can write
  one no thaw would accept."
  [^java.io.RandomAccessFile log ^bytes payload]
  (.seek log (f/log-length log))
  (.writeInt log (alength payload))
  (.write log payload))

(deftest the-length-walk-agrees-with-the-decoding-scan
  ;; The claim the substitution rests on.  Not "it works" — the same answer, case by
  ;; case, including the shapes the open path actually meets.
  (with-tmp
    (fn [dir]
      (doseq [[label build!]
              [["an empty log" (fn [_] nil)]
               ["one frame" (fn [log] (f/append-record! log {:v 1}))]
               ["many frames" (fn [log] (dotimes [i 500] (f/append-record! log {:v i :pad (range 20)})))]
               ["a frame larger than the read window"
                (fn [log] (f/append-record! log {:big (vec (range 40000))})
                  (f/append-record! log {:v :after}))]]]
        (testing label
          (let [path (str dir "/" (hash label) ".log")
                log  (f/open-log path)]
            (build! log)
            (is (= (f/scan-log log (fn [_ _] nil)) (f/log-tail-offset log))
                "the walk and the decoding scan disagree")
            (f/close! log)))))))

(deftest the-length-walk-finds-the-same-torn-tail
  (with-tmp
    (fn [dir]
      (doseq [[label tear!]
              [["a prefix promising bytes never written"
                (fn [^java.io.RandomAccessFile log]
                  (.writeInt log 999999) (.write log (byte-array 8)))]
               ["a half-written prefix"
                (fn [^java.io.RandomAccessFile log] (.write log (byte-array 2)))]
               ["a zero-filled tail — a prefix that was never written at all"
                (fn [^java.io.RandomAccessFile log] (.write log (byte-array 4096)))]]]
        (testing label
          (let [path     (str dir "/" (hash label) ".log")
                log      (f/open-log path)
                _        (f/append-record! log {:v 1})
                _        (f/append-record! log {:v 2})
                good-end (f/log-length log)]
            (.seek log (f/log-length log))
            (tear! log)
            (is (= good-end (f/log-tail-offset log)) "the walk mislocated the tear")
            (is (= good-end (f/scan-log log (fn [_ _] nil)))
                "and the decoding scan agrees, so the substitution loses nothing")
            (f/close! log)))))))

(deftest a-log-this-build-cannot-decode-still-opens
  ;; The failure that motivated this: a record class rename made every frame undecodable,
  ;; and the open path — whose only question was how long the log is — raised one
  ;; exception per frame and then truncated the whole log at the first.  The walk never
  ;; thaws, so an undecodable log has an undecodable *record* and an intact length chain.
  (with-tmp
    (fn [dir]
      (let [path (str dir "/opaque.log")
            log  (f/open-log path)]
        (dotimes [i 30] (append-raw-frame! log (.getBytes (str "not-nippy-" i) "UTF-8")))
        (let [full (f/log-length log)]
          (is (= full (f/log-tail-offset log))
              "the walk truncated a log whose frames are merely undecodable")
          (is (not= full (f/scan-log log (fn [_ _] nil)))
              "and scan-log would have — which is the behaviour being retired"))
        (f/close! log)))))

;; ---- the clean-shutdown marker ------------------------------------------

(deftest the-clean-marker-is-believed-only-when-the-length-still-agrees
  (with-tmp
    (fn [dir]
      (let [path (str dir "/c.log")
            log  (f/open-log path)
            _    (dotimes [i 10] (f/append-record! log {:v i}))
            len  (f/log-length log)]
        (testing "a matching length skips the walk"
          (is (= [len false] (f/log-tail-offset-from log len))))
        (testing "every disagreement falls back to the walk"
          (doseq [[label recorded] [["absent"       nil]
                                    ["stale/short"  (- len 40)]
                                    ["past EOF"     (+ len 4096)]
                                    ["not a number" :garbage]]]
            (is (= [len true] (f/log-tail-offset-from log recorded)) (str "marker " label))))
        (testing "and the fallback is still correct when there is a real tear"
          (.seek ^java.io.RandomAccessFile log (f/log-length log))
          (.writeInt ^java.io.RandomAccessFile log 999999)
          (is (= [len true] (f/log-tail-offset-from log (+ len 999999)))
              "a marker longer than the log must not be believed"))
        (f/close! log))))
  (with-tmp
    (fn [dir]
      (testing "write / read / remove round-trips, and a missing marker reads nil"
        (is (nil? (f/read-clean-marker dir)))
        (f/write-clean-marker! dir {"sentexes" 12 "kv" 34})
        (is (= {"sentexes" 12 "kv" 34} (f/read-clean-marker dir)))
        (f/remove-clean-marker! dir)
        (is (nil? (f/read-clean-marker dir)))))))

(deftest validate-idx-tail-tombstones-slots-past-eof
  (with-tmp
    (fn [dir]
      (let [log (f/open-log (str dir "/t.log"))
            idx (f/open-idx (str dir "/t.idx"))
            o0  (f/append-record! log {:v 1})]
        (f/write-slot! idx 0 o0 (- (f/log-length log) o0 4) 0 0)   ; valid
        (f/write-slot! idx 1 (+ (f/log-length log) 1000) 50 0 0)   ; frame past EOF
        (is (= 1 (f/validate-idx-tail! idx log (f/slot-count idx))))
        (is (some? (f/read-slot idx 0)) "the valid slot is untouched")
        (is (:tombstone? (f/read-slot idx 1)) "the past-EOF slot is tombstoned")
        (f/close! log) (f/close! idx)))))

;; ---- crash-safe compaction: the (log, idx) pair -------------------------

(defn- write-one-record! [log-path idx-path v]
  (let [log (f/open-log log-path)
        idx (f/open-idx idx-path)
        o   (f/append-record! log v)]
    (f/write-slot! idx 0 o (- (f/log-length log) o 4) 0 0)
    (f/close! log) (f/close! idx)))

(defn- slot0 [log-path idx-path]
  (let [log (f/open-log log-path)
        idx (f/open-idx idx-path)
        v   (f/read-record log (:offset (f/read-slot idx 0)))]
    (f/close! log) (f/close! idx)
    v))

(deftest recover-compaction-replays-a-committed-crash
  (with-tmp
    (fn [dir]
      (let [lp (str dir "/x.log") ip (str dir "/x.idx")
            {:keys [log-tmp idx-tmp marker]} (f/compact-temp-paths lp ip)]
        (write-one-record! lp ip {:v :orig})            ; the original (pre-compaction) content
        (write-one-record! log-tmp idx-tmp {:v :compacted})  ; the finished compaction temps
        (f/write-commit-marker! marker {:log lp})       ; commit point crossed, then "crash"
        (testing "a marker + both temps present ⇒ finish the compaction on recovery"
          (is (= :replayed (f/recover-compaction! lp ip)))
          (is (= {:v :compacted} (slot0 lp ip)) "the compacted content replaced the original")
          (is (not (exists? marker)) "temps + marker cleaned up")
          (is (not (exists? log-tmp))))))))

(deftest recover-compaction-keeps-originals-when-not-committed
  (with-tmp
    (fn [dir]
      (testing "temps present but NO marker (crashed before commit) ⇒ drop temps, keep original"
        (let [lp (str dir "/a.log") ip (str dir "/a.idx")
              {:keys [log-tmp idx-tmp]} (f/compact-temp-paths lp ip)]
          (write-one-record! lp ip {:v :orig})
          (write-one-record! log-tmp idx-tmp {:v :half})
          (is (= :discarded-incomplete (f/recover-compaction! lp ip)))
          (is (= {:v :orig} (slot0 lp ip)) "the original is authoritative")
          (is (not (exists? log-tmp)) "the orphan temp is removed")))
      (testing "marker present but a temp missing (deeper damage) ⇒ keep originals"
        (let [lp (str dir "/b.log") ip (str dir "/b.idx")
              {:keys [marker]} (f/compact-temp-paths lp ip)]
          (write-one-record! lp ip {:v :orig})
          (f/write-commit-marker! marker {:log lp})       ; marker but no temps
          (is (= :discarded-incomplete (f/recover-compaction! lp ip)))
          (is (= {:v :orig} (slot0 lp ip)))
          (is (not (exists? marker)))))
      (testing "nothing pending ⇒ :none"
        (let [lp (str dir "/c.log") ip (str dir "/c.idx")]
          (write-one-record! lp ip {:v :orig})
          (is (= :none (f/recover-compaction! lp ip))))))))

;; ---- crash-safe compaction: the single log (the KV WAL) -----------------

(deftest recover-log-compaction-branches
  (with-tmp
    (fn [dir]
      (testing "committed (marker + temp) ⇒ replay the temp onto the log"
        (let [lp (str dir "/w.log")
              {:keys [tmp marker]} (f/log-compact-paths lp)]
          (let [log (f/open-log lp)] (f/append-record! log {:v :orig}) (f/close! log))
          (let [t (f/open-log tmp)] (f/append-record! t {:v :compacted}) (f/close! t))
          (f/write-commit-marker! marker {:log lp})
          (is (= :replayed (f/recover-log-compaction! lp)))
          (let [log (f/open-log lp)]
            (is (= {:v :compacted} (f/read-record log 0)))
            (f/close! log))
          (is (not (exists? tmp)))
          (is (not (exists? marker)))))
      (testing "temp only (crashed before commit) ⇒ drop the temp, keep the log"
        (let [lp (str dir "/w2.log")
              {:keys [tmp]} (f/log-compact-paths lp)]
          (let [log (f/open-log lp)] (f/append-record! log {:v :orig}) (f/close! log))
          (let [t (f/open-log tmp)] (f/append-record! t {:v :half}) (f/close! t))
          (is (= :discarded-incomplete (f/recover-log-compaction! lp)))
          (is (not (exists? tmp)))
          (let [log (f/open-log lp)]
            (is (= {:v :orig} (f/read-record log 0)))
            (f/close! log))))
      (testing "clean ⇒ :none"
        (is (= :none (f/recover-log-compaction! (str dir "/w3.log"))))))))

;; ---- whole-blob metadata + markers --------------------------------------

(deftest nippy-blob-round-trip-and-fallbacks
  (with-tmp
    (fn [dir]
      (let [p (str dir "/meta.nippy")]
        (f/write-nippy-atomic! p {:seq 42 :prem #{1 2 3}})
        (is (= {:seq 42 :prem #{1 2 3}} (f/read-nippy-file p)))
        (f/write-nippy-atomic! p {:seq 43})               ; atomic overwrite
        (is (= {:seq 43} (f/read-nippy-file p)))
        (is (= :default (f/read-nippy-file (str dir "/missing.nippy") :default)))
        (testing "a corrupt blob falls back to the default rather than throwing"
          (let [bad (str dir "/bad.nippy")]
            (spit bad "not nippy at all")
            (is (= :default (f/read-nippy-file bad :default)))))))))

(deftest dirty-marker-lifecycle
  (with-tmp
    (fn [dir]
      (is (not (f/dirty-marker-present? dir)))
      (f/create-dirty-marker! dir)
      (is (f/dirty-marker-present? dir) "present after a crash-y open")
      (f/remove-dirty-marker! dir)
      (is (not (f/dirty-marker-present? dir)) "gone after a clean close"))))

(deftest assert-format-adopts-then-guards
  (with-tmp
    (fn [dir]
      (f/ensure-dir! dir)
      (f/assert-format! dir)                              ; stamps format.edn
      (is (.exists (File. ^String dir "format.edn")))
      (f/assert-format! dir)                              ; a known version re-opens fine
      (testing "an unknown future version is refused with a clean error"
        (spit (File. ^String dir "format.edn") (pr-str {:format-version 999}))
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unsupported"
                              (f/assert-format! dir)))))))

;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.disk-fault-test
  "A disk write that fails part-way: what the store holds afterwards, in this process and
  after a reopen, and what every later call is told."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.disk.backend :as backend]
            [vaelii.impl.disk.files :as f]
            [vaelii.impl.disk.kv :as dkv]
            [vaelii.impl.disk.record-store :as drs]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.sentex :as sx])
  (:import [java.io RandomAccessFile]
           [java.nio.channels FileChannel]
           [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]))

(defn- tmpdir ^String []
  (str (Files/createTempDirectory "vaelii-disk-fault-" (into-array FileAttribute []))))

(defn- rm-rf! [^String dir]
  (doseq [f (reverse (file-seq (java.io.File. dir)))] (.delete ^java.io.File f)))

(defn- with-tmp [f]
  (let [dir (tmpdir)]
    (try (f dir)
         (finally (try (backend/close-dir! dir) (catch Throwable _ nil))
                  (rm-rf! dir)))))

(defn- open [dir] (v/open-kb {:backend :disk-log :dir dir}))

(defn- seed! [kb]
  (v/assert kb '(genl dog animal) 'CxUniverse)
  (v/assert kb '(dog Rex) 'CxUniverse)
  (v/assert kb '(implies (dog ?x) (pet ?x)) 'CxUniverse {:direction :forward})
  kb)

(defn- state
  "What the record store holds, as `[sentence context]` pairs, and which of them are
  believed — the two readings a reopen has to agree with."
  [kb]
  (let [recs (:records kb)
        hs   (vec (p/sentex-ids recs))
        in   (v/believed kb hs)
        row  (fn [h] (let [s (p/get-sentex recs h)] [(sx/sentence-of s) (:context s)]))]
    {:stored   (set (map row hs))
     :believed (set (map row (filter in hs)))}))

(defn- refusal-type [thunk]
  (try (thunk) :no-throw
       (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))
       (catch Throwable t (.getName (class t)))))

(defn- stalled-copy
  "What `files/copy-into-channel!` leaves when the transfer moves nothing: the target
  truncated and the refusal."
  [^FileChannel dst ^String src]
  (.truncate dst 0)
  (throw (ex-info (str "copy of " src " stalled at 0") {:type :short-transfer :path src :copied 0})))

(deftest a-record-whose-index-write-failed-does-not-survive
  (with-tmp
    (fn [dir]
      (let [kb     (seed! (open dir))
            before (state kb)]
        (with-redefs [f/copy-into-channel! stalled-copy]
          (is (thrown? Exception (dkv/compact! (:backend (:index kb))))
              "the kv compaction fails past its commit point, so the index refuses writes")
          (is (= :compaction-failed
                 (refusal-type #(v/assert kb '(dog Spot) 'CxUniverse)))
              "the assert is refused by the index")
          (is (= before (state kb))
              "and the record it appended before the index write is gone in this process")
          (v/close! kb))
        (let [kb2 (open dir)]
          (try
            (is (= before (state kb2))
                "a reopen holds what the KB held before the refused assert")
            (testing "and a later assert of the same fact derives its consequence"
              (v/assert kb2 '(dog Spot) 'CxUniverse)
              (is (v/ask? kb2 '(pet Spot) 'CxUniverse)))
            (finally (v/close! kb2))))))))

;; ---- a store that stops ----------------------------------------------------

(defn- refusal
  "`[type reason]` of what `thunk` throws, or `:no-throw`."
  [thunk]
  (try (thunk) :no-throw
       (catch clojure.lang.ExceptionInfo e [(:type (ex-data e)) (:reason (ex-data e))])
       (catch Throwable t (.getName (class t)))))

(defn- entry-points
  "What a caller tries next, keyed by name, each answering `refusal`.  `h` is a stored
  handle to retract."
  [kb h]
  {:assert            (refusal #(v/assert kb '(dog Fido) 'CxUniverse))
   :retract!          (refusal #(v/retract! kb h))
   :edit!             (refusal #(v/edit! kb {:add [['(dog Fido) 'CxUniverse]]}))
   :sentexes-matching (refusal #(doall (v/sentexes-matching kb '(dog ?x) 'CxUniverse)))
   :ask?              (refusal #(v/ask? kb '(pet Rex) 'CxUniverse))})

(deftest an-interrupted-write-stops-the-store-by-name
  ;; An interrupt on a thread blocked in a `FileChannel` operation closes the channel,
  ;; and every later call through it would throw `ClosedChannelException` or
  ;; `IOException: Stream Closed`, with no `:type`.  Setting the flag before the write is
  ;; the deterministic way to land the interrupt inside the store's first channel call.
  (with-tmp
    (fn [dir]
      (let [kb     (seed! (open dir))
            before (state kb)
            h-rex  (v/handle-of kb '(dog Rex) 'CxUniverse)
            first-call @(future
                          (.interrupt (Thread/currentThread))
                          (try (refusal #(v/assert kb '(dog Spot) 'CxUniverse))
                               (finally (Thread/interrupted))))]
        (is (= [:store-unusable :interrupted] first-call)
            "the interrupted write is refused by name")
        (let [calls (entry-points kb h-rex)]
          (is (= {:assert            [:store-unusable :interrupted]
                  :retract!          [:store-unusable :interrupted]
                  :edit!             [:store-unusable :interrupted]
                  :sentexes-matching [:store-unusable :interrupted]
                  :ask?              [:store-unusable :interrupted]}
                 calls)
              "and so is every call after it, with the first fault"))
        (is (= :no-throw (refusal #(v/close! kb))) "close! releases the store without throwing")
        (let [kb2 (open dir)]
          (try
            (is (= before (state kb2)) "a reopen holds what the KB held before the interrupt")
            (finally (v/close! kb2))))))))

(deftest every-call-after-close-is-refused-by-name
  (with-tmp
    (fn [dir]
      (let [kb (seed! (open dir))
            h  (v/handle-of kb '(dog Rex) 'CxUniverse)]
        (v/close! kb)
        (is (= {:assert            [:store-unusable :closed]
                :retract!          [:store-unusable :closed]
                :edit!             [:store-unusable :closed]
                :sentexes-matching [:store-unusable :closed]
                :ask?              [:store-unusable :closed]}
               (entry-points kb h)))
        (is (= [:store-unusable :closed] (refusal #(v/sentex-count kb)))
            "a count off the index is refused too")
        (is (= :no-throw (refusal #(v/close! kb))) "and a second close! is a no-op")))))

(deftest close-drops-the-listeners
  ;; the store refuses every write after `close!`, so a listener left registered would
  ;; hear nothing again and `watchers` would list it as live
  (with-tmp
    (fn [dir]
      (let [kb (open dir)]
        (v/watch kb (fn [_]))
        (v/watch kb '(dog ?x) 'CxUniverse (fn [_]))
        (is (= 2 (count (v/watchers kb))))
        (v/close! kb)
        (is (empty? (v/watchers kb)))))))

(deftest a-failed-fsync-stops-the-store
  ;; A retry of a failed fsync can succeed over pages the kernel already dropped, so the
  ;; failure is latched and the writer told, rather than logged and retried on a tick.
  (with-tmp
    (fn [dir]
      (let [kb (seed! (open dir))]
        (with-redefs [f/force! (fn [_ _] (throw (java.io.IOException. "EIO (simulated)")))]
          (is (= [:store-unusable :fsync-failed]
                 (refusal #(drs/fsync (:records kb))))))
        (is (= [:store-unusable :fsync-failed]
               (refusal #(v/assert kb '(dog Fido) 'CxUniverse)))
            "the next write is refused")
        (is (= :no-throw (refusal #(v/close! kb))))))))

(deftest a-store-that-stops-after-the-write-landed-does-not-fail-the-write
  ;; `assert` stamps provenance after the sentence is stored, chained and settled.  A
  ;; store that stops there has taken the write, and a reopen holds it; the assert
  ;; returns its handle, and the call after it is refused.
  (with-tmp
    (fn [dir]
      (let [kb        (seed! (open dir))
            prov      (:provenance (:kinds (:records kb)))
            read-slot f/read-slot]
        ;; the provenance kind's channels close under the store as the stamp reads its
        ;; slot, as an interrupt on another thread would close them.  Closed before the
        ;; assert, the durability daemon's fsync tick can find them first and stop the
        ;; store while the sentence is still being chained.
        (with-redefs [f/read-slot (fn [^RandomAccessFile raf ^long id]
                                    (when (identical? raf (:idx prov))
                                      (.close (.getChannel ^RandomAccessFile (:log prov)))
                                      (.close (.getChannel raf)))
                                    (read-slot raf id))]
          (let [h (v/assert kb '(dog Spot) 'CxUniverse)]
            (is (integer? h) "the assert returns the handle it stored")))
        (is (= [:store-unusable :channel-closed]
               (refusal #(v/assert kb '(dog Fido) 'CxUniverse)))
            "the next write is refused by name")
        (v/close! kb)
        (let [kb2 (open dir)]
          (try
            (is (v/ask? kb2 '(dog Spot) 'CxUniverse))
            (is (v/ask? kb2 '(pet Spot) 'CxUniverse)
                "a reopen holds the fact and its consequence")
            (finally (v/close! kb2))))))))

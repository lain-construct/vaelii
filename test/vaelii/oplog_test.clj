;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.oplog-test
  "The operation log (`vaelii.impl.oplog`): a KB carrying one records each outermost
  public write as the call that made it, with the inputs the call reads beyond its
  arguments.  A nested write appends no frame, a deferred batch records its closing
  settle, and a configuration call, an argument nippy cannot freeze or a change-feed
  listener's write marks the log unusable.  The frames and the mark read back after a
  reopen, which truncates a torn trailing frame.  The logged record store fsyncs an
  operation's frame before the operation writes a record older than the log, and a
  record write outside every operation marks the log unusable.  Under `:each` every frame
  is fsynced before its operation runs, and a log that cannot take a frame stops: the
  write is refused before it runs, and so is every write after it."
  (:require [clojure.java.io :as io]
            [clojure.test :refer [is use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.oplog :as oplog]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.solve :as solve]
            [vaelii.test-util :as tu])
  (:import [java.io File RandomAccessFile]
           [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- tmpdir ^String []
  (str (Files/createTempDirectory "vaelii-oplog-" (into-array FileAttribute []))))

(defn- rm-rf! [^String dir]
  (doseq [f (reverse (file-seq (io/file dir)))] (.delete ^File f)))

(defn- with-log
  "Call `(f lkb log dir)`, where `lkb` is `kb` attached to an operation log in a fresh
  directory `dir` (`oplog/attach`), opened with `opts`.  The log is closed and the
  directory removed afterwards."
  ([kb f] (with-log kb nil f))
  ([kb opts f]
   (let [dir (tmpdir)
         log (oplog/open-log dir 0 opts)]
     (try (f (oplog/attach kb log) log dir)
          (finally (oplog/close-log! log)
                   (rm-rf! dir))))))

(tu/deftest-kb a-write-to-an-older-record-fsyncs-its-frame-first
  (tu/with-terms [dog Fido Rex CxPets]
    (let [older (v/assert kb (list dog Fido) CxPets)]
      (with-log kb
        (fn [lkb log _]
          (v/assert lkb (list dog Rex) CxPets)
          (is (zero? (:guard-checks @(:state log)))
              "an operation that only adds records writes nothing below the watermark")
          (v/retract! lkb older)
          (let [{:keys [ops synced guard-checks]} @(:state log)]
            (is (pos? guard-checks) "the retraction writes a record below the watermark")
            (is (= ops synced) "and the frame describing it is on disk before it does")))))))

(tu/deftest-kb a-record-write-outside-an-operation-marks-the-log-unusable
  (tu/with-terms [dog Fido CxPets]
    (let [h (v/assert kb (list dog Fido) CxPets)]
      (with-log kb
        (fn [lkb log _]
          (p/mark-premise (:records lkb) h :default)
          (is (= [:unlogged-write :mark-premise] (oplog/unusable log))))))))

(tu/deftest-kb an-outermost-write-is-one-frame-carrying-its-inputs
  (tu/with-terms [dog Fido CxPets]
    (with-log kb
      (fn [lkb log _]
        (let [s (list dog Fido)
              h (binding [v/*clock* (constantly 42) v/*creator* 'tester]
                  (v/assert lkb s CxPets))
              frames (oplog/read-frames log)]
          (is (= [{:op :assert :args [s CxPets]}]
                 (mapv #(select-keys % [:op :args]) frames)))
          (is (= {:clock 42 :creator 'tester}
                 (select-keys (:in (first frames)) [:clock :creator])))
          (is (= 42 (:created (v/provenance lkb h)))
              "the call stamps the clock its frame records"))))))

(tu/deftest-kb a-write-nested-in-another-appends-no-frame
  (tu/with-terms [dog Fido Rex CxPets]
    (with-log kb
      (fn [lkb log _]
        (v/assert-many lkb [(list dog Fido) (list dog Rex)] CxPets)
        (is (= [:assert-many] (mapv :op (oplog/read-frames log)))
            "the asserts inside `assert-many` are part of its frame")))))

(tu/deftest-kb a-deferred-batch-records-its-closing-settle
  (tu/with-terms [dog Fido Rex CxPets]
    (with-log kb
      (fn [lkb log _]
        (v/with-deferred-settle lkb
          (v/assert lkb (list dog Fido) CxPets)
          (v/assert lkb (list dog Rex) CxPets))
        (let [frames (oplog/read-frames log)]
          (is (= [:assert :assert :settle] (mapv :op frames)))
          (is (= [true true] (mapv (comp :defer-settle? :in) (take 2 frames)))
              "each assert records that its settle was deferred"))))))

(tu/deftest-kb a-configuration-call-marks-the-log-unusable
  (with-log kb
    (fn [lkb log _]
      (is (nil? (oplog/unusable log)))
      (v/set-solver lkb solve/local-solver)
      (is (= [:config :set-solver] (oplog/unusable log)))
      (is (= [{:unusable [:config :set-solver]}] (oplog/read-frames log))
          "the mark is a frame, so it outlives the process"))))

;; The argument is `forward-chain`'s `:on-progress` callback, which no record store keeps.
;; An argument a write stores, such as a provenance value, reaches a disk record store,
;; and that store's own nippy freeze refuses it before the write completes.
(tu/deftest-kb an-argument-nippy-cannot-freeze-marks-the-log-unusable
  (with-log kb
    (fn [lkb log _]
      (let [r (v/forward-chain lkb {:on-progress (fn [_] nil)})]
        (is (= [:unfreezable :forward-chain] (take 2 (oplog/unusable log))))
        (is (number? (:derived r)) "the write the frame describes still runs")))))

(tu/deftest-kb a-listener-write-marks-the-log-unusable
  (tu/with-terms [dog Fido Rex CxPets]
    (with-log kb
      (fn [lkb log _]
        (let [token (v/watch lkb (fn [_] (v/assert lkb (list dog Rex) CxPets)))]
          (try (v/assert lkb (list dog Fido) CxPets)
               (finally (v/unwatch lkb token))))
        (is (= [:listener-write :assert] (oplog/unusable log)))))))

(tu/deftest-kb a-reopen-reads-the-frames-and-truncates-a-torn-tail
  (tu/with-terms [dog Fido CxPets]
    (with-log kb
      (fn [lkb log dir]
        (v/assert lkb (list dog Fido) CxPets)
        (v/set-solver lkb solve/local-solver)
        (oplog/close-log! log)
        (let [path (str dir "/oplog/ops.log")
              len  (.length (io/file path))]
          ;; a length prefix promising more bytes than follow it
          (with-open [raf (RandomAccessFile. path "rw")]
            (.seek raf len)
            (.writeInt raf 1000)
            (.write raf (byte-array [1 2 3])))
          (let [log2 (oplog/open-log dir 0)]
            (try
              (is (= [:assert nil] (mapv :op (oplog/read-frames log2))))
              (is (= [:config :set-solver] (oplog/unusable log2)))
              (is (= len (.length (io/file path))) "the torn frame is gone")
              (finally (oplog/close-log! log2)))))))))

(tu/deftest-kb under-each-every-frame-is-fsynced-before-its-operation-runs
  (tu/with-terms [dog Fido Rex CxPets]
    (with-log kb {:fsync :each}
      (fn [lkb log _]
        (is (= :each (oplog/fsync-mode log)))
        (v/assert lkb (list dog Fido) CxPets)
        (v/assert lkb (list dog Rex) CxPets)
        (let [{:keys [ops synced guard-checks]} @(:state log)]
          (is (= 2 ops synced))
          (is (zero? guard-checks) "neither operation wrote below the watermark"))))))

(tu/deftest-kb a-log-that-cannot-take-a-frame-refuses-the-write-and-every-write-after
  (tu/with-terms [dog Fido Rex CxPets]
    (with-log kb
      (fn [lkb log _]
        (let [before (v/sentex-count lkb)]
          ;; the channel closes under the log, as a thread interrupt closes it
          (.close ^RandomAccessFile (:raf log))
          (let [refusals (mapv (fn [x]
                                 (try (v/assert lkb (list dog x) CxPets) nil
                                      (catch clojure.lang.ExceptionInfo e
                                        (select-keys (ex-data e) [:type :reason]))))
                               [Fido Rex])]
            (is (= :store-unusable (:type (first refusals))))
            (is (= (first refusals) (second refusals))
                "the second write is refused by the fault the first latched"))
          (is (= before (v/sentex-count lkb)) "neither write ran"))))))

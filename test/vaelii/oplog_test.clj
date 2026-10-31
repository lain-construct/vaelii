;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.oplog-test
  "The operation log (`vaelii.impl.oplog`): a KB carrying one records each outermost
  public write as the call that made it, with the inputs the call reads beyond its
  arguments.  A nested write appends no frame, a deferred batch records its closing
  settle, and a configuration call, an argument nippy cannot freeze, a change-feed
  listener's write or a `VirtualMachineError` inside a write marks the log unusable; a
  `VirtualMachineError` freezing a frame propagates before the write runs.  The frames
  and the mark read back after a reopen, which truncates a torn trailing frame.  The
  logged record store fsyncs an operation's frame before the operation writes a record
  older than the log, and a record write outside every operation marks the log unusable.
  Under `:each` every frame is fsynced before its operation runs, and a log that cannot
  take a frame stops: the write is refused before it runs, and so is every write after
  it."
  (:require [clojure.java.io :as io]
            [clojure.test :refer [is use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.oplog :as oplog]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.solve :as solve]
            [vaelii.test-util :as tu])
  (:import [java.io RandomAccessFile]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- with-log
  "Call `(f lkb log dir)`, where `lkb` is `kb` attached to an operation log in a fresh
  directory `dir` (`oplog/attach`), opened with `opts`.  The log is closed and the
  directory removed afterwards."
  ([kb f] (with-log kb nil f))
  ([kb opts f]
   (let [dir (tu/tmpdir "vaelii-oplog-")
         log (oplog/open-log dir 0 opts)]
     (try (f (oplog/attach kb log) log dir)
          (finally (oplog/close-log! log)
                   (tu/rm-rf! dir))))))

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
              "the call records the clock value its frame holds"))))))

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

;; `:stamp-inert` is the keyword an `ops.log` of a development build holds for the
;; `:mark-inert` operation.
(tu/deftest-kb both-keywords-of-the-inert-mark-operation-replay-through-mark-inert
  (let [seen (atom [])]
    (with-redefs [v/mark-inert! (fn [_ opts] (swap! seen conj opts))]
      (oplog/replay! kb [{:op :stamp-inert :args [{:handles [7]}] :in {}}
                         {:op :mark-inert :args [{:handles [8]}] :in {}}]))
    (is (= [{:handles [7]} {:handles [8]}] @seen))))

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

(defn- deep-sentence
  "A sentence nested `n` deep, which overflows the stack nippy freezes it on."
  [n]
  (reduce (fn [acc _] (list 'p acc)) 'X (range n)))

(tu/deftest-kb a-virtual-machine-error-freezing-a-frame-neither-marks-the-log-nor-runs-the-write
  (doseq [[arg cls] [[(lazy-seq (cons 1 (lazy-seq (throw (OutOfMemoryError. "freeze")))))
                      OutOfMemoryError]
                     [(deep-sentence 200000) StackOverflowError]]]
    (with-log kb
      (fn [lkb log _]
        (let [ran    (atom false)
              thrown (try (oplog/run-op lkb :assert :replay [arg] (constantly {})
                                        (fn [_] (reset! ran true)))
                          nil
                          (catch Throwable t (class t)))]
          (is (= [cls false nil []]
                 [thrown @ran (oplog/unusable log) (oplog/read-frames log)])))))))

(tu/deftest-kb a-virtual-machine-error-inside-a-logged-write-marks-the-log
  (tu/with-terms [dog Fido CxPets]
    (doseq [[label throwable] [["thrown as itself" (OutOfMemoryError. "mid-write")]
                               ["wrapped" (ex-info "wrapped" {} (StackOverflowError.))]]]
      (with-log kb
        (fn [lkb log _]
          (let [s (list dog Fido)]
            (is (thrown? Throwable
                         (oplog/run-op lkb :assert :replay [s CxPets] (constantly {})
                                       (fn [_] (throw throwable))))
                label)
            (let [vm (.getName (class (or (ex-cause throwable) throwable)))]
              (is (= [{:op :assert :args [s CxPets]} {:unusable [:vm-error :assert vm]}]
                     (mapv #(if (:op %) (select-keys % [:op :args]) %) (oplog/read-frames log)))
                  label))))))))

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

;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.oplog-seal-test
  "Seals and restores (`vaelii.impl.seal`).  A `:disk-snapshot` KB attached to an
  operation log is sealed, takes writes, and its directory is copied as a crash would
  leave it; a restore over the copy replays the log to the belief a recover of the same
  records computes.  A frame whose replay writes a different record, a frame lost after
  its records reached the disk, and an unusable log each decline the restore.  A
  `:seal`-class operation seals when it returns, a KB whose network does not cover its
  records cannot be sealed, and closing the directory seals it."
  (:require [clojure.java.io :as io]
            [clojure.test :refer [deftest is]]
            [vaelii.core :as v]
            [vaelii.impl.disk.files :as f]
            [vaelii.impl.oplog :as oplog]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.seal :as seal]
            [vaelii.impl.solve :as solve]
            [vaelii.test-util :as tu])
  (:import [java.io File RandomAccessFile]
           [java.nio.file CopyOption Files StandardCopyOption]
           [java.nio.file.attribute FileAttribute]))

(defn- tmpdir ^String []
  (str (Files/createTempDirectory "vaelii-seal-" (into-array FileAttribute []))))

(defn- rm-rf! [^String dir]
  (doseq [f (reverse (file-seq (io/file dir)))] (.delete ^File f)))

(defn- copy-dir!
  "Copy `from` into `to` as the files stand — a crash's view of a directory whose store
  is still open."
  [^String from ^String to]
  (let [src (.toPath (io/file from)) dst (.toPath (io/file to))]
    (doseq [^File f (file-seq (io/file from))
            :let [t (.toFile (.resolve dst (.relativize src (.toPath f))))]]
      (if (.isDirectory f)
        (.mkdirs t)
        ;; A store still open on `from` renames a temp file away between the listing and
        ;; the copy (the durability daemon's `counters.nippy` write), and a file gone by
        ;; then is one the directory no longer holds.
        (try
          (Files/copy (.toPath f) (.toPath t)
                      ^"[Ljava.nio.file.CopyOption;"
                      (into-array CopyOption [StandardCopyOption/REPLACE_EXISTING]))
          (catch java.nio.file.NoSuchFileException _ nil))))))

(defn- open
  ([dir] (open dir nil))
  ([dir opts] (v/open-kb (merge {:backend :disk-snapshot :dir dir} opts))))

(defn- write-world!
  "A forward rule, three facts it fires on, a retraction of one, and a fourth fact, all
  through `kb`.  Six operations."
  [kb]
  (v/assert kb '(set/forwardRule (implies (and (animal ?x)) (mortal ?x))) 'CxUniverse)
  (let [hs (mapv #(v/assert kb (list 'animal %) 'CxUniverse) '[Socrates Plato Aristotle])]
    (v/retract! kb (second hs))
    (v/assert kb '(animal Zeno) 'CxUniverse)))

(defn- belief
  "Handle -> believed?, over every sentex `kb`'s records hold."
  [kb]
  (into (sorted-map)
        (map (fn [h] [h (v/in? kb h)]))
        (p/sentex-ids (oplog/inner-records (:records kb)))))

(defn- log-path ^String [dir] (str dir "/oplog/ops.log"))

(defn- rewrite-log!
  "Replace the operation frames of `dir`'s log with `(f frames)`, keeping its header."
  [dir f]
  (let [path   (log-path dir)
        frames (with-open [raf (RandomAccessFile. path "r")]
                 (let [acc (transient [])]
                   (f/scan-log raf (fn [_ v] (conj! acc v)))
                   (persistent! acc)))]
    (with-open [raf (f/open-log path)]
      (.setLength raf 0)
      (doseq [fr (cons (first frames) (f (vec (rest frames))))]
        (f/append-record! raf fr)))))

(defn- restore-copy
  "Copy `src` to a fresh directory, open it `{:recover? false}` and restore it.  Calls
  `(check r)` with the restore's result, then closes whatever it opened and removes the
  copy.  `(edit dir)` runs on the copy before the open."
  ([src check] (restore-copy src identity check))
  ([src edit check]
   (let [dir (tmpdir)]
     (try
       (copy-dir! src dir)
       (edit dir)
       (let [kb (open dir {:recover? false})
             r  (seal/restore! kb)]
         (try (check r)
              (finally (v/close! (or (:kb r) kb)))))
       (finally (rm-rf! dir))))))

(deftest a-restore-replays-to-the-belief-a-recover-computes
  (tu/with-snapshot-platform
    (let [a (tmpdir) c (tmpdir)]
      (try
        (let [lkb (seal/attach! (open a))]
          (try
            (write-world! lkb)
            (copy-dir! a c)
            (let [kb-c (open c)]
              (try
                (restore-copy a (fn [r]
                                  (is (:restored r))
                                  (is (= 6 (:frames r)))
                                  (is (= (belief kb-c) (belief (:kb r)))
                                      "the restored KB believes what a recover of its records believes")))
                (finally (v/close! kb-c))))
            (finally (v/close! lkb))))
        (finally (rm-rf! a) (rm-rf! c))))))

(deftest a-replayed-write-that-differs-from-the-store-declines
  (tu/with-snapshot-platform
    (let [a (tmpdir)]
      (try
        (let [lkb (seal/attach! (open a))]
          (try
            (write-world! lkb)
            (restore-copy a
                          #(rewrite-log! % (fn [ops]
                                             (mapv (fn [fr]
                                                     (if (= '(animal Zeno) (first (:args fr)))
                                                       (assoc fr :args ['(animal Heraclitus) 'CxUniverse])
                                                       fr))
                                                   ops)))
                          (fn [r]
                            (is (not (:restored r)))
                            (is (= :diverged (first (:reason r))))
                            (is (false? (:clean? r)) "replayed state is in the KB")))
            (finally (v/close! lkb))))
        (finally (rm-rf! a))))))

(deftest a-frame-lost-after-its-records-reached-the-disk-declines
  (tu/with-snapshot-platform
    (let [a (tmpdir)]
      (try
        (let [lkb (seal/attach! (open a))]
          (try
            (write-world! lkb)
            (restore-copy a
                          #(rewrite-log! % (fn [ops] (vec (butlast ops))))
                          (fn [r]
                            (is (not (:restored r)))
                            (is (= :extra-records (:reason r))
                                "the last assert's records sit above every handle the replay allocated")))
            (finally (v/close! lkb))))
        (finally (rm-rf! a))))))

(deftest a-frame-that-fails-rather-than-refuses-stops-the-restore
  (tu/with-snapshot-platform
    ;; A frame that refused when it was made refuses again, and replay goes on.  A frame
    ;; that throws something else did not refuse: skipped, it restored a KB missing the
    ;; write — here the retraction, so `(animal Plato)` came back believed — and answered
    ;; `:restored true`.
    (let [a (tmpdir)]
      (try
        (let [lkb (seal/attach! (open a))]
          (try
            (write-world! lkb)
            (let [dir (tmpdir)]
              (try
                (copy-dir! a dir)
                (let [kb (open dir {:recover? false})]
                  (try
                    (is (thrown? OutOfMemoryError
                                 (with-redefs [v/retract! (fn [& _] (throw (OutOfMemoryError. "witness")))]
                                   (seal/restore! kb))))
                    (finally (v/close! kb))))
                (finally (rm-rf! dir))))
            (finally (v/close! lkb))))
        (finally (rm-rf! a))))))

(deftest an-unusable-log-declines
  (tu/with-snapshot-platform
    (let [a (tmpdir)]
      (try
        (let [lkb (seal/attach! (open a))]
          (try
            (v/assert lkb '(animal Socrates) 'CxUniverse)
            (v/set-solver lkb solve/local-solver)
            (restore-copy a (fn [r]
                              (is (not (:restored r)))
                              (is (= [:unusable [:config :set-solver]] (:reason r)))
                              (is (:clean? r))))
            (finally (v/close! lkb))))
        (finally (rm-rf! a))))))

(deftest a-log-with-a-damaged-frame-inside-it-declines
  (tu/with-snapshot-platform
    ;; A frame that does not thaw with frames after it ends what can be replayed.  Read as a
    ;; torn tail, the log was cut there and the frames before it replayed: here the two
    ;; retractions were lost, the replay rewrote both records, and the restore answered
    ;; `:restored true` with `(animal Plato)` believed.  A retraction allocates no handle,
    ;; so the extra-records check has nothing to find.
    (let [a (tmpdir)]
      (try
        (let [lkb (seal/attach! (open a))]
          (try
            (let [hs (mapv #(v/assert lkb (list 'animal %) 'CxUniverse) '[Socrates Plato Aristotle])]
              (v/retract! lkb (hs 1))
              (v/retract! lkb (hs 2)))
            (let [offset (atom nil)]
              (restore-copy a
                            (fn [dir]
                              ;; frame 0 is the header, 1-3 the asserts, 4 the first retraction
                              (with-open [raf (RandomAccessFile. (log-path dir) "rw")]
                                (let [off (loop [pos 0 k 0]
                                            (if (= k 4)
                                              pos
                                              (do (.seek raf pos)
                                                  (recur (+ pos 4 (.readInt raf)) (inc k)))))]
                                  (reset! offset off)
                                  (.seek raf (+ off 4))
                                  (.write raf (byte-array 2)))))
                            (fn [r]
                              (is (not (:restored r)))
                              (is (= [:unusable [:damaged-frame @offset]] (:reason r)))
                              (is (:clean? r)))))
            (finally (v/close! lkb))))
        (finally (rm-rf! a))))))

(deftest a-seal-class-operation-seals-when-it-returns
  (tu/with-snapshot-platform
    (let [a (tmpdir) txt (tmpdir)]
      (try
        (spit (io/file txt "CxUniverse.txt") "(animal Socrates)\n(animal Plato)\n")
        (let [lkb (seal/attach! (open a))
              g   (:generation (seal/read-seal a))]
          (try
            (v/assert lkb '(animal Zeno) 'CxUniverse)
            (v/load-text! lkb txt)
            (is (= (inc (long g)) (:generation (seal/read-seal a))))
            (is (nil? (oplog/unusable (:oplog lkb))) "the seal starts the log again")
            (is (empty? (oplog/read-frames (:oplog lkb))))
            (finally (v/close! lkb))))
        (finally (rm-rf! a) (rm-rf! txt))))))

(deftest a-kb-whose-network-does-not-cover-its-records-is-not-sealed
  (tu/with-snapshot-platform
    (let [a (tmpdir)]
      (try
        (let [lkb (seal/attach! (open a))
              g   (:generation (seal/read-seal a))]
          (try
            (v/assert lkb '(animal Zeno) 'CxUniverse)
            ;; `clear!` wipes the records and leaves the network's nodes, so the seal it
            ;; requests is refused
            (v/clear! lkb)
            (is (= [:seal :clear] (oplog/unusable (:oplog lkb)))
                "the refused seal leaves the mark the operation made")
            (is (= g (:generation (seal/read-seal a))) "and starts no generation")
            (finally (v/close! lkb))))
        (finally (rm-rf! a))))))

(deftest closing-the-directory-seals-it
  (tu/with-snapshot-platform
    (let [a (tmpdir)]
      (try
        (let [lkb (seal/attach! (open a))
              g   (:generation (seal/read-seal a))
              h   (v/assert lkb '(animal Zeno) 'CxUniverse)]
          (v/close! lkb)
          (is (= (inc (long g)) (:generation (seal/read-seal a))))
          (let [kb (open a {:recover? false})
                r  (seal/restore! kb)]
            (try
              (is (:restored r))
              (is (zero? (long (:frames r))) "every write is in the images the close wrote")
              (is (v/in? (:kb r) h))
              (finally (v/close! (or (:kb r) kb))))))
        (finally (rm-rf! a))))))

;; ---- open-kb with :oplog? ---------------------------------------------------

(defn- opened [kb] (dissoc (oplog/opened (:oplog kb)) :ms))

(defn- write-dilemma!
  "`write-world!`, a `genl` edge, and a rebuttal the settle leaves standing: two forward
  rules concluding opposite literals over one individual."
  [kb]
  (write-world! kb)
  (v/assert kb '(genl animal living) 'CxUniverse)
  (v/assert kb '(set/forwardRule (implies (and (quaker ?x)) (pacifist ?x))) 'CxUniverse)
  (v/assert kb '(set/forwardRule (implies (and (republican ?x)) (not (pacifist ?x)))) 'CxUniverse)
  (v/assert kb '(quaker Nixon) 'CxUniverse)
  (v/assert kb '(republican Nixon) 'CxUniverse))

(defn- reading
  "What a reader sees of `kb` without a write: the stored count, belief per handle, the
  supertypes of `animal`, and the contradictions."
  [kb]
  {:count          (v/sentex-count kb)
   :belief         (belief kb)
   :genls          (v/genls kb 'animal 'CxUniverse)
   :contradictions (set (map #(set (map :sentence (:sides %))) (v/contradictions kb)))})

(deftest an-open-with-an-oplog-restores-what-a-crash-left
  (tu/with-snapshot-platform
    (let [a (tmpdir) c (tmpdir) d (tmpdir)]
      (try
        (let [lkb (open a {:oplog? true})]
          (try
            (is (= {:restored false :reason :no-seal} (opened lkb))
                "a directory with no seal is opened from its records, attached and sealed")
            (is (some? (seal/read-seal a)))
            (write-dilemma! lkb)
            ;; two copies of the directory as a crash leaves it
            (copy-dir! a c)
            (copy-dir! a d)
            (finally (v/close! lkb))))
        (let [restored (open c {:oplog? true})
              rebuilt  (open d)]
          (try
            (is (= {:restored true :frames 11} (opened restored)))
            (is (seq (:contradictions (reading rebuilt))) "the world leaves a dilemma standing")
            (is (= (reading rebuilt) (reading restored))
                "the restored KB answers each read as a rebuild from the same records answers it")
            (is (number? (v/assert restored '(animal Thales) 'CxUniverse)) "and takes writes")
            (finally (v/close! restored) (v/close! rebuilt))))
        (finally (rm-rf! a) (rm-rf! c) (rm-rf! d))))))

(deftest an-open-whose-restore-declines-rebuilds-from-the-records-and-seals
  (tu/with-snapshot-platform
    (let [a (tmpdir) c (tmpdir)]
      (try
        (let [lkb (open a {:oplog? true})]
          (try
            (v/assert lkb '(animal Socrates) 'CxUniverse)
            (v/set-solver lkb solve/local-solver)
            (copy-dir! a c)
            (finally (v/close! lkb))))
        (let [g  (:generation (seal/read-seal c))
              kb (open c {:oplog? true})]
          (try
            (is (= {:restored false :reason [:unusable [:config :set-solver]]} (opened kb)))
            (is (v/ask? kb '(animal Socrates) 'CxUniverse) "the records are rebuilt")
            (is (= (inc (long g)) (:generation (seal/read-seal c))) "and sealed again")
            (is (nil? (oplog/unusable (:oplog kb))) "so the log starts usable")
            (finally (v/close! kb))))
        (finally (rm-rf! a) (rm-rf! c))))))

(deftest a-clean-close-reopens-by-restoring-no-operation
  (tu/with-snapshot-platform
    (let [a (tmpdir)]
      (try
        (let [h (let [lkb (open a {:oplog? :tick})]
                  (try (v/assert lkb '(animal Zeno) 'CxUniverse)
                       (finally (v/close! lkb))))
              kb (open a {:oplog? :tick})]
          (try
            (is (= {:restored true :frames 0} (opened kb)))
            (is (= :tick (oplog/fsync-mode (:oplog kb))))
            (is (v/in? kb h))
            (finally (v/close! kb))))
        (finally (rm-rf! a))))))

(deftest seal-starts-a-generation-and-declines-while-a-settle-is-pending
  (tu/with-snapshot-platform
    (let [a (tmpdir) b (tmpdir)]
      (try
        (let [kb (open a {:oplog? true})
              g  (:generation (seal/read-seal a))]
          (try
            (v/assert kb '(animal Zeno) 'CxUniverse)
            (let [r (v/seal kb)]
              (is (= {:sealed true :generation (inc (long g))}
                     (select-keys r [:sealed :generation])))
              (is (pos? (long (:watermark r))))
              (is (empty? (oplog/read-frames (:oplog kb))) "the operation is in the images"))
            (v/with-deferred-settle kb
              (v/assert kb '(animal Thales) 'CxUniverse)
              (is (= {:sealed false :reason :settle-deferred :busy true} (v/seal kb))))
            (is (= [:assert :settle] (mapv :op (oplog/read-frames (:oplog kb))))
                "the declined seal leaves the log as it was")
            (finally (v/close! kb))))
        (let [kb (open b)]
          (try (is (= {:sealed false :reason :not-applicable} (v/seal kb)) "a KB with no log")
               (finally (v/close! kb))))
        (finally (rm-rf! a) (rm-rf! b))))))

(deftest oplog-is-read-on-a-disk-snapshot-kb-that-recovers
  (doseq [[opts mismatch] [[{:backend :disk-snapshot :oplog? :yes}            :bad-value]
                           [{:backend :disk-log :oplog? true}                 :conflict]
                           [{:backend :disk-snapshot :oplog? true :recover? false} :conflict]]]
    (let [dir (tmpdir)
          e   (try (v/open-kb (assoc opts :dir dir)) nil
                   (catch clojure.lang.ExceptionInfo e e)
                   (finally (rm-rf! dir)))]
      (is (= {:type :unknown-option :mismatch mismatch}
             (select-keys (ex-data e) [:type :mismatch]))
          (pr-str opts)))))

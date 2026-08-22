;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.wipe-fsync-cost-test
  "What one wipe costs the **filesystem**, as counted directory fsyncs — the gate for the
  class of regression `lein perf` and `assert_cost_test` are both structurally blind to.

  `assert_cost_test` counts index operations, and says so in its own preamble: work that
  is not an index operation is invisible there, a record-store touch included.  `lein
  perf` asserts a growth ratio and never a millisecond, so a constant added per call
  moves both sizes alike and divides out.  A directory fsync added to a wipe is neither
  an index read nor a growth term, so it passes both untouched.

  One regression has already shipped through that gap.  `clear-records!` calls
  `delete-compact-temps!` once per record kind, and that helper fsynced the parent
  directory unconditionally — three whole-store flushes per wipe on a store with no
  compaction in flight, where the three `.delete` calls had found nothing to remove
  (`cde74f49`, fixed in `2bc2d719`).  A directory fsync is `F_FULLFSYNC` on macOS,
  measured at ~5 ms, and the suite's own `fresh` fixture wipes per test — so the disk
  configurations ran roughly twice the wall clock of the memory ones, and the matrix
  stayed green throughout because no verdict depends on elapsed time.

  ## Why a count and not a duration

  Same argument `assert_cost_test` makes: the quantity is a number of calls the engine
  makes, not a measurement of the machine, so it is bit-identical across runs, across
  machines and on a loaded box.  There is no warm-up, no tolerance and no noise floor,
  which is what lets it live in the suite rather than behind a command somebody has to
  remember.

  ## Why both directions are pinned

  An exact count that only said \"a quiet wipe fsyncs once\" would be satisfied by
  deleting the fsync outright, which is a crash-safety bug and not an optimization: the
  *removal* of a failed compaction's commit marker is what the next open repairs from,
  and a marker whose directory entry never reached the platter is a marker that comes
  back.  So the second test plants the temps a failed compaction leaves and pins the
  fsync that clears them.  The two together say the fsync is owed exactly when a
  directory entry actually went away.

  ## What it does not catch

  - **Any fsync but the directory one.**  `write-nippy-atomic!` also fsyncs the file it
    wrote, and the durability tick fsyncs the logs; neither is counted here.
  - **A wipe that is slow for another reason.**  This counts one syscall family on one
    operation, and nothing else about what a wipe costs.
  - **Another thread's fsyncs.**  The count is scoped to the calling thread on purpose,
    so the durability daemon's own tick cannot move it.

  The KB is pinned to `:backend :disk` rather than inheriting `VAELII_TEST_BACKEND`, for
  the reason `assert_cost_test` pins `:memory`: the gate then says the same thing on all
  thirteen matrix configurations instead of thirteen different things."
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.disk.backend :as backend]
            [vaelii.impl.disk.files :as f])
  (:import [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]))

(defn- rm-rf! [^String dir]
  (doseq [x (reverse (file-seq (java.io.File. dir)))] (.delete ^java.io.File x)))

(defn- with-tmp
  "Run `(g dir)` in a fresh temp directory, closing any disk stores opened on it — so the
  durability daemon does not outlive the directory — and deleting it afterwards."
  [g]
  (let [dir (str (Files/createTempDirectory "vaelii-wipe-fsync-" (into-array FileAttribute [])))]
    (try (g dir)
         (finally (backend/close-dir! dir) (rm-rf! dir)))))

(defn- counting-dir-fsyncs
  "Run `thunk`, returning `[result n]` where `n` is the directory fsyncs made **on this
  thread**.  `fsync-dir!` is private, so the var is resolved rather than quoted; the
  original still runs, so this counts the real thing and does not stub it out."
  [thunk]
  (let [fsync-var (ns-resolve 'vaelii.impl.disk.files 'fsync-dir!)
        original  @fsync-var
        caller    (Thread/currentThread)
        n         (atom 0)]
    (with-redefs-fn {fsync-var (fn [path]
                                 (when (identical? caller (Thread/currentThread))
                                   (swap! n inc))
                                 (original path))}
      (fn [] [(thunk) @n]))))

(defn- record-pairs
  "The `(log, idx)` pairs the record store keeps under `dir`, **discovered** rather than
  spelled out: a record kind added to the store then moves this gate's numbers, which is
  a diff somebody reads, instead of slipping past a hard-coded three."
  [dir]
  (->> (file-seq (io/file dir))
       (filter #(and (.isFile ^java.io.File %)
                     (str/ends-with? (.getName ^java.io.File %) ".log")
                     (= "records" (.getName (.getParentFile ^java.io.File %)))))
       (map (fn [^java.io.File x]
              (let [log (.getPath x)]
                {:log log :idx (str/replace log #"\.log$" ".idx")})))
       (sort-by :log)
       vec))

(defn- populated-kb
  "A disk KB over `dir` holding enough that a wipe has records to drop."
  [dir]
  (doto (v/open-kb {:backend :disk :dir dir :recover? false})
    (v/assert '(genl dog animal) 'CxUniverse {:strength :monotonic})
    (v/assert '(genl animal organism) 'CxUniverse {:strength :monotonic})
    (v/assert '(isa Muffet dog) 'CxUniverse {:strength :monotonic})))

(deftest a-quiet-wipe-fsyncs-the-directory-once
  (with-tmp
    (fn [dir]
      (let [kb    (populated-kb dir)
            pairs (record-pairs dir)]
        (testing "the store keeps the three record kinds this gate's numbers assume"
          (is (= 3 (count pairs))
              (str "record kinds under " dir ": " (mapv :log pairs))))
        (testing "no compaction is in flight, so nothing needs its removal made durable"
          (let [[_ n] (counting-dir-fsyncs #(v/clear! kb))]
            ;; ONE: `clear-records!` rewrites the counters blob through
            ;; `write-nippy-atomic!`, which fsyncs the directory the rename landed in.
            ;; The three `delete-compact-temps!` calls beside it find nothing to delete
            ;; and so owe nothing.  Re-pin deliberately; do not widen to a ceiling.
            (is (= 1 n)
                "a wipe with no compaction in flight costs exactly one directory fsync")))))))

(deftest a-wipe-that-finds-a-failed-compaction-fsyncs-its-removal
  (with-tmp
    (fn [dir]
      (let [kb    (populated-kb dir)
            pairs (record-pairs dir)
            temps (mapv (fn [{:keys [log idx]}] (f/compact-temp-paths log idx)) pairs)]
        (is (= 3 (count pairs)) "three record kinds, as above")
        ;; what a compaction that died past its commit point leaves behind: the marker
        ;; the next open would finish the install from, and both temps it would install.
        (doseq [{:keys [log-tmp idx-tmp marker]} temps]
          (spit marker "") (spit log-tmp "") (spit idx-tmp ""))
        (testing "the wipe supersedes the install, and the removal is made durable"
          (let [[_ n] (counting-dir-fsyncs #(v/clear! kb))]
            ;; FOUR: the counters blob as above, plus one per kind whose temps this wipe
            ;; actually removed.  This is the half that must not be optimized away — a
            ;; marker whose directory entry never reached the platter comes back.
            (is (= 4 n)
                "a wipe clearing three kinds' compaction temps fsyncs once per removal, plus the counters")))
        (testing "and the temps are gone, which is the bug the fsync makes durable"
          (doseq [{:keys [log-tmp idx-tmp marker]} temps]
            (is (not (.exists (io/file marker)))  (str marker " survived the wipe"))
            (is (not (.exists (io/file log-tmp))) (str log-tmp " survived the wipe"))
            (is (not (.exists (io/file idx-tmp))) (str idx-tmp " survived the wipe"))))))))

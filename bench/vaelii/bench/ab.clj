;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.bench.ab
  "Fixed workloads timed in absolute milliseconds, for `scripts/perf-ab.sh` to run on two
  revisions and compare.  `lein perf` judges growth, so a cost added to every operation
  moves both of its readings and passes; a slower revision beside a faster one on the
  same machine and JDK does not.

  The probes call `vaelii.core` and nothing below it, so the copy at the head revision
  loads against an older one unchanged, and both sides time the same code.  Each prints
  one `ab-result <probe> <ms>` line: the median of `reps` timed runs after `warm`
  discarded ones.

  Run: `lein with-profile +bench run -m vaelii.bench.ab [--only a,b] [--list]`"
  (:require [clojure.string :as str]
            [vaelii.core :as v]))

(def ^:private cx 'CxAb)

(def ^:private next-space (atom 100))
(def ^:private opened (atom []))

(defn- fresh-kb
  "An empty KB on a space of its own: a closed space refuses a later open's writes.
  `-main` closes it after the probe that opened it."
  []
  (let [kb (v/open-kb {:space (swap! next-space inc) :recover? false})]
    (swap! opened conj kb)
    kb))

(defn- median [xs]
  (let [s (vec (sort xs))] (nth s (quot (count s) 2))))

(defn- timed-ms [f]
  (let [t (System/nanoTime)] (f) (/ (- (System/nanoTime) t) 1e6)))

(defn- sample
  "Median ms of `reps` timed calls of `f` after `warm` discarded ones."
  [f warm reps]
  (dotimes [_ warm] (f))
  (median (repeatedly reps #(timed-ms f))))

(defn- sample-fresh
  "`sample` of `(f kb)` over a KB `setup` builds per call, the build outside the timed
  window."
  [setup f warm reps]
  (let [one #(let [kb (setup)] (timed-ms (fn [] (f kb))))]
    (dotimes [_ warm] (one))
    (median (repeatedly reps one))))

(defn- node [i] (symbol (str "AbN" i)))

(defn- dag-edges
  "A seeded DAG over n nodes: node i above 0 has one or two parents below it."
  [n]
  (let [rng (java.util.Random. 4010)]
    (vec (distinct
          (for [i (range 1 n)
                p (repeatedly (inc (.nextInt rng 2)) #(.nextInt rng i))]
            (list 'abEdge (node i) (node p)))))))

(defn- dag-kb
  "A KB holding a dag of n nodes under a transitive `abEdge`."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(transitive abEdge) cx {:strength :monotonic})
    (doseq [e (dag-edges n)] (v/assert kb e cx {:chain? false}))
    kb))

(defn- shuffle-with [xs seed]
  (let [l (java.util.ArrayList. ^java.util.Collection xs)]
    (java.util.Collections/shuffle l (java.util.Random. seed))
    (vec l)))

(defn- ancestors-of [kb i]
  (doall (v/ask kb (list 'abEdge (node i) '?y) cx)))

;; ---- the probes ---------------------------------------------------------
;;
;; Each mirrors a row of the field benchmark, small enough that the whole set runs in one
;; JVM in well under a minute.

(defn- genl-read
  "A genls read of a fresh type right after its edge, under a 2000-type braid (field w1 genl)."
  []
  (let [kb (fresh-kb)
        t  #(symbol (str "abg" % "_t"))
        k  (atom 0)]
    (v/with-deferred-settle kb
      (doseq [i (range 3)] (v/assert kb (list 'genl (t i) 'thing) cx {:strength :monotonic}))
      (doseq [i (range 3 2000) p [(- i 3) (- i 2)]]
        (v/assert kb (list 'genl (t i) (t p)) cx {:strength :monotonic})))
    (sample #(let [x (symbol (str "abgx" (swap! k inc) "_t"))]
               (v/assert kb (list 'genl x (t 1999)) cx {:strength :monotonic})
               (count (v/genls kb x)))
            3 15)))

(defn- transitive-ask
  "The ancestors of the deepest node over a transitive predicate, warm (field w1 warm)."
  []
  (let [kb (dag-kb 5000)]
    (sample #(ancestors-of kb 4999) 5 25)))

(defn- retract-reask
  "100 edges retracted, the ancestors re-asked, the edges restored (field w11 b100, w2del)."
  []
  (let [kb    (dag-kb 5000)
        batch (take 100 (shuffle-with (dag-edges 5000) 7))]
    (sample #(do (run! (fn [e] (some->> (v/handle-of kb e cx) (v/retract! kb))) batch)
                 (ancestors-of kb 4999)
                 (run! (fn [e] (v/assert kb e cx {:chain? false})) batch))
            3 15)))

(defn- assert-load
  "20,000 binary facts into an empty KB (field wload)."
  []
  (sample-fresh fresh-kb
                #(dotimes [i 20000] (v/assert % (list 'abVal (node i) i) cx {:chain? false}))
                2 7))

(defn- forward-join
  "Forward rules materializing every ancestor pair of a 600-node dag (field w4, w2c)."
  []
  (sample-fresh #(let [kb (fresh-kb)]
                   (doseq [e (dag-edges 600)] (v/assert kb e cx {:chain? false}))
                   (v/assert-rule kb ['(abEdge ?c ?p)] '(abAnc ?c ?p) cx
                                  {:direction :forward :chain? false})
                   (v/assert-rule kb ['(abAnc ?d ?m) '(abEdge ?m ?p)] '(abAnc ?d ?p) cx
                                  {:direction :forward :chain? false})
                   kb)
                #(v/forward-chain % {:max-depth 1000000 :max-derivations 100000000})
                2 7))

(defn- naf-prove
  "Nodes not reaching the deepest one, through `unknown` (field wneg)."
  []
  (let [kb (dag-kb 3000)]
    (dotimes [i 3000] (v/assert kb (list 'ab_node (node i)) cx {:chain? false}))
    (doseq [b (ancestors-of kb 2999)]
      (v/assert kb (list 'ab_reach (get b '?y)) cx {:chain? false}))
    (sample #(doall (v/prove kb ['(ab_node ?n) '(unknown (ab_reach ?n))] cx)) 3 15)))

(defn- arith-prove
  "Edges whose endpoints' values differ by more than half the nodes, through
  `evaluate` and `greaterThan` (field warith).  The edge predicate is not declared
  transitive, as in the field row: a transitive one answers its closure in a conjunction
  that binds its subject first."
  []
  (let [kb (fresh-kb)]
    (doseq [e (dag-edges 2000)] (v/assert kb e cx {:chain? false}))
    (dotimes [i 2000] (v/assert kb (list 'abVal (node i) i) cx {:chain? false}))
    (sample #(doall (v/prove kb ['(abEdge ?c ?p) '(abVal ?c ?cv) '(abVal ?p ?pv)
                                 '(evaluate ?d (- ?cv ?pv)) '(greaterThan ?d 1000)] cx))
            2 7)))

(defn- read-after-import
  "Ancestor asks over a 2000-node dag that a dump import loaded, timed after the import.
  The records-only import runs inside `with-bulk-writes`, so every dynamic-var read after
  it reads the thread's binding frame; listed last, so the probes before it run before
  any bulk load in the JVM."
  []
  (let [dir (str (java.nio.file.Files/createTempDirectory
                  "ab-import" (make-array java.nio.file.attribute.FileAttribute 0)))
        kb  (fresh-kb)]
    (v/export! (dag-kb 2000) dir)
    (v/import! kb dir)
    (sample #(dotimes [i 50] (ancestors-of kb (+ 1900 i))) 2 7)))

(def probes
  [#'genl-read #'transitive-ask #'retract-reask #'assert-load #'forward-join #'naf-prove
   #'arith-prove #'read-after-import])

(defn -main [& args]
  (let [[flag value] args
        only (when (= flag "--only") (set (str/split (str value) #",")))]
    (if (= flag "--list")
      (doseq [p probes] (println (format "%-16s %s" (:name (meta p)) (:doc (meta p)))))
      (do (println "ab-java" (System/getProperty "java.version"))
          (doseq [p probes :let [k (str (:name (meta p)))] :when (or (nil? only) (only k))]
            (println "ab-result" k (format "%.3f" (double (p))))
            (flush)
            (run! v/close! (first (reset-vals! opened []))))))
    (shutdown-agents)
    (System/exit 0)))

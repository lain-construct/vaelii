;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.bench.plan
  "What conjunctive planning is worth, and — first — whether the cost model it rests on
  composes at all.

  **The q-error curve is the gate, and it is read before any plan is timed.**  For each
  prefix of the chosen order, `q = max(est/actual, actual/est)` against the count the
  engine actually returns for that prefix.  Flat in the join depth means the estimates
  compose and an ordering built over them is worth having; growing in the depth means
  they do not, and no amount of better ordering would rescue that.  Judging a cost
  model by the cost of the plans it produces is two inferences downstream of the
  defect: it reports \"the plan is bad\" without reporting that the estimator is why.

  Then the ordering.  `vaelii.impl.plan` splits a conjunction into blocks — connected
  components, two literals in one when they share a variable — orders each internally
  by cheapest joined prefix, and ranks the blocks by the transposition law,
  `s/(n−1)` descending.  What that buys over ranking every generator alike is a
  **cartesian factor**: a literal sharing no variable with anything else, which nothing
  narrows and which narrows nothing, so wherever it runs it multiplies the row count of
  everything after it.  Ranking it by its own extent ranks it exactly wrong, since a
  *selective* one is taken first, where the multiplication lands on the whole rest of
  the plan.

  So the corpus is a 1:1 chain (`link1 ?a ?b`, `link2 ?b ?c`, …) that collapses to one
  row per step once its join variable is bound, beside a small `loose` relation
  sharing nothing with it.  The chain is what a real theory's antecedents look like;
  `loose` is the literal a per-literal estimate cannot rank.

  Three orders are timed at each width — the conjunction as written (planning off, the
  reference), the plan with every generator in one block (`greedy`), and the plan with
  the blocks ranked (`placed`) — plus the planning call itself, since a planner that
  wins on execution and loses more on the plan has not won.  Wall-clock is a **ratio**
  against the best of the three, so the reading means the same thing on a loaded box;
  the row counts beside it are structural and are the trustworthy half.

  A last section runs the same conjunction as a **rule's antecedents**, which is where
  the cost matters most and where nothing else measures it — no rule in the shipped KB
  or the test world has three generators.  See `rule-expansion-ms` for why its
  cartesian antecedent is spelled differently.

  Run: `lein bench-plan [chain-size] [loose-size]`  (default 400 40)"
  (:require [clojure.string :as str]
            [vaelii.core :as v]
            [vaelii.impl.plan :as plan]))

(def ^:private orderer #'vaelii.impl.plan/block-order)
(def ^:private greedy  #'vaelii.impl.plan/greedy-block)
(def ^:private empty-prefix #'vaelii.impl.plan/empty-prefix)

(defn- with-strategy*
  "Run `f` with the planner forced to one strategy.  `:greedy` is the block split
  removed — every generator in one pool, taken cheapest-joined-prefix first whether it
  is connected to anything or not — which is the thing the split has to beat.  Both are
  private because nothing in the engine chooses between them; a measurement is the one
  caller that has to."
  [strategy f]
  (let [real @orderer]
    (try
      (when (= strategy :greedy)
        (alter-var-root orderer
                        (constantly (fn [gens bound cost summary-of _anchor]
                                      {:pairs (:pairs (@greedy gens @empty-prefix bound
                                                               cost summary-of))
                                       :info  {}}))))
      (f)
      (finally (alter-var-root orderer (constantly real))))))

(defn- links [n] (mapv #(symbol (str "benchLink" %)) (range n)))

(defn- build!
  "`width` chained relations of `n` facts each, plus a `loose` relation of `m`."
  [kb width n m]
  (v/assert-many kb
                 (concat
                  (mapcat (fn [i]
                            (let [p (nth (links width) i)]
                              (for [j (range n)]
                                (list p (symbol (str "BenchN" i "v" j))
                                      (symbol (str "BenchN" (inc i) "v" j))))))
                          (range width))
                  (for [j (range m)]
                    (list 'benchLoose (symbol (str "BenchU" j)) (symbol (str "BenchV" j)))))
                 'CxUniverse {:chain? false}))

(defn- conjunction [width]
  (into ['(benchLoose ?u ?v)]
        (map (fn [i] (list (nth (links width) i)
                           (symbol (str "?n" i)) (symbol (str "?n" (inc i))))))
        (range width)))

(defn- timed [f]
  (f)
  (let [t0 (System/nanoTime), n (count (f))]
    [n (/ (- (System/nanoTime) t0) 1e6)]))

(defn- prefix-rows
  "How many solutions the first `k` literals of `order` actually return."
  [kb order k]
  (binding [plan/*enabled* false]
    (count (v/prove kb (vec (take k order)) 'CxUniverse))))

(defn- rows
  "Σ of the partial-solution counts an order passes through — the structural cost,
  read off the engine by asking each prefix for its solutions."
  [kb order]
  (reduce + (for [k (range 1 (inc (count order)))] (prefix-rows kb order k))))

(defn- q-errors
  "`max(est/actual, actual/est)` per join depth, for the plan the engine would run.
  The estimate is `explain`'s `:est-prefix`, which is the number the ordering itself
  turned on rather than one computed alongside it."
  [kb q]
  (let [steps (plan/explain kb q 'CxUniverse)
        order (mapv :goal steps)]
    (mapv (fn [k]
            (let [est (double (max 1 (:est-prefix (nth steps (dec k)))))
                  act (double (max 1 (prefix-rows kb order k)))]
              (max (/ est act) (/ act est))))
          (range 1 (inc (count order))))))

(defn- rule-expansion-ms
  "Wall clock for proving a rule's head, planned and unplanned.

  The same claim through a **rule**, which is where it matters most and where nothing
  else measures it.  A rule's stored antecedent order is *canonical* order — chosen so
  two spellings of one rule dedup to one sentex — and canonical order is structural, so
  it bears no relation to what is cheap to run; the planner is what stands between the
  two.  No rule in the shipped KB or the test world has three generators, so this
  corpus is the only place a three-or-more-antecedent join is timed.

  The rule is `:backward` and asserted with `:chain? false`, so nothing is derived and
  stored ahead of the question: what is timed is the rule *expansion*, which is the
  conjunction `plan/order` is handed by `res/planned-antecedents`.

  The cartesian antecedent is `benchAlone` here and `benchLoose` in the query section
  above, and the difference is the whole point of timing this separately.  Canonical
  order is structural, so whether it is any good is an accident of spelling: it sorts
  `benchLoose` *after* the links, where it belongs, and `benchAlone` in front of them,
  where it multiplies the join.  This measures the case where the accident goes the
  other way, which is the case the planner exists for."
  [kb width m]
  (let [head (symbol (str "benchHead" width))
        ante (into ['(benchAlone ?u ?v)]
                   (map (fn [i] (list (nth (links width) i)
                                      (symbol (str "?n" i)) (symbol (str "?n" (inc i))))))
                   (range width))]
    (v/assert-many kb (for [j (range m)]
                        (list 'benchAlone (symbol (str "BenchU" j)) (symbol (str "BenchV" j))))
                   'CxUniverse {:chain? false})
    (v/assert-rule kb ante (list head '?n0 (symbol (str "?n" width)))
                   'CxUniverse {:direction :backward :chain? false})
    (let [goal [(list head '?a '?b)]
          run  (fn [on?]
                 (binding [plan/*enabled* on?]
                   ;; one discarded run to warm the JIT and the literal cache, so what
                   ;; is timed is the join rather than the first-call overhead
                   (dotimes [_ 1] (count (v/prove kb goal 'CxUniverse)))
                   (let [t0 (System/nanoTime)
                         n  (count (v/prove kb goal 'CxUniverse))]
                     [n (/ (- (System/nanoTime) t0) 1e6)])))]
      [(run false) (run true)])))

(defn- plan-cost-ms [kb q strategy iters]
  (with-strategy* strategy
    (fn []
      (dotimes [_ 200] (plan/order kb q 'CxUniverse {}))
      (let [t0 (System/nanoTime)]
        (dotimes [_ iters] (plan/order kb q 'CxUniverse {}))
        (/ (- (System/nanoTime) t0) 1e6 iters)))))

(defn -main [& args]
  (let [n (or (some-> (first args) Long/parseLong) 400)
        m (or (some-> (second args) Long/parseLong) 40)
        kbs (into {} (for [width [2 3 4 5]]
                       (let [kb (v/open-kb {:backend :memory :space 30 :recover? false})]
                         (build! kb width n m)
                         [width kb])))]
    (println (format "vaelii conjunctive planning — chain of %,d facts per link, loose relation of %,d" n m))

    ;; ---- the cost model, before any plan is timed --------------------------
    (println "\n  q-error per join depth — the estimate against the rows the prefix returns.")
    (println "  Flat in k is the claim that the estimates compose; growing in k withdraws it.")
    (println (format "\n  %-7s %s" "lits" "q at k = 1, 2, …"))
    (println (str "  " (apply str (repeat 60 \-))))
    (doseq [width [2 3 4 5]]
      (let [qs (q-errors (kbs width) (conjunction width))]
        (println (format "  %-7s %s" (inc width)
                         (str/join "  " (map #(format "%.2f" %) qs))))))

    ;; ---- and then the orders ----------------------------------------------
    ;; the conjunction is the chain plus the loose literal, so it is one wider
    (println (format "\n  %-7s %-30s %10s %10s %9s %11s"
                     "lits" "strategy" "rows" "exec ms" "exec x" "plan ms"))
    (println (str "  " (apply str (repeat 82 \-))))
    (println "  row counts are TRUSTED (structural); wall-clock is a ratio against the best of the three.")
    (doseq [width [2 3 4 5]]
      (let [kb (kbs width)
            q  (conjunction width)
            plans {:written  (vec q)
                   :greedy   (with-strategy* :greedy   #(plan/order kb q 'CxUniverse {}))
                   :placed   (with-strategy* :placed #(plan/order kb q 'CxUniverse {}))}
            runs  (into {} (for [[k order] plans]
                             [k {:order order
                                 :rows  (rows kb order)
                                 :ms    (second (timed #(binding [plan/*enabled* false]
                                                          (v/prove kb order 'CxUniverse))))}]))
            best  (apply min (map (comp :ms val) runs))]
        (doseq [k [:written :greedy :placed]]
          (let [{:keys [rows ms]} (runs k)]
            (println (format "  %-7s %-30s %,10d %10.1f %8.2fx %11.4f"
                             (if (= k :written) (inc width) "")
                             (name k) rows ms (/ ms best)
                             (if (= k :written)
                               0.0
                               (plan-cost-ms kb q (if (= k :greedy) :greedy :placed) 1000))))))
        (println)))
    (println "  A `placed` row that beats `greedy` on rows is the whole claim; one that does")
    (println "  not, at a width the engine actually sees, is the claim being withdrawn.")

    ;; ---- and the same claim through a rule ---------------------------------
    (println "\n  The same conjunction as a rule's antecedents, reached by proving its head.")
    (println "  Stored antecedent order is canonical order, so what the planner is")
    (println "  standing between is the author's spelling and the cost of running it.")
    (println (format "\n  %-9s %10s %14s %14s %9s"
                     "antes" "solutions" "unplanned ms" "planned ms" "speedup"))
    (println (str "  " (apply str (repeat 62 \-))))
    (doseq [width [3 4]]
      (let [[[n0 off] [n1 on]] (rule-expansion-ms (kbs width) width m)]
        (println (format "  %-9s %,10d %14.1f %14.1f %8.2fx"
                         (inc width) n1 off on (/ off (max 0.001 on))))
        (when (not= n0 n1)
          (println (format "  !! planned returned %,d solutions and unplanned %,d — planning may not change the answer set"
                           n1 n0)))))))

;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.bench.plan
  "What conjunctive planning is worth, on the shape that separates the two cost models.

  `vaelii.impl.plan` orders a conjunction cheapest-literal-first, and holds one class
  of literal back from that: a **cartesian factor**, sharing no variable with anything
  else in the conjunction.  Nothing narrows it and it narrows nothing, so wherever it
  runs it multiplies the row count of everything after it — and ranking it by its own
  extent ranks it exactly wrong, since a *selective* one is taken first, where the
  multiplication lands on the whole rest of the plan.

  So the corpus is a 1:1 chain (`link1 ?a ?b`, `link2 ?b ?c`, …) that collapses to one
  row per step once its join variable is bound, beside a small `loose` relation
  sharing nothing with it.  The chain is what a real theory's antecedents look like;
  `loose` is the literal an estimate cannot rank.

  Three orders are timed at each width — the conjunction as written (planning off, the
  reference), the plan with every generator ranked alike (`greedy`), and the plan with
  the cartesian factors held back (`placed`) — plus the planning call itself, since a
  planner that wins on execution and loses more on the plan has not won.  Wall-clock is
  a **ratio** against the best of the three, so the reading means the same thing on a
  loaded box; the row counts beside it are structural and are the trustworthy half.

  Run: `lein bench-plan [chain-size] [loose-size]`  (default 400 40)"
  (:require [vaelii.core :as v]
            [vaelii.impl.plan :as plan]))

(def ^:private placer #'vaelii.impl.plan/deferring-isolated-order)
(def ^:private greedy #'vaelii.impl.plan/greedy-order)

(defn- with-strategy*
  "Run `f` with the planner forced to one strategy.  `:greedy` is the placement rule
  removed — cheapest-first over every generator alike, isolated or not — which is the
  thing the rule has to beat.  Both are private because nothing in the engine chooses
  between them; a measurement is the one caller that has to."
  [strategy f]
  (let [real @placer]
    (try
      (when (= strategy :greedy)
        (alter-var-root placer (constantly (fn [gens bound cost _others]
                                             (@greedy gens bound cost)))))
      (f)
      (finally (alter-var-root placer (constantly real))))))

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
                 'UniverseContext {:chain? false}))

(defn- conjunction [width]
  (into ['(benchLoose ?u ?v)]
        (map (fn [i] (list (nth (links width) i)
                           (symbol (str "?n" i)) (symbol (str "?n" (inc i))))))
        (range width)))

(defn- timed [f]
  (f)
  (let [t0 (System/nanoTime), n (count (f))]
    [n (/ (- (System/nanoTime) t0) 1e6)]))

(defn- rows
  "Σ of the partial-solution counts an order passes through — the structural cost,
  read off the engine by asking each prefix for its solutions."
  [kb order]
  (reduce + (for [k (range 1 (inc (count order)))]
              (binding [plan/*enabled* false]
                (count (v/prove kb (vec (take k order)) 'UniverseContext))))))

(defn- plan-cost-ms [kb q strategy iters]
  (with-strategy* strategy
    (fn []
      (dotimes [_ 200] (plan/order kb q 'UniverseContext {}))
      (let [t0 (System/nanoTime)]
        (dotimes [_ iters] (plan/order kb q 'UniverseContext {}))
        (/ (- (System/nanoTime) t0) 1e6 iters)))))

(defn -main [& args]
  (let [n (or (some-> (first args) Long/parseLong) 400)
        m (or (some-> (second args) Long/parseLong) 40)]
    (println (format "vaelii conjunctive planning — chain of %,d facts per link, loose relation of %,d" n m))
    (println "row counts are TRUSTED (structural); wall-clock is a ratio against the best of the three.")
    ;; the conjunction is the chain plus the loose literal, so it is one wider
    (println (format "\n  %-7s %-30s %10s %10s %9s %11s"
                     "lits" "strategy" "rows" "exec ms" "exec x" "plan ms"))
    (println (str "  " (apply str (repeat 82 \-))))
    (doseq [width [2 3 4 5]]
      (let [kb (v/open-kb {:backend :memory :space 30 :recover? false})
            _  (build! kb width n m)
            q  (conjunction width)
            plans {:written  (vec q)
                   :greedy   (with-strategy* :greedy   #(plan/order kb q 'UniverseContext {}))
                   :placed   (with-strategy* :placed #(plan/order kb q 'UniverseContext {}))}
            runs  (into {} (for [[k order] plans]
                             [k {:order order
                                 :rows  (rows kb order)
                                 :ms    (second (timed #(binding [plan/*enabled* false]
                                                          (v/prove kb order 'UniverseContext))))}]))
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
    (println "  not, at a width the engine actually sees, is the claim being withdrawn.")))

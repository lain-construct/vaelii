(ns vaelii.bench.cyclic
  "Does a CYCLIC forward rule set terminate?  Datalog theory says yes — range-restricted
  rules with no existential/function head invent no new terms, so the Herbrand base is
  finite and semi-naive evaluation with dedup reaches a fixpoint.  It can be *large* and it
  can hit the depth guard, but it must terminate.  This checks the claim directly, to tell a
  finite-but-huge fixpoint (a scale problem) apart from a re-derivation bug (a real one).

  Workload: transitive closure of an m-cycle Ind0→Ind1→…→Ind{m-1}→Ind0 under the cyclic rule
  `(rel ?x ?y) ∧ (rel ?y ?z) ⇒ (rel ?x ?z)` (consequent predicate = antecedent predicate).
  The closure of an m-cycle is the complete graph *with self-loops* = **m² `rel` facts**, and
  a self-loop needs a path of length m ⇒ derivation depth ≈ m, so past the depth guard
  (`:max-depth`, default 64) the longest facts are truncated and the count falls below m².

  It terminates (every m reaches the full m² closure, dedup working) and it is fast, both
  of which rest on `add-just*`'s redundant-justification fast path (`jtms`): a re-derivation
  of an already-believed fact via another path must not relabel the fact's whole growing
  forward closure, or this goes cubic.  Measured 100 facts 88 ms, **400 facts 242 ms**
  (~O(n log n)).  This bench is the regression guard: if the ms column goes cubic again,
  the fast path regressed.

  Run: `lein bench-cyclic [max-m]`  (default 12)."
  (:require [vaelii.core :as v]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.protocols :as p]))

(defn- run [m]
  (let [kb (kb/open-kb {:backend :memory :record-space 38 :index-space 39 :recover? false}
                       (fn [_] nil) (fn [_] nil))]
    (p/clear-records! (:records kb)) (p/clear-index! (:index kb))
    (v/assert-rule kb ['(rel ?x ?y) '(rel ?y ?z)] '(rel ?x ?z) 'CyContext {:direction :forward})
    (let [inds (mapv #(symbol (str "Ind" %)) (range m))
          t0   (System/nanoTime)]
      (v/with-deferred-settle kb
        (dotimes [i m]
          (v/assert kb (list 'rel (nth inds i) (nth inds (mod (inc i) m))) 'CyContext)))
      (let [ms    (/ (- (System/nanoTime) t0) 1e6)
            n     (p/count-with-functor (:index kb) 'rel)
            trunc (boolean (get-in (v/chain-stats kb) [:last :truncated?]))]
        (println (format "  m=%-3d | rel facts %,7d  (m² = %,7d, %s) | truncated %-5s | %,.0f ms | TERMINATED"
                         m n (* m m) (if (= n (* m m)) "full closure" "partial") trunc ms))))))

(defn -main [& args]
  (let [maxm (or (some-> (first args) Long/parseLong) 12)]
    (println "cyclic forward-chaining test — TC of an m-cycle, no skolemization")
    (println "every row TERMINATES with the full m² closure; ms is now ~O(n log n) since the")
    (println "add-just* redundant-justification fast path landed (was ~O(n³)).\n")
    (doseq [m (take-while #(<= % maxm) [3 5 8 10 12 15 20])]
      (run m))
    (shutdown-agents)))

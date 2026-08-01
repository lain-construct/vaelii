(ns vaelii.reach-memo-test
  "The per-query memo for a transitive predicate's closure lookups
  (`observe/*reach-memo*`).  A rule with two transitive antecedents solves the second
  once per binding of the join variable; without the memo each solve re-walks the
  closure over the nodes many seeds share.  The memo — opened once per backward search
  (`observe/with-search-scope`) — collapses those repeated neighbour lookups to one store hit per node,
  and (being fresh per query, over a KB a query never mutates) can never go stale."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.resolution :as res]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- counting-closure-lookups
  "Wrap `matches-visible`, counting only the closure's neighbour probes for `pred` —
  those `succs`/`preds-of` issue, which always carry the `?rv` variable.  A
  `FactProver` lookup of the same predicate uses the goal's own variables, so it is
  not counted; this isolates the closure walk."
  [pred calls]
  (let [orig res/matches-visible]
    (fn [kb s c]
      (when (and (sequential? s) (= pred (first s)) (some #(= '?rv %) s))
        (swap! calls inc))
      (orig kb s c))))

(tu/deftest-kb succs-is-memoized-only-under-a-bound-cache
  (tu/with-terms [before A B FarmContext]
    (v/assert kb (list 'transitive before) FarmContext)
    (v/assert kb (list before A B) FarmContext)
    (let [calls (atom 0)]
      (with-redefs [res/matches-visible (counting-closure-lookups before calls)]
        (testing "no memo bound -> each succs call hits the store"
          (reset! calls 0)
          (binding [observe/*reach-memo* nil]
            (#'provers/succs kb before A FarmContext)
            (#'provers/succs kb before A FarmContext))
          (is (= 2 @calls)))
        (testing "a bound memo -> repeated succs of the same node hits the store once"
          (reset! calls 0)
          (binding [observe/*reach-memo* (atom {})]
            (#'provers/succs kb before A FarmContext)
            (#'provers/succs kb before A FarmContext))
          (is (= 1 @calls)))
        (testing "preds-of shares the cache without colliding with succs (different dir)"
          (reset! calls 0)
          (binding [observe/*reach-memo* (atom {})]
            (#'provers/succs kb before A FarmContext)
            (#'provers/preds-of kb before A FarmContext))    ; a different direction of A
          (is (= 2 @calls) "succ and pred of the same node are distinct keys"))))))

(tu/deftest-kb two-transitive-antecedents-stay-correct-and-linear
  (tu/with-terms [before twoHop FarmContext]
    (v/assert kb (list 'transitive before) FarmContext)
    (let [nodes (vec (repeatedly 11 tu/tmp-ind))]           ; N0 -> N1 -> … -> N10, a chain
      (doseq [i (range 10)] (v/assert kb (list before (nodes i) (nodes (inc i))) FarmContext))
      ;; twoHop(?a,?c) :- before(?a,?b) ∧ before(?b,?c), backward-only so nothing is
      ;; forward-materialized and the join genuinely walks the `before` closure twice
      (v/assert-rule kb [(list before '?a '?b) (list before '?b '?c)]
                     (list twoHop '?a '?c) FarmContext {:direction :backward})
      (let [calls (atom 0)]
        (with-redefs [res/matches-visible (counting-closure-lookups before calls)]
          (let [ans (set (map #(get % '?c) (v/query kb (list twoHop (nodes 0) '?c) FarmContext {:max-depth 2})))]
            (testing "correct: N0 two-hops to every node from N2 onward"
              (is (= (set (subvec nodes 2)) ans)))
            (testing "the closure is walked once, not once per join binding"
              ;; ~11 distinct nodes each probed once; un-memoized is ~66 (11+10+…+1)
              (is (< @calls 25)
                  (str "closure lookups " @calls " should be ~linear, not quadratic")))))))))

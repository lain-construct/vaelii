;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.provers-test
  "The pluggable prover query engine (v/ask): transitivity, disjointness, `different`
  (the unique-name assumption, ground only), facts, rules, and the query plan with
  per-prover estimates."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(tu/deftest-kb transitivity-prover-answers-genl
  (let [dog (tu/tmp-type) mammal (tu/tmp-type) animal (tu/tmp-type)]
    (v/assert kb (list 'genl dog mammal)  'UniverseContext)
    (v/assert kb (list 'genl mammal animal) 'UniverseContext)
    (testing "supertype query returns the full transitive closure, not just direct edges"
      (let [ys (set (map #(get % '?y) (v/ask kb (list 'genl dog '?y) 'UniverseContext)))]
        (is (contains? ys mammal))
        (is (contains? ys animal))))                    ; transitive — no genl fact for this
    (testing "subtype query"
      (let [xs (set (map #(get % '?x) (v/ask kb (list 'genl '?x animal) 'UniverseContext)))]
        (is (contains? xs dog))
        (is (contains? xs mammal))))
    (testing "ground genl decided by the closure"
      (is (v/ask? kb (list 'genl dog animal) 'UniverseContext))
      (is (not (v/ask? kb (list 'genl animal dog) 'UniverseContext))))))

(tu/deftest-kb the-self-pair-goal-answers-the-reflexive-closure
  ;; `genls` / `context-up` are reflexive closures, so a self-pair holds of every node
  ;; the relation holds at all — the arm exists to bind one variable rather than throw
  ;; on a duplicate map key, and its answer is the node set, not the empty set.
  (tu/with-terms [dog_t animal_t AContext]
    (v/assert kb (list 'genl dog_t animal_t) 'UniverseContext)
    (v/assert kb (list 'genlContext AContext 'UniverseContext) 'UniverseContext)
    (testing "ground self-pairs are decided by the reflexive closure"
      (is (v/ask? kb (list 'genl dog_t dog_t) 'UniverseContext))
      (is (v/ask? kb (list 'genlContext AContext AContext) 'UniverseContext)))
    (testing "the open self-pair binds every node of the relation, without throwing"
      (let [xs (set (map #(get % '?x) (v/ask kb (list 'genl '?x '?x) 'UniverseContext)))]
        (is (contains? xs dog_t))
        (is (contains? xs animal_t)))
      (let [cs (set (map #(get % '?x)
                         (v/ask kb (list 'genlContext '?x '?x) 'UniverseContext)))]
        (is (contains? cs AContext))))))

(tu/deftest-kb disjointness-prover-answers-disjoint
  (let [dog (tu/tmp-type) cat (tu/tmp-type) fish (tu/tmp-type)]
    (v/assert kb (list 'disjoint dog cat) 'UniverseContext)
    (testing "ground disjointness"
      (is (v/ask? kb (list 'disjoint dog cat) 'UniverseContext))
      (is (not (v/ask? kb (list 'disjoint dog fish) 'UniverseContext))))
    (testing "enumerate what a type is disjoint with"
      (is (= #{cat} (set (map #(get % '?t) (v/ask kb (list 'disjoint dog '?t) 'UniverseContext))))))))

(tu/deftest-kb ask-reaches-a-forward-derived-fact-but-expands-no-rule
  ;; The two halves of what `ask` means for rules, and they are easy to conflate.  A
  ;; *forward* rule's conclusion is stored when the fixpoint runs it, so `ask` sees a
  ;; stored fact and needs no rule expansion to answer.  A *backward* rule's conclusion
  ;; is never stored, and `ask` expands no rule, so nothing in the registry reaches it —
  ;; that is `query` with a depth, or `prove`.
  (let [parentOf (tu/tmp-pred) grandparentOf (tu/tmp-pred) ancestorOf (tu/tmp-pred)
        tom (tu/tmp-ind) bob (tu/tmp-ind) ann (tu/tmp-ind)]
    (v/assert-rule kb [(list parentOf '?x '?y) (list parentOf '?y '?z)]
                   (list grandparentOf '?x '?z) 'FamContext)
    (v/assert-rule kb [(list parentOf '?x '?y)] (list ancestorOf '?x '?y) 'FamContext
                   {:direction :backward})
    (v/assert kb (list parentOf tom bob) 'FamContext)
    (v/assert kb (list parentOf bob ann) 'FamContext)
    (testing "the forward rule's conclusion is stored, so the fact prover answers it"
      (is (= #{ann} (set (map #(get % '?who)
                              (v/ask kb (list grandparentOf tom '?who) 'FamContext)))))
      (is (seq (v/sentexes-matching kb (list grandparentOf tom ann) 'FamContext))
          "stored, which is why `ask` sees it"))
    (testing "the backward rule's conclusion is not, and `ask` does not expand it"
      (is (not (v/ask? kb (list ancestorOf tom '?who) 'FamContext)))
      (is (= #{bob} (set (map #(get % '?who)
                              (v/query kb (list ancestorOf tom '?who) 'FamContext
                                       {:max-depth 1}))))
          "the same conclusion, from the reader whose job is expanding rules"))))

(tu/deftest-kb no-member-of-the-registry-opens-a-proof-search
  ;; The invariant the whole closed-world half of the engine rests on.  `exceptWhen`,
  ;; `unknown`, `thereExists` and the aggregates all evaluate their argument through the
  ;; registry, and they are reached from inside a relabel loop — so a registry member
  ;; that backchained would put an unbounded proof search there.  `ask`'s cost being a
  ;; property of the goal rather than of the rule graph is the same fact.
  ;;
  ;; Stated as the `:search` tier being unoccupied, which is what `cost-tiers` says and
  ;; what makes `:max-cost :compute` and `:max-cost :search` select the same provers.
  (let [p (tu/tmp-pred) a (tu/tmp-ind) b (tu/tmp-ind)
        goal (list p a '?y)]
    (v/assert kb (list p a b) 'FamContext)
    (testing "no shipped prover claims the search tier"
      (is (= #{:lookup :compute}
             (set (map #(provers/cost % kb goal 'FamContext) (provers/registry kb))))
          "a :search member would be backward chaining inside every closed-world read"))
    (testing "so the two upper ceilings cannot narrow the registry differently"
      (is (= (provers/cost-capped-provers kb goal 'FamContext :compute)
             (provers/cost-capped-provers kb goal 'FamContext :search)
             (provers/registry kb))))
    (testing "while :lookup does narrow it"
      (is (< (count (provers/cost-capped-provers kb goal 'FamContext :lookup))
             (count (provers/registry kb)))))))

(tu/deftest-kb rule-planning-costs-antecedents-by-the-registry-and-memoizes-it
  ;; perf-review #10, and the seam under it (`provers/registry-est-override`).
  ;;
  ;; A chainer whose **leaf is the registry** must cost its antecedents by the registry:
  ;; a conjunct a cached closure answers costs the closure, not the handful of stored
  ;; edges the trie can count.  Level 7 is that chainer, so it is what this drives; a
  ;; `prove`, whose leaf is the stored facts, correctly consults nothing here because for
  ;; that leaf the index model is the right one.
  (let [p1 (tu/tmp-pred) p2 (tu/tmp-pred) p3 (tu/tmp-pred) p4 (tu/tmp-pred) q (tu/tmp-pred)
        a (tu/tmp-ind) b (tu/tmp-ind) c (tu/tmp-ind) d (tu/tmp-ind) e (tu/tmp-ind)]
    ;; backward, so the conclusion is not stored and a chainer has to expand the rule —
    ;; four reorderable antecedents, none recursive, so the planner has a real choice
    (v/assert-rule kb [(list p1 '?a '?b) (list p2 '?b '?c) (list p3 '?c '?d) (list p4 '?d '?e)]
                   (list q '?a '?e) 'FamContext {:direction :backward})
    (v/assert kb (list p1 a b) 'FamContext)
    (v/assert kb (list p2 b c) 'FamContext)
    (v/assert kb (list p3 c d) 'FamContext)
    (v/assert kb (list p4 d e) 'FamContext)
    (let [goal  (list q a '?e)
          count-est (fn [f]
                      (let [calls (atom 0), orig provers/est-goal]
                        (with-redefs [provers/est-goal
                                      (fn [& args] (swap! calls inc) (apply orig args))]
                          (let [r (f)] [@calls r]))))
          [n7 answer] (count-est (fn [] (set (map (comp (fn [m] (get m '?e)) :bindings)
                                                  (v/lookup kb 7 goal 'FamContext)))))
          [np _]      (count-est #(v/prove kb goal 'FamContext))]
      (testing "the plan does not change the answer"
        (is (= #{e} answer)))
      (testing "the registry is consulted for the antecedents at all"
        (is (pos? n7) "nothing costed the antecedents by the registry"))
      (testing "est-goal is estimated once per distinct antecedent goal, not per pick"
        ;; With the memo the planner evaluates each goal once (<= 4); un-memoized it
        ;; re-estimates every remaining literal on every pick — 4 + 3 + 2 + 1 = 10 — so
        ;; this bound is the guard.
        (is (<= n7 4) (str "est-goal called " n7 " times for four antecedents")))
      (testing "and a chainer whose leaf is the stored facts consults it not at all"
        (is (zero? np))))))

;; ---- different: the unique-name assumption ------------------------------

(defn- different-prover-applicable? [kb goal context]
  (provers/applicable? (provers/->DifferentProver) kb goal context))

(defn- plan-provers [kb goal context]
  (set (map :prover (v/query-plan kb goal context))))

(tu/deftest-kb different-holds-of-unmerged-symbols
  (tu/with-terms [Tom Bob Ann]
    (testing "two symbols nobody merged denote two things"
      (is (v/ask? kb (list 'different Tom Bob) 'UniverseContext))
      (is (v/ask? kb (list 'different Bob Ann) 'UniverseContext)))
    (testing "three arguments are pairwise distinct"
      (is (v/ask? kb (list 'different Tom Bob Ann) 'UniverseContext))
      (is (not (v/ask? kb (list 'different Tom Bob Tom) 'UniverseContext))
          "a repeat anywhere in the list breaks pairwise distinctness"))
    (testing "a term is never different from itself"
      (is (not (v/ask? kb (list 'different Tom Tom) 'UniverseContext))))
    (testing "the prover is the sole complete method — nothing else may be unioned in"
      (let [p (first (filter #(= "DifferentProver" (:prover %))
                             (v/query-plan kb (list 'different Tom Bob) 'UniverseContext)))]
        (is (some? p))
        (is (= 100 (:completeness p)))))))

(tu/deftest-kb different-with-a-free-argument-is-refused-not-answered
  ;; "no answers" and "refused" are different claims, and only the second is correct:
  ;; (different ?x Y) asks for every term in the KB outside Y's class.  So assert on
  ;; applicability, not on the (also empty) result set.
  (tu/with-terms [Tom Bob]
    (testing "ground goals are claimed"
      (is (different-prover-applicable? kb (list 'different Tom Bob) 'UniverseContext))
      (is (contains? (plan-provers kb (list 'different Tom Bob) 'UniverseContext)
                     "DifferentProver")))
    (testing "an unbound argument is refused outright"
      (doseq [goal [(list 'different '?x Bob)
                    (list 'different Tom '?y)
                    (list 'different '?x '?y)
                    (list 'different Tom Bob '?z)]]
        (is (not (different-prover-applicable? kb goal 'UniverseContext))
            (str "must be inapplicable: " goal))
        (is (not (contains? (plan-provers kb goal 'UniverseContext) "DifferentProver"))
            (str "must not appear in the plan: " goal))))
    (testing "a nested unbound argument is refused too"
      (is (not (different-prover-applicable?
                kb (list 'different (list 'fatherOf '?x) Bob) 'UniverseContext))))
    (testing "fewer than two arguments says nothing to be distinct about"
      (is (not (different-prover-applicable? kb (list 'different Tom) 'UniverseContext))))))

(tu/deftest-kb different-reads-the-equality-closure
  (tu/with-terms [Obama BarackObama Bush]
    (v/assert kb (list 'sameAs Obama BarackObama) 'UniverseContext)
    (is (tax/same-class? (:taxonomy kb) Obama BarackObama)
        "asserting `sameAs` merges — everything below reads the class it built")
    (testing "merged terms are not different"
      (is (not (v/ask? kb (list 'different Obama BarackObama) 'UniverseContext)))
      (is (v/ask? kb (list 'different Obama Bush) 'UniverseContext)
          "a third, unmerged term still is")
      (is (not (v/ask? kb (list 'different Obama BarackObama Bush) 'UniverseContext))
          "one merged pair breaks pairwise distinctness for the whole list"))))

;; Congruence, which is the half a flat class lookup cannot answer: the closure is keyed by
;; symbol, so a compound argument is never a key in it.  Normalizing the whole argument in
;; one lookup leaves `(F 5 Kilogram)` unchanged and reports it different from `(F 5 Kg)`
;; with the merge believed; `res/representative-term` descends instead, and these pin the
;; difference in both directions so neither can regress unnoticed.

(tu/deftest-kb different-descends-into-compound-arguments
  (tu/with-terms [Kilogram Kg Gram QuantityFn]
    (v/assert kb (list 'sameAs Kilogram Kg) 'UniverseContext)
    (let [q (fn [u] (list QuantityFn 5 u))]
      (is (not (v/ask? kb (list 'different (q Kilogram) (q Kg)) 'UniverseContext))
          "same functor, same number, merged units — one term under congruence")
      (is (v/ask? kb (list 'different (q Kilogram) (q Gram)) 'UniverseContext)
          "an unmerged unit still tells the two compounds apart")
      (is (v/ask? kb (list 'different (q Kilogram) (list QuantityFn 6 Kg)) 'UniverseContext)
          "merging the unit does not merge compounds differing elsewhere")
      (testing "and it descends past the first level"
        (is (not (v/ask? kb (list 'different (q (q Kilogram)) (q (q Kg))) 'UniverseContext))
            "the merged symbol sits two compounds deep and still normalizes")))))

(tu/deftest-kb query-plan-exposes-estimates
  (let [dog (tu/tmp-type) animal (tu/tmp-type) likes (tu/tmp-pred)]
    (v/assert kb (list 'genl dog animal) 'UniverseContext)
    (testing "a genl goal is served by a single complete prover (transitivity)"
      (let [plan (v/query-plan kb (list 'genl dog '?y) 'UniverseContext)
            trans (first (filter #(= "TransitivityProver" (:prover %)) plan))]
        (is (= 100 (:completeness trans)))
        (is (number? (:est-bindings trans)))
        (is (contains? (set provers/cost-tiers) (:cost trans)))))
    (testing "a plain predicate goal has no complete prover (facts + rules combine)"
      (let [plan (v/query-plan kb (list likes '?a '?b) 'UniverseContext)]
        (is (every? #(< (:completeness %) 100) plan))))))

(tu/deftest-kb custom-prover-is-pluggable
  ;; a trivial prover that always yields one empty solution for goals it likes
  (defrecord AlwaysProver []
    provers/Prover
    (applicable?  [_ _ goal _] (= 'magic (first goal)))
    (est-bindings [_ _ _ _] 1)
    (cost         [_ _ _ _] :lookup)
    (completeness [_ _ _ _] 100)
    (solve        [_ _ _ _] [{}]))
  (v/add-prover kb (->AlwaysProver))
  (is (v/ask? kb '(magic Anything) 'UniverseContext)))

;; ---- declared-transitive predicates --------------------------------------
;; `(transitive P)` is *metadata*, not a cached relation: nothing about P lives in the
;; taxonomy's adjacency, so there is no depth potential to maintain and no arrival
;; order to be sensitive to.  The whole cost is at query time, and a closed goal asks
;; about one pair rather than for the closure.

(tu/deftest-kb declared-transitive-closure-and-its-limits
  (let [larger (tu/tmp-pred "largerThan")
        r      (fn [i] (tu/fresh-term :individual (str "R" i)))
        rs     (mapv r (range 6))]
    (v/assert kb (list 'transitive larger) 'UniverseContext)
    (doseq [i (range 1 6)]
      (v/assert kb (list larger (rs (dec i)) (rs i)) 'UniverseContext))
    (testing "a chain is answered end to end, and not backwards"
      (is (v/ask? kb (list larger (rs 0) (rs 5)) 'UniverseContext))
      (is (not (v/ask? kb (list larger (rs 5) (rs 0)) 'UniverseContext))))
    (testing "an open argument still enumerates the whole reach"
      (is (= (set (rest rs))
             (set (map #(get % '?y) (v/ask kb (list larger (rs 0) '?y) 'UniverseContext))))))
    (testing "nothing of it is stored in the taxonomy — only the declaration is"
      (is (v/has-prop? kb :transitive larger))
      (is (empty? (filter #(= larger %) (v/types kb)))))))

(tu/deftest-kb a-closed-transitive-goal-stops-at-its-answer
  ;; The membership question is not the closure question.  Building the closure to
  ;; answer it charges a near pair for the whole extent; `reaches?` stops at the
  ;; sighting, so a two-hop answer never visits the far end of the chain.
  (let [larger (tu/tmp-pred "largerThan")
        r      (fn [i] (tu/fresh-term :individual (str "R" i)))
        n      60
        rs     (mapv r (range (inc n)))
        seen   (atom 0)]
    (v/assert kb (list 'transitive larger) 'UniverseContext)
    (v/with-deferred-settle kb
      (doseq [i (range 1 (inc n))]
        (v/assert kb (list larger (rs (dec i)) (rs i)) 'UniverseContext {:chain? false})))
    ;; count how far the walk goes by watching how many distinct nodes it asks about
    (with-redefs [vaelii.impl.resolution/matches-visible
                  (let [orig vaelii.impl.resolution/matches-visible]
                    (fn [& args] (swap! seen inc) (apply orig args)))]
      (reset! seen 0)
      (is (v/ask? kb (list larger (rs 0) (rs 2)) 'UniverseContext))
      (let [near @seen]
        (reset! seen 0)
        (is (v/ask? kb (list larger (rs 0) (rs n)) 'UniverseContext))
        (is (< near @seen)
            "a near answer must cost less than the far one — it did not stop early")))))

(tu/deftest-kb a-cyclic-transitive-predicate-terminates
  ;; `wff` refuses a `genl` / `genlContext` cycle; nothing refuses one here, because a
  ;; user-declared transitive relation means what the user said — and a cycle in a
  ;; transitive relation really does entail reflexivity around the loop.  What must
  ;; hold is that the walk terminates rather than spinning.
  (let [nx (tu/tmp-pred "nextTo")
        [a b c] [(tu/tmp-ind) (tu/tmp-ind) (tu/tmp-ind)]]
    (v/assert kb (list 'transitive nx) 'UniverseContext)
    (v/assert kb (list nx a b) 'UniverseContext)
    (v/assert kb (list nx b c) 'UniverseContext)
    (v/assert kb (list nx c a) 'UniverseContext)
    (is (v/ask? kb (list nx a c) 'UniverseContext))
    (is (v/ask? kb (list nx a a) 'UniverseContext) "reflexive around the loop, and it returns")
    (is (= #{a b c} (set (map #(get % '?y) (v/ask kb (list nx a '?y) 'UniverseContext)))))))

(tu/deftest-kb the-walk-reads-hops-through-the-subsumption-fan
  ;; Each hop of the walk is a `matches-visible` read, so a hop written on a
  ;; *sub-predicate* of the transitive one is on the graph: the closure composes with
  ;; the predicate hierarchy rather than reading one functor's postings.  The edge
  ;; arrives late and is retracted again, because the failures worth catching here are
  ;; a fan that reads every predicate and a closure cache that outlives the edge —
  ;; both invisible to a test that asserts everything first and asks once.
  (tu/with-terms [largerThan muchLargerThan A B C]
    (v/with-deferred-settle kb
      (v/assert kb (list 'transitive largerThan) 'UniverseContext)
      (v/assert kb (list muchLargerThan A B) 'UniverseContext)
      (v/assert kb (list largerThan B C) 'UniverseContext))
    (is (not (v/ask? kb (list largerThan A C) 'UniverseContext))
        "without the edge the sub-predicate's fact is not a hop, and the chain is broken")
    (v/assert kb (list 'genl muchLargerThan largerThan) 'UniverseContext)
    (is (v/ask? kb (list largerThan A C) 'UniverseContext)
        "the late edge puts the first hop on the graph")
    (is (not (v/ask? kb (list largerThan C A) 'UniverseContext)) "and not backwards")
    (is (= #{B C} (set (map #(get % '?y)
                            (v/ask kb (list largerThan A '?y) 'UniverseContext))))
        "the open goal enumerates through the fan too")
    (is (not (v/ask? kb (list muchLargerThan A C) 'UniverseContext))
        "transitivity stays with the predicate that declared it")
    (v/retract! kb (v/handle-of kb (list 'genl muchLargerThan largerThan)
                                'UniverseContext))
    (is (not (v/ask? kb (list largerThan A C) 'UniverseContext))
        "and retracting the edge breaks the chain again")))

(tu/deftest-kb a-partner-spelled-edge-of-a-sub-predicate-is-an-edge-of-the-super
  ;; (inverse P' Q) with (genl P' P): a stored (Q y x) is (P' x y), and a P' tuple is a
  ;; P tuple by subsumption, however it is spelled — so the partner spelling answers the
  ;; super-predicate's one-hop goal and is a hop of its walk, like every other spelling
  ;; of the same edge.
  (tu/with-terms [before strictlyBefore laterThan A B C]
    (v/with-deferred-settle kb
      (v/assert kb (list 'transitive before) 'UniverseContext)
      (v/assert kb (list 'genl strictlyBefore before) 'UniverseContext)
      (v/assert kb (list 'inverse strictlyBefore laterThan) 'UniverseContext)
      (v/assert kb (list before A B) 'UniverseContext)
      (v/assert kb (list laterThan C B) 'UniverseContext))
    (is (v/ask? kb (list strictlyBefore B C) 'UniverseContext)
        "the sub-predicate reads its own partner")
    (is (v/ask? kb (list before B C) 'UniverseContext)
        "and so does the super-predicate: the same tuple under the wider name")
    (is (v/ask? kb (list before A C) 'UniverseContext)
        "so the chain crosses the partner-spelled hop")
    (is (not (v/ask? kb (list before C A) 'UniverseContext)) "and not backwards")
    (is (= #{B C} (set (map #(get % '?y)
                            (v/ask kb (list before A '?y) 'UniverseContext))))
        "the open walk enumerates across it")))

(tu/deftest-kb a-sub-predicates-partner-composes-only-where-it-is-declared
  ;; The composed read rests on the inverse declaration like the fan rests on the genl
  ;; edge: a partner declared where the asker cannot see it contributes no spelling.
  (tu/with-terms [before2 strictlyBefore2 laterThan2 A B C AContext BContext]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genlContext AContext 'UniverseContext) 'UniverseContext)
      (v/assert kb (list 'genlContext BContext 'UniverseContext) 'UniverseContext)
      (v/assert kb (list 'transitive before2) 'UniverseContext)
      (v/assert kb (list 'genl strictlyBefore2 before2) 'UniverseContext)
      (v/assert kb (list 'inverse strictlyBefore2 laterThan2) AContext)
      (v/assert kb (list before2 A B) 'UniverseContext)
      (v/assert kb (list laterThan2 C B) 'UniverseContext))
    (is (v/ask? kb (list before2 A C) AContext)
        "the declaring context composes the chain")
    (is (not (v/ask? kb (list before2 A C) BContext))
        "a sibling that cannot see the declaration gets no partner spelling")))

(tu/deftest-kb the-transitive-licence-is-read-from-the-asking-context-by-the-prover
  ;; `applicable?` reads `(transitive p)` from the vantage — the prover's own half of
  ;; the licence scoping `inherit_test` pins for preservation.  A fresh KB, because
  ;; CoreContext decontextualizes `transitive` and would lift the declaration where
  ;; every context sees it.
  (tu/with-terms [reaches X Y Z AContext BContext]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genlContext AContext 'UniverseContext) 'UniverseContext)
      (v/assert kb (list 'genlContext BContext 'UniverseContext) 'UniverseContext)
      (v/assert kb (list 'transitive reaches) AContext)
      (v/assert kb (list reaches X Y) 'UniverseContext)
      (v/assert kb (list reaches Y Z) 'UniverseContext))
    (is (v/ask? kb (list reaches X Z) AContext) "the declaring context composes the chain")
    (is (not (v/ask? kb (list reaches X Z) BContext))
        "a sibling holding both hops and no licence closes nothing")
    (is (not (v/ask? kb (list reaches X Z) 'UniverseContext))
        "and neither does the root, which cannot see down to the licence")))

(tu/deftest-kb a-partner-hop-is-read-from-the-asking-context
  ;; The other scoping channel of the partner probe: the declaration was visible
  ;; everywhere, and the partner *fact* is not.
  (tu/with-terms [before after A B C AContext BContext]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genlContext AContext 'UniverseContext) 'UniverseContext)
      (v/assert kb (list 'genlContext BContext 'UniverseContext) 'UniverseContext)
      (v/assert kb (list 'transitive before) 'UniverseContext)
      (v/assert kb (list 'inverse before after) 'UniverseContext)
      (v/assert kb (list before A B) 'UniverseContext)
      (v/assert kb (list after C B) AContext))
    (is (v/ask? kb (list before A C) AContext) "A sees the partner-spelled hop")
    (is (not (v/ask? kb (list before A C) BContext))
        "the hop lives where B cannot see it")
    (is (not (v/ask? kb (list before A C) 'UniverseContext)))))

(tu/deftest-kb the-partner-probe-fans-over-the-partners-sub-predicates
  ;; The partner probe goes through `matches-visible`, so a hop stored under a
  ;; *sub-predicate of the partner* is the same edge again: `(immediatelyAfter C B)`
  ;; is an `after` fact by subsumption, and an `after` fact is a `before` edge.
  (tu/with-terms [before after immediatelyAfter A B C]
    (v/with-deferred-settle kb
      (v/assert kb (list 'transitive before) 'UniverseContext)
      (v/assert kb (list 'inverse before after) 'UniverseContext)
      (v/assert kb (list 'genl immediatelyAfter after) 'UniverseContext)
      (v/assert kb (list before A B) 'UniverseContext)
      (v/assert kb (list immediatelyAfter C B) 'UniverseContext))
    (is (v/ask? kb (list before A C) 'UniverseContext))
    (is (not (v/ask? kb (list before C A) 'UniverseContext)) "and not backwards")
    (is (= #{B C} (set (map #(get % '?y)
                            (v/ask kb (list before A '?y) 'UniverseContext)))))))

(tu/deftest-kb a-cycle-closed-on-the-partner-spelling-is-found
  ;; The `(P ?x ?x)` arm seeds and steps through the partner probes too, so a cycle
  ;; whose return edge is spelled on the partner — or on the mirror — is a cycle.
  (testing "the return edge on the declared partner"
    (tu/with-terms [follows precedes N0 N1]
      (v/with-deferred-settle kb
        (v/assert kb (list 'transitive follows) 'UniverseContext)
        (v/assert kb (list 'inverse follows precedes) 'UniverseContext)
        (v/assert kb (list follows N0 N1) 'UniverseContext)
        (v/assert kb (list precedes N0 N1) 'UniverseContext))
      (is (= #{N0 N1}
             (set (map #(get % '?x) (v/ask kb (list follows '?x '?x) 'UniverseContext)))))))
  (testing "every edge of a symmetric transitive predicate is on a two-cycle"
    (tu/with-terms [linkedTo M0 M1]
      (v/with-deferred-settle kb
        (v/assert kb (list 'transitive linkedTo) 'UniverseContext)
        (v/assert kb (list 'symmetric linkedTo) 'UniverseContext)
        (v/assert kb (list linkedTo M0 M1) 'UniverseContext))
      (is (= #{M0 M1}
             (set (map #(get % '?x) (v/ask kb (list linkedTo '?x '?x) 'UniverseContext)))))))
  (testing "a cycle only one context can close answers only there"
    (tu/with-terms [routesTo K0 K1 AContext BContext]
      (v/with-deferred-settle kb
        (v/assert kb (list 'genlContext AContext 'UniverseContext) 'UniverseContext)
        (v/assert kb (list 'genlContext BContext 'UniverseContext) 'UniverseContext)
        (v/assert kb (list 'transitive routesTo) 'UniverseContext)
        (v/assert kb (list routesTo K0 K1) 'UniverseContext)
        (v/assert kb (list routesTo K1 K0) AContext))
      (is (= #{K0 K1}
             (set (map #(get % '?x) (v/ask kb (list routesTo '?x '?x) AContext)))))
      (is (empty? (v/ask kb (list routesTo '?x '?x) BContext))))))

(tu/deftest-kb the-open-extent-includes-partner-spelled-pairs
  ;; A wholly-open transitive goal answers from the extent, and the extent speaks both
  ;; spellings: a pair recorded only on the partner is in it, and the derived
  ;; transitive pair is not — the walk contributes nothing with both ends open.
  (tu/with-terms [before after A B C]
    (v/with-deferred-settle kb
      (v/assert kb (list 'transitive before) 'UniverseContext)
      (v/assert kb (list 'inverse before after) 'UniverseContext)
      (v/assert kb (list before A B) 'UniverseContext)
      (v/assert kb (list after C B) 'UniverseContext))
    (is (= #{[A B] [B C]}
           (set (map (juxt #(get % '?x) #(get % '?y))
                     (v/ask kb (list before '?x '?y) 'UniverseContext))))
        "the stored extent in both spellings, and no derived pair")))

(tu/deftest-kb a-defeated-edge-is-not-answered-from-the-held-set-by-a-closed-goal
  ;; The closed arm consults the closure cache an open ask filled; a mid-chain defeat
  ;; retires the entry through the change clock, and the fallthrough walk refuses the
  ;; disbelieved hop.  The one sequence where a clock bug answers a ground pair from a
  ;; dead closure.
  (tu/with-terms [feeds A B C]
    (v/with-deferred-settle kb
      (v/assert kb (list 'transitive feeds) 'UniverseContext)
      (v/assert kb (list feeds A B) 'UniverseContext)
      (v/assert kb (list feeds B C) 'UniverseContext))
    (is (= #{B C} (set (map #(get % '?y) (v/ask kb (list feeds A '?y) 'UniverseContext))))
        "the open ask holds the closure")
    (v/assert kb (list 'not (list feeds B C)) 'UniverseContext {:strength :monotonic})
    (is (not (v/ask? kb (list feeds A C) 'UniverseContext))
        "the defeated hop is not answered from the held set")
    (is (= #{B} (set (map #(get % '?y) (v/ask kb (list feeds A '?y) 'UniverseContext)))))
    (v/retract! kb (v/handle-of kb (list 'not (list feeds B C)) 'UniverseContext))
    (is (v/ask? kb (list feeds A C) 'UniverseContext)
        "and the revived hop closes the chain again")))

(tu/deftest-kb the-walk-travels-only-hops-the-asker-can-see
  ;; And each hop is read *from the asking context*: a middle hop stored where the
  ;; asker cannot see it is a break in the chain, not an edge of it.  The licence has
  ;; the same scoping (`inherit_test`); this pins the hops themselves.
  (tu/with-terms [reachesTo A B C AContext BContext]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genlContext AContext 'UniverseContext) 'UniverseContext)
      (v/assert kb (list 'genlContext BContext 'UniverseContext) 'UniverseContext)
      (v/assert kb (list 'transitive reachesTo) 'UniverseContext)
      (v/assert kb (list reachesTo A B) 'UniverseContext)
      (v/assert kb (list reachesTo B C) AContext))
    (is (v/ask? kb (list reachesTo A C) AContext) "A sees both hops")
    (is (not (v/ask? kb (list reachesTo A C) BContext))
        "the middle hop lives where B cannot see it")
    (is (not (v/ask? kb (list reachesTo A C) 'UniverseContext))
        "visibility reads upward only, so the root does not see A's hop either")
    (is (v/ask? kb (list reachesTo A B) BContext) "the visible half still answers")))

;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.backward-test
  "The recur-based backward chainer (v/prove), focusing on inference that relies
  on transitive types (genl) and context visibility (genlCx)."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.plan :as plan]
            [vaelii.impl.resolution :as res]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(tu/deftest-kb prove-facts-and-rules
  (let [parentOf (tu/tmp-pred) grandparentOf (tu/tmp-pred)
        tom (tu/tmp-ind) bob (tu/tmp-ind) ann (tu/tmp-ind) zed (tu/tmp-ind)]
    (v/assert-rule kb [(list parentOf '?x '?y) (list parentOf '?y '?z)] (list grandparentOf '?x '?z) 'CxFam)
    (v/assert kb (list parentOf tom bob) 'CxFam)
    (v/assert kb (list parentOf bob ann) 'CxFam)
    (testing "prove a direct fact"
      (is (v/provable? kb (list parentOf tom bob) 'CxFam))
      (is (not (v/provable? kb (list parentOf tom zed) 'CxFam))))
    (testing "prove via a rule, reading out the bindings"
      (let [sols (v/prove kb (list grandparentOf tom '?who) 'CxFam)]
        (is (= #{ann} (set (map #(get % '?who) sols))))))))

(tu/deftest-kb prove-uses-type-transitivity
  (let [dog (tu/tmp-type) animal (tu/tmp-type) rock (tu/tmp-type)
        breathes (tu/tmp-pred) muffet (tu/tmp-ind) boulder (tu/tmp-ind)]
    (v/assert kb (list 'genl dog animal) 'CxUniverse)
    (v/assert-rule kb [(list animal '?x)] (list breathes '?x) 'CxUniverse)
    (v/assert kb (list dog muffet) 'CxUniverse)
    (v/assert kb (list rock boulder) 'CxUniverse)          ; not an animal
    (testing "a rule about animals is provable for a dog (subtype), not a rock"
      (is (v/provable? kb (list breathes muffet) 'CxUniverse))
      (is (not (v/provable? kb (list breathes boulder) 'CxUniverse))))))

(tu/deftest-kb prove-is-context-aware
  (let [parentOf (tu/tmp-pred) tom (tu/tmp-ind) bob (tu/tmp-ind) ann (tu/tmp-ind)]
    (v/assert kb (list 'genlCx 'CxBio 'CxUniverse) 'CxUniverse)
    (v/assert kb (list parentOf tom bob) 'CxUniverse)      ; general fact
    (v/assert kb (list parentOf bob ann) 'CxBio)           ; specific fact
    (testing "a specific context sees general facts (genlCx up-closure)"
      (is (v/provable? kb (list parentOf tom bob) 'CxBio))
      (is (v/provable? kb (list parentOf bob ann) 'CxBio)))
    (testing "a general context does not see specific facts"
      (is (v/provable? kb (list parentOf tom bob) 'CxUniverse))
      (is (not (v/provable? kb (list parentOf bob ann) 'CxUniverse))))))

(tu/deftest-kb prove-terminates-on-recursive-rule
  (let [parentOf (tu/tmp-pred) ancestorOf (tu/tmp-pred)
        aa (tu/tmp-ind) bb (tu/tmp-ind) cc (tu/tmp-ind) dd (tu/tmp-ind)]
    (v/assert-rule kb [(list parentOf '?x '?y)] (list ancestorOf '?x '?y) 'CxUniverse)                   ; base
    (v/assert-rule kb [(list parentOf '?x '?y) (list ancestorOf '?y '?z)] (list ancestorOf '?x '?z) 'CxUniverse) ; right-recursive
    (v/assert kb (list parentOf aa bb) 'CxUniverse)
    (v/assert kb (list parentOf bb cc) 'CxUniverse)
    (v/assert kb (list parentOf cc dd) 'CxUniverse)
    (testing "transitive closure via a recursive rule, and it terminates"
      (is (= #{bb cc dd}
             (set (map #(get % '?who) (v/prove kb (list ancestorOf aa '?who) 'CxUniverse))))))
    (testing "the lazy chainer terminates on the same rule set, fully realized —
              `backward` needs a recursion guard of its own, or running past the
              fact solutions diverges where `prove` terminates"
      (is (= #{bb cc dd}
             (set (map #(get % '?who)
                       (doall (v/prove kb (list ancestorOf aa '?who) 'CxUniverse)))))))))

;; ---- conjunctive goals ---------------------------------------------------
;; `prove` takes either one sentence or a *vector* of them.  A vector is a
;; conjunction: bindings thread across the conjuncts, so a shared variable joins.

(tu/deftest-kb prove-a-conjunction-joins-on-a-shared-variable
  (tu/with-terms [parentOf dog cat Tom Bob Ann CxJoin]
    (v/assert kb (list parentOf Tom Bob) CxJoin)
    (v/assert kb (list parentOf Tom Ann) CxJoin)
    (v/assert kb (list dog Bob) CxJoin)
    (v/assert kb (list cat Ann) CxJoin)
    (testing "?y must satisfy both conjuncts — only the child that is a dog"
      (is (= #{Bob}
             (set (map #(get % '?y)
                       (v/prove kb [(list parentOf Tom '?y) (list dog '?y)] CxJoin))))))
    (testing "the join is symmetric in conjunct order (no reordering, same answer)"
      (is (= #{Bob}
             (set (map #(get % '?y)
                       (v/prove kb [(list dog '?y) (list parentOf Tom '?y)] CxJoin))))))
    (testing "every conjunct's variables are bound in each solution"
      (let [sols (v/prove kb [(list parentOf '?x '?y) (list cat '?y)] CxJoin)]
        (is (= [{'?x Tom '?y Ann}] (map #(select-keys % '[?x ?y]) sols)))))
    (testing "a conjunction with no joint solution proves nothing"
      (is (empty? (v/prove kb [(list parentOf Tom '?y) (list dog '?y) (list cat '?y)] CxJoin)))
      (is (not (v/provable? kb [(list parentOf Tom '?y) (list cat '?y) (list dog '?y)] CxJoin))))
    (testing "each conjunct alone, and the pair that does share a binding"
      (is (v/provable? kb [(list parentOf Tom '?y)] CxJoin))
      (is (v/provable? kb [(list cat '?y)] CxJoin))
      (is (v/provable? kb [(list parentOf Tom '?y) (list cat '?y)] CxJoin)))
    (testing "an empty conjunction is trivially proved"
      (is (v/provable? kb [] CxJoin)))))

(tu/deftest-kb a-repeated-goal-key-across-conjuncts-answers-in-both
  ;; the per-path loop guard is scoped to the expansion subtree: a later conjunct
  ;; repeating an earlier conjunct's goal-key is a *sibling* of the expanded goal, not
  ;; a descendant, so it gets its own rule expansion — the cross product, never the
  ;; empty answer while each conjunct answers alone.  Two children of one parent, so
  ;; both conjuncts answer only through the rules and share one goal-key.
  (tu/with-terms [parentOf ancestorOf Tom Bob Cal CxGuard]
    (v/assert-rule kb [(list parentOf '?x '?y)] (list ancestorOf '?x '?y) CxGuard)
    (v/assert-rule kb [(list parentOf '?x '?y) (list ancestorOf '?y '?z)]
                   (list ancestorOf '?x '?z) CxGuard)
    (v/assert kb (list parentOf Tom Bob) CxGuard)
    (v/assert kb (list parentOf Tom Cal) CxGuard)
    (testing "each conjunct alone answers twice, so the pair is a 4-row cross product"
      (is (= #{Bob Cal}
             (set (map #(get % '?y) (v/prove kb (list ancestorOf Tom '?y) CxGuard)))))
      (is (= #{[Bob Bob] [Bob Cal] [Cal Bob] [Cal Cal]}
             (set (map (juxt #(get % '?y) #(get % '?z))
                       (v/prove kb [(list ancestorOf Tom '?y) (list ancestorOf Tom '?z)]
                                CxGuard))))))
    (testing "provable? agrees with prove on the repeated-key conjunction"
      (is (v/provable? kb [(list ancestorOf Tom '?y) (list ancestorOf Tom '?z)]
                       CxGuard)))
    (testing "the planner does not change the answer set"
      (is (= #{[Bob Bob] [Bob Cal] [Cal Bob] [Cal Cal]}
             (binding [plan/*enabled* false]
               (set (map (juxt #(get % '?y) #(get % '?z))
                         (v/prove kb [(list ancestorOf Tom '?y) (list ancestorOf Tom '?z)]
                                  CxGuard)))))))))

(tu/deftest-kb prove-a-single-goal-is-unchanged-by-the-conjunction-form
  (tu/with-terms [parentOf grandparentOf Tom Bob Ann CxJoin]
    (v/assert-rule kb [(list parentOf '?x '?y) (list parentOf '?y '?z)]
                   (list grandparentOf '?x '?z) CxJoin)
    (v/assert kb (list parentOf Tom Bob) CxJoin)
    (v/assert kb (list parentOf Bob Ann) CxJoin)
    (testing "a bare sentence and the one-element vector agree, facts and rules alike"
      (is (= (v/prove kb (list parentOf Tom Bob) CxJoin)
             (v/prove kb [(list parentOf Tom Bob)] CxJoin)))
      (is (= (v/prove kb (list grandparentOf Tom '?who) CxJoin)
             (v/prove kb [(list grandparentOf Tom '?who)] CxJoin)))
      (is (v/provable? kb (list grandparentOf Tom Ann) CxJoin))
      (is (v/provable? kb [(list grandparentOf Tom Ann)] CxJoin)))
    (testing "a conjunct may itself be answered by backchaining through a rule"
      ;; Tom -> Bob -> Ann: whoever parents Bob is a grandparent, of Ann
      (is (= #{Ann}
             (set (map #(get % '?z)
                       (v/prove kb [(list parentOf '?x Bob) (list grandparentOf '?x '?z)]
                                CxJoin)))))
      (is (v/provable? kb [(list parentOf Tom '?y) (list parentOf '?y Ann)] CxJoin)))))

(tu/deftest-kb prove-answers-once-per-derivation-and-not-once-per-answer
  ;; `prove`'s documented contract, and the one most likely to be "fixed" by a reader
  ;; who meets it and reads a repeat as a bug: a goal reachable two ways comes back
  ;; twice, with the two maps equal.  Deduping here would be a Breaking change and
  ;; would take `abduce`'s explanations with it — an explanation is a derivation, so a
  ;; reader that collapsed equal maps could not tell two of them apart.
  ;;
  ;; **That multiplicity is the DFS's, and it is the one thing the two engines do not
  ;; share.**  The node engine keys a `seen` set on the bindings, so two derivations of
  ;; one answer are one answer and the proof it hands back is the first found
  ;; (`inference/step!`, which says so).  What both engines promise is the answer
  ;; *set* — that is what `*query-engine*` claims, what `inference_parity_test`
  ;; compares, and all of what `docs/inference.md` means by the two agreeing.  So the
  ;; counting halves stand aside under `VAELII_QUERY_ENGINE`, in the shape
  ;; `query_test.clj` uses, and the set halves run under both engines.
  (tu/with-terms [viaA viaB shared Someone CxDeriv]
    (v/assert-rule kb [(list viaA '?x)] (list shared '?x) CxDeriv)
    (v/assert-rule kb [(list viaB '?x)] (list shared '?x) CxDeriv)
    (v/assert kb (list viaA Someone) CxDeriv)
    (v/assert kb (list viaB Someone) CxDeriv)
    (let [proofs (v/prove kb (list shared '?x) CxDeriv)
          ;; the DFS answers one solution per derivation, the node engine one per answer —
          ;; the sweep runs the second, so the multiplicity asserted is the engine's own
          per-derivation? (nil? (tu/query-engine-override))]
      (testing "every derivation is its own solution under the DFS, and equal maps repeat"
        (is (= per-derivation? (< 1 (count proofs)))
            "two rules concluding one goal are two derivations, or one answer")
        (is (apply = proofs)
            "and the maps are equal — a repeat carries no binding the others lack"))
      (testing "the answer set is one binding, however many derivations reached it"
        (is (= 1 (count (distinct proofs)))
            "so `distinct` is what recovers the answer set"))
      (testing "the readers that project to the goal's variables answer each binding once"
        (is (= 1 (count (v/ask kb (list shared '?x) CxDeriv))))
        (is (= 1 (count (v/query kb (list shared '?x) CxDeriv {:max-depth 3})))))
      (testing "a ground goal binds nothing, so the repeats are empty maps"
        (let [ground (v/prove kb (list shared Someone) CxDeriv)]
          (is (= per-derivation? (< 1 (count ground))))
          (is (every? empty? ground))
          (is (v/provable? kb (list shared Someone) CxDeriv)
              "provable? asks whether there is one, not how many"))))))

;; ---- the term-growth ceiling ---------------------------------------------
;; The per-path goal key keeps its ground arguments, so a rule that wraps a function
;; around a head variable asks a fresh goal per expansion and the key never repeats.
;; The second half of the loop guard is a ceiling on how far a subgoal's terms may
;; nest past the query's (`res/default-max-term-growth`): relative, so recursion that
;; shrinks a term is never touched.

(defn- within-ms
  "`f`'s value, or `::timeout` when it has not returned after `ms` — the shape a
  termination claim is tested in, since a hang has no value to assert on."
  [ms f]
  (let [fut (future (f))
        r   (deref fut ms ::timeout)]
    (when (= r ::timeout) (future-cancel fut))
    r))

(deftest term-depth-reads-argument-nesting
  (is (= 0 (res/term-depth '(p A))))
  (is (= 0 (res/term-depth '(p ?x ?y))))
  (is (= 1 (res/term-depth '(p (SuccFn A)))))
  (is (= 2 (res/term-depth '(p A (SuccFn (SuccFn ?x))))))
  (is (= 0 (res/term-depth 'A))))

(tu/deftest-kb a-term-growing-rule-terminates-at-the-ceiling
  (tu/with-terms [p SuccFn A CxGrow]
    ;; (implies (p (SuccFn ?x)) (p ?x)): every expansion wraps one more SuccFn
    (v/assert-rule kb [(list p (list SuccFn '?x))] (list p '?x) CxGrow)
    (testing "with nothing stored, the search cuts at the ceiling and answers no"
      (is (false? (within-ms 20000 #(v/provable? kb (list p A) CxGrow)))))
    (testing "a fact within the allowance is still reached through the rule"
      (v/assert kb (list p (list SuccFn (list SuccFn A))) CxGrow)
      (is (true? (within-ms 20000 #(v/provable? kb (list p A) CxGrow)))))
    (testing "the level stack's unbounded level terminates on the same rule"
      (is (not= ::timeout
                (within-ms 20000 #(doall (v/explain-levels kb (list p A) CxGrow))))))))

(tu/deftest-kb a-term-shrinking-recursion-is-not-bounded
  (tu/with-terms [q SuccFn Zero CxShrink]
    ;; (implies (q ?x) (q (SuccFn ?x))): a goal about a numeral counts it down
    (v/assert-rule kb [(list q '?x)] (list q (list SuccFn '?x)) CxShrink)
    (v/assert kb (list q Zero) CxShrink)
    (let [deep (nth (iterate #(list SuccFn %) Zero) 12)]
      (testing "twelve levels of descent, past the growth allowance, still answer —
                the ceiling is relative to the query and a shrinking goal never meets it"
        (is (true? (within-ms 20000 #(v/provable? kb (list q deep) CxShrink))))))))

(tu/deftest-kb a-deep-stored-term-a-conjunct-bound-raises-the-ceiling-for-the-next
  (tu/with-terms [deepOf baseOf holdsIt okFor FooFn Zed Aye Other CxDeep]
    ;; ten levels of nesting is past the allowance, and no rule grew any of it: the
    ;; term is stored that deep, and the second conjunct only inherits it
    (let [deep (nth (iterate #(list FooFn %) Zed) 10)]
      (v/assert kb (list deepOf Aye deep) CxDeep)
      (v/assert kb (list baseOf deep) CxDeep)
      ;; a handful of stored `holdsIt` facts, so the planner leads with `deepOf` — the
      ;; order that binds the deep term before the conjunct that has to inherit it
      (doseq [i (range 6)] (v/assert kb (list holdsIt (symbol (str Other i))) CxDeep))
      (v/assert-rule kb [(list baseOf '?y)] (list holdsIt '?y) CxDeep {:direction :backward})
      (v/assert-rule kb [(list deepOf '?x '?y) (list holdsIt '?y)] (list okFor '?x) CxDeep
                     {:direction :backward})
      (testing "the derivation is found: only a rule's own nesting meets the ceiling"
        (is (= [{}] (v/prove kb (list okFor Aye) CxDeep))))
      (testing "the node engine agrees, as it must within its depth bound"
        (is (= [{}] (v/query kb (list okFor Aye) CxDeep {:max-depth 4}))))
      (testing "reordering the conjunction changes cost, never the answer set"
        (binding [plan/*enabled* false]
          (is (= #{{'?y deep}}
                 (set (v/prove kb [(list deepOf Aye '?y) (list holdsIt '?y)] CxDeep))
                 (set (v/prove kb [(list holdsIt '?y) (list deepOf Aye '?y)] CxDeep)))))))))

;; ---- a variable-functor goal expands rules ---------------------------------
;; `(?p Tom ?y)` names no consequent bucket, and any rule may conclude it once `?p`
;; binds — so the candidate rules are every rule, read off the antecedent roster, and
;; `subsuming-unify` binds the functor per rule.  Fact matching answers the open functor
;; through the argument roots; rule expansion has to answer it the same way, in both
;; engines, or the open question silently sees the stored half of the KB.

(tu/deftest-kb a-variable-functor-goal-expands-a-concrete-consequent-rule
  (tu/with-terms [parentOf ancestorOf Tom Bob CxOpen]
    (v/assert kb (list parentOf Tom Bob) CxOpen)
    (let [rh    (v/assert kb (list 'set/backwardRule
                                   (list 'implies (list parentOf '?x '?y)
                                         (list ancestorOf '?x '?y)))
                          CxOpen)
          preds (fn [sols] (set (map #(get % '?p) sols)))]
      (testing "the concrete goal answers through the rule"
        (is (= #{{'?y Bob}} (set (v/query kb (list ancestorOf Tom '?y) CxOpen {:max-depth 2})))))
      (testing "the node engine binds the open functor to the rule's consequent predicate"
        (is (= #{parentOf ancestorOf}
               (preds (v/query kb (list '?p Tom '?y) CxOpen {:max-depth 2})))))
      (testing "and so does the DFS"
        (is (= #{parentOf ancestorOf}
               (preds (v/prove kb (list '?p Tom '?y) CxOpen)))))
      (testing "a ground open-functor goal finds the derived predicate too"
        (is (= #{parentOf ancestorOf}
               (preds (v/prove kb (list '?p Tom Bob) CxOpen)))))
      (testing "the candidate set for an open functor is every rule, read off the roster"
        (is (contains? (set (res/concluding-rule-handles kb '?p CxOpen)) rh))))))

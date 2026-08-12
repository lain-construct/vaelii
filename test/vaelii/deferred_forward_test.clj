;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.deferred-forward-test
  "Deferred (evaluable) antecedents in a **forward** rule.

  A deferred literal — `lessThan` / `greaterThan` / `evaluate` / `different` — is
  computed by the prover registry, not stored and looked up.  Forward chaining used
  to join every antecedent through the index, so a deferred one matched nothing and
  killed the join: a rule carrying a comparison derived nothing at all, and did it
  silently, since an empty join looks exactly like a rule with nothing to fire on.
  Backward chaining never had the bug — it discharges antecedents through
  `provers/solve-goal` — so the two chainers disagreed about the same rule, which is
  the thing they may never do.

  What is pinned here:

    * a comparison **tests** — the rule fires for the pairs that satisfy it and no
      others, in one direction only;
    * `evaluate` **binds** — it extends the join with a value the consequent can use;
    * a computed literal contributes **no handle** to the justification, so a firing
      is supported by exactly the facts that bound its variables (plus the rule), and
      retracting any one of them withdraws the conclusion;
    * an input that is not bound by the time the join reaches it **throws**, rather
      than reporting a comparison that was never run as one that failed."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.rules :as vr]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- fwd [antes conseq]
  (list 'set/forwardRule (vr/rule-sentence antes conseq)))

(defn- sentences [kb pred]
  (set (map :sentence (v/sentexes-with-functor kb pred {:believed? true}))))

(defn- handle-of [kb pred sentence]
  (:id (first (filter #(= sentence (:sentence %)) (v/sentexes-with-functor kb pred)))))

;; ---- a comparison tests --------------------------------------------------

(tu/deftest-kb a-forward-rule-with-a-comparison-fires-only-for-the-satisfying-pairs
  (tu/with-terms [ageOf youngerThan Ann Bob Cid]
    (doseq [[who n] [[Ann 10] [Bob 20] [Cid 30]]]
      (v/assert kb (list ageOf who n) 'CxNaturalWorld {:chain? false}))
    (v/assert kb (fwd [(list ageOf '?x '?a) (list ageOf '?y '?b) (list 'lessThan '?a '?b)]
                      (list youngerThan '?x '?y))
              'CxNaturalWorld)
    (let [derived (sentences kb youngerThan)]
      (testing "every strictly-increasing pair is derived"
        (is (= #{(list youngerThan Ann Bob)
                 (list youngerThan Ann Cid)
                 (list youngerThan Bob Cid)}
               derived)))
      (testing "the comparison holds one way, so the mirror is never derived"
        (is (not (contains? derived (list youngerThan Bob Ann)))))
      (testing "and it is strict, so nothing is younger than itself"
        (is (not (contains? derived (list youngerThan Ann Ann))))))))

(tu/deftest-kb a-comparison-that-holds-of-nothing-derives-nothing
  ;; The other half of the previous test: an empty result must mean the comparison
  ;; *failed*, not that it was never run.  Equal ages satisfy no strict `lessThan`.
  (tu/with-terms [ageOf youngerThan Ann Bob]
    (doseq [who [Ann Bob]]
      (v/assert kb (list ageOf who 10) 'CxNaturalWorld {:chain? false}))
    (v/assert kb (fwd [(list ageOf '?x '?a) (list ageOf '?y '?b) (list 'lessThan '?a '?b)]
                      (list youngerThan '?x '?y))
              'CxNaturalWorld)
    (is (empty? (sentences kb youngerThan)))))

;; ---- evaluate binds ------------------------------------------------------

(tu/deftest-kb evaluate-binds-a-fresh-variable-the-consequent-uses
  (tu/with-terms [ageOf nextAge Ann Bob]
    (v/assert kb (list ageOf Ann 10) 'CxNaturalWorld {:chain? false})
    (v/assert kb (list ageOf Bob 41) 'CxNaturalWorld {:chain? false})
    (v/assert kb (fwd [(list ageOf '?x '?a) (list 'evaluate '?next (list '+ '?a 1))]
                      (list nextAge '?x '?next))
              'CxNaturalWorld)
    (testing "the computed value reaches the conclusion"
      (is (= #{(list nextAge Ann 11) (list nextAge Bob 42)}
             (sentences kb nextAge))))))

;; ---- what a computed literal contributes to the justification ------------

(tu/deftest-kb a-computed-literal-contributes-no-handle
  (tu/with-terms [ageOf youngerThan Ann Bob]
    (let [h1 (v/assert kb (list ageOf Ann 10) 'CxNaturalWorld {:chain? false})
          h2 (v/assert kb (list ageOf Bob 20) 'CxNaturalWorld {:chain? false})
          rh (v/assert kb (fwd [(list ageOf '?x '?a) (list ageOf '?y '?b) (list 'lessThan '?a '?b)]
                               (list youngerThan '?x '?y))
                       'CxNaturalWorld)
          ch (handle-of kb youngerThan (list youngerThan Ann Bob))]
      (is (some? ch))
      (testing "the two facts and the rule support it — the comparison names nothing"
        (is (= [#{h1 h2 rh}]
               (mapv (comp set :antecedents) (v/supporting-justifications kb ch))))))))

(tu/deftest-kb a-firing-with-only-computed-antecedents-is-supported-by-the-rule-alone
  ;; The degenerate case the placeholder question is really about: there is no fact to
  ;; name, so the justification names the rule and nothing else.
  (tu/with-terms [theSum]
    (let [rh (v/assert kb (fwd [(list 'evaluate '?s (list '+ 1 2))] (list theSum '?s))
                       'CxNaturalWorld)
          ch (handle-of kb theSum (list theSum 3))]
      (is (some? ch))
      (is (= [[rh]] (mapv :antecedents (v/supporting-justifications kb ch)))))))

;; ---- retraction ----------------------------------------------------------

(tu/deftest-kb retracting-a-contributing-fact-withdraws-the-computed-conclusion
  ;; This is what a bogus placeholder handle would break.  The comparison is still
  ;; *true* — 10 is still less than 20 — so the conclusion may only survive on the
  ;; strength of the facts that bound its variables.
  (tu/with-terms [ageOf youngerThan Ann Bob]
    (let [h1 (v/assert kb (list ageOf Ann 10) 'CxNaturalWorld {:chain? false})
          _  (v/assert kb (list ageOf Bob 20) 'CxNaturalWorld {:chain? false})
          _  (v/assert kb (fwd [(list ageOf '?x '?a) (list ageOf '?y '?b) (list 'lessThan '?a '?b)]
                               (list youngerThan '?x '?y))
                       'CxNaturalWorld)
          ch (handle-of kb youngerThan (list youngerThan Ann Bob))]
      (is (v/in? kb ch))
      (v/retract! kb h1)
      (testing "the conclusion goes with the fact that bound the comparison's left side"
        (is (empty? (sentences kb youngerThan)))
        (is (not (v/in? kb ch)))))))

;; ---- the ordering invariant ----------------------------------------------

(tu/deftest-kb a-deferred-antecedent-whose-input-nothing-binds-fails-loudly
  ;; `?b` appears only inside the comparison, so no antecedent can ever bind it.
  ;; Canonical order puts the comparison last and it still arrives unbound — the one
  ;; case where the ordering guarantee cannot save the join.  Answering it with an
  ;; empty result would report an unrunnable rule as a rule that merely did not fire.
  (tu/with-terms [ageOf tooOld Ann]
    (v/assert kb (list ageOf Ann 10) 'CxNaturalWorld {:chain? false})
    (let [e (try (v/assert kb (fwd [(list ageOf '?x '?a) (list 'lessThan '?a '?b)]
                                   (list tooOld '?x))
                           'CxNaturalWorld)
                 nil
                 (catch clojure.lang.ExceptionInfo ex ex))]
      (is (some? e) "an unbound comparison input throws rather than joining to nothing")
      (is (re-find #"unbound" (ex-message e)))
      (is (seq (:unbound (ex-data e)))))))

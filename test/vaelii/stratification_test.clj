;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.stratification-test
  "Stratification: a rule set with a **cycle through negation** is refused at assert
  time, as a well-formedness check over the rule dependency graph beside the `genl`
  cycle check.  See the Stratification section of
  [docs/exceptions.md](../../docs/exceptions.md).

  `exceptWhen` is negation as failure, so if one rule's exception depends on what
  another rule concludes and vice versa, the program admits zero or several stable
  models and which one you land in depends on arrival order — exactly what
  `docs/nmtms.md` forbids.  The two things this namespace has to pin are therefore
  symmetrical: every cycle crossing a negative edge is caught (including one that
  only closes through a genl subtype), and **no purely positive cycle is** —
  ordinary recursion is a supported feature, not a violation.

  House rules as everywhere: gensym'd temporaries via `tu/with-terms`, engine
  vocabulary (`genl`, `set/defaultRule`, `exceptWhen`) literal, and the neutral
  fixture asserts the KB is restored."
  (:require [clojure.string :as str]
            [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.rules :as vr]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- except-rule
  "The shape docs/exceptions.md writes: an exception query wrapping a defeasible rule."
  [exception antes conseq]
  (list 'exceptWhen exception (list 'set/defaultRule (vr/rule-sentence antes conseq))))

(defn- refusal
  "Assert, and return the `ex-data` of the refusal — nil if the assert went through.
  Reading the data rather than catching bare `ExceptionInfo` is what distinguishes a
  stratification refusal from a range-restriction or naming one, which would pass a
  `thrown?` test for the wrong reason."
  [kb sentence context]
  (try (v/assert kb sentence context) nil
       (catch clojure.lang.ExceptionInfo e (ex-data e))))

(defn- cycle-text [data] (str/join " " (:cycle data)))

;; ---- cycles through negation are refused ---------------------------------

(tu/deftest-kb a-two-rule-cycle-through-negation-is-refused
  ;; R1 excepts on what R2 concludes; R2 excepts on what R1 concludes.  Neither rule
  ;; is objectionable alone — it is the second one that closes the cycle, and the
  ;; second one is what has to be refused.
  (tu/with-terms [base p q CxCyc]
    (is (v/assert kb (except-rule (list q '?x) [(list base '?x)] (list p '?x)) CxCyc)
        "the first rule is fine: nothing concludes its exception's predicate yet")
    (let [data (refusal kb (except-rule (list p '?x) [(list base '?x)] (list q '?x))
                        CxCyc)]
      (testing "the rule closing the cycle is refused, and says so"
        (is (= :not-stratified (:type data))))
      (testing "the refusal names the cycle"
        (is (seq (:cycle data)))
        (is (str/includes? (cycle-text data) (str p)))
        (is (str/includes? (cycle-text data) (str q)))))))

(tu/deftest-kb a-three-rule-cycle-through-negation-is-refused
  ;; One negative edge is enough, however long the positive stretch that closes it:
  ;;   R1 excepts-on r -> R3 concludes r, depends on q -> R2 concludes q, depends on
  ;;   p -> R1 concludes p.
  (tu/with-terms [base p q r CxCyc]
    (is (v/assert kb (except-rule (list r '?x) [(list base '?x)] (list p '?x)) CxCyc))
    (is (v/assert kb (vr/rule-sentence [(list p '?x)] (list q '?x)) CxCyc))
    (let [data (refusal kb (vr/rule-sentence [(list q '?x)] (list r '?x)) CxCyc)]
      (testing "the third rule closes a cycle with one negative edge in it"
        (is (= :not-stratified (:type data)))))))

(tu/deftest-kb an-exception-that-mentions-the-rules-own-conclusion-is-refused
  ;; The degenerate case: a rule whose exception mentions the predicate it concludes
  ;; is a one-rule cycle.  It is refused on its *first* assert, which is only
  ;; possible because the graph counts the rule being added — it is not stored yet.
  (tu/with-terms [base p CxSelf]
    (let [data (refusal kb (except-rule (list p '?x) [(list base '?x)] (list p '?x))
                        CxSelf)]
      (is (= :not-stratified (:type data))))))

;; ---- the genl closure is part of the graph -------------------------------
;; DECISION: predicate dependence is not literal.  An exception on `flightless` is
;; satisfied by a stored `(penguin Opus)` when `(genl penguin flightless)`, so the
;; graph follows the spec closure the way the re-check trigger does.

(tu/deftest-kb a-cycle-that-closes-only-through-a-genl-subtype-is-refused
  (tu/with-terms [base flightless penguin p CxBird]
    (v/assert kb (list 'genl penguin flightless) CxBird)
    (is (v/assert kb (except-rule (list flightless '?x) [(list base '?x)] (list p '?x))
                  CxBird))
    (let [data (refusal kb (vr/rule-sentence [(list p '?x)] (list penguin '?x)) CxBird)]
      (testing "concluding a *subtype* of the exception's predicate closes the cycle"
        (is (= :not-stratified (:type data)))))))

(tu/deftest-kb without-the-genl-edge-the-same-two-rules-are-stratified
  ;; The control for the test above: identical rules, no genl edge, and the cycle
  ;; does not exist — so the refusal there is attributable to the subtype and not to
  ;; the shape of the rules.
  (tu/with-terms [base flightless penguin p CxBird]
    (is (v/assert kb (except-rule (list flightless '?x) [(list base '?x)] (list p '?x))
                  CxBird))
    (is (v/assert kb (vr/rule-sentence [(list p '?x)] (list penguin '?x)) CxBird))))

;; ---- positive recursion is not a cycle through negation ------------------
;; DECISION: "A purely positive cycle is ordinary recursion, which the engine
;; supports and bounds by depth."  Each test here keeps an unrelated excepted rule in
;; the KB so the graph has a negative edge somewhere and the walk actually runs —
;; without it the check short-circuits and the test would pass vacuously.

(defn- unrelated-excepted-rule!
  "An excepted rule sharing no predicate with anything else, asserted only so the
  stratification walk is not skipped."
  [kb context]
  (tu/with-terms [other otherBase otherExc]
    (v/assert kb (except-rule (list otherExc '?x) [(list otherBase '?x)] (list other '?x))
              context)))

(tu/deftest-kb direct-positive-recursion-is-accepted
  (tu/with-terms [path link CxRec]
    (unrelated-excepted-rule! kb CxRec)
    (testing "a rule whose antecedent is its own consequent's predicate is recursion"
      (is (v/assert kb (vr/rule-sentence [(list path '?x '?y) (list link '?y '?z)]
                                         (list path '?x '?z))
                    CxRec)))))

(tu/deftest-kb mutual-positive-recursion-is-accepted
  (tu/with-terms [a b CxMut]
    (unrelated-excepted-rule! kb CxMut)
    (is (v/assert kb (vr/rule-sentence [(list a '?x)] (list b '?x)) CxMut))
    (testing "the rule closing the positive loop is accepted — it crosses no negation"
      (is (v/assert kb (vr/rule-sentence [(list b '?x)] (list a '?x)) CxMut)))))

(tu/deftest-kb a-recursive-rule-may-carry-an-exception-on-something-outside-the-loop
  ;; The negative edge exists and leads out of the cycle rather than around it, so
  ;; the program is stratified: the exception's predicate is concluded by no rule.
  (tu/with-terms [path link tooLong CxRec]
    (is (v/assert kb (except-rule (list tooLong '?x)
                                  [(list path '?x '?y) (list link '?y '?z)]
                                  (list path '?x '?z))
                  CxRec))))

;; ---- a refused rule stores nothing ---------------------------------------

(tu/deftest-kb a-refused-rule-leaves-no-partial-state
  ;; The check runs before anything is written, so there is nothing to unwind.  The
  ;; neutral fixture makes the same claim for the namespace as a whole; this pins it
  ;; to the refusal itself, where a half-stored rule would also leave a stale posting
  ;; in the rule and exception indexes.
  (tu/with-terms [base p q CxCyc]
    (v/assert kb (except-rule (list q '?x) [(list base '?x)] (list p '?x)) CxCyc)
    (let [before-sx (tu/sentex-ids kb)
          before-dd (tu/justification-ids kb)
          data      (refusal kb (except-rule (list p '?x) [(list base '?x)] (list q '?x))
                             CxCyc)]
      (is (= :not-stratified (:type data)))
      (is (= before-sx (tu/sentex-ids kb))    "no sentex was stored")
      (is (= before-dd (tu/justification-ids kb)) "no justification was stored")
      (testing "and the refused rule is not reachable as knowledge"
        ;; the whole `(exceptWhen ..)` was refused before the bare rule was stored, so
        ;; the rule concluding q is not there (the surviving first rule's *exception*
        ;; legitimately mentions q, so probe the refused rule's own form)
        (is (nil? (v/handle-of kb (vr/rule-sentence [(list base '?x)] (list q '?x))
                               CxCyc)))))))

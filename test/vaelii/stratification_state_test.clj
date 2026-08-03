;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.stratification-state-test
  "The **search state** of `wff/negation-cycle`, which is `[rule negative?]` and not
  the rule alone.

  `vaelii.stratification-test` covers the two ends of the check — cycles through
  negation are refused, purely positive recursion is not — but it keeps them in
  disjoint scenarios, so every rule in it is reachable exactly one way.  That leaves
  the state itself unpinned: collapsing `seen` to `(:id r)` passes that whole
  namespace, because a node there is never reached both positively and negatively.

  It is the *both* case that the pair-keyed state exists for.  A node reached with a
  negative edge behind it and the same node reached without one are genuinely
  different search states: only the negative one can close a bad cycle, so pruning
  the negative arrival because the positive arrival was seen first silently accepts
  an unstratified program.  The masking needs three rules — the hit is tested on a
  node's *successors*, so the wrongly-pruned node has to be one hop short of the
  cycle-closing edge, which no two-rule shape can arrange.

  The complement matters just as much: the extra state must not manufacture cycles
  that are not there.  So each refusal here has an acceptance beside it with the same
  topology minus the closing edge.

  House rules as everywhere: gensym'd temporaries via `tu/with-terms`, engine
  vocabulary (`exceptWhen`, `set/defaultRule`) literal, and the neutral fixture
  asserts the KB is restored."
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

;; ---- a node reached BOTH ways ------------------------------------------------
;;
;; Three rules, arranged so R2 is reachable from the start twice over:
;;
;;   R1 --depends-on q--> R2                       (positive, one hop)
;;   R1 --excepts-on r--> R3 --depends-on q--> R2  (negative, two hops)
;;   R2 --depends-on p--> R1                       (closes both)
;;
;; The positive arrival at R2 is found first and expands to `[R1 positive]`, which is
;; not a hit.  The cycle is only visible from `[R2 negative]`, one expansion later.
;; Keyed on the rule alone, R2 is already in `seen` when the negative arrival shows
;; up, that arrival is dropped, and the program is accepted.

(tu/deftest-kb a-node-reachable-positively-does-not-mask-the-negative-path-to-it
  ;; THE discriminating test for the `[rule negative?]` state.  Changing `seen` to key
  ;; on `(:id r)` — a plausible simplification, and one every other stratification test
  ;; survives — accepts this rule set instead of refusing it.
  (tu/with-terms [p q r MaskContext]
    (testing "the two positive rules are fine on their own — no exception exists yet"
      (is (v/assert kb (vr/rule-sentence [(list p '?x)] (list q '?x)) MaskContext))
      (is (v/assert kb (vr/rule-sentence [(list q '?x)] (list r '?x)) MaskContext)))
    (let [data (refusal kb (except-rule (list r '?x) [(list q '?x)] (list p '?x))
                        MaskContext)]
      (testing "the excepted rule closes a cycle whose only negative route to the
                closing edge runs through a node already reached positively"
        (is (= :not-stratified (:type data))))
      (testing "and the refusal names the cycle it found"
        (is (seq (:cycle data)))
        (is (str/includes? (cycle-text data) "excepts-on"))
        (is (str/includes? (cycle-text data) (str r)))))))

(tu/deftest-kb the-same-shape-without-the-closing-edge-is-accepted
  ;; The control: identical topology — R2 still reached both positively and negatively
  ;; — except R2 now depends on a predicate no rule concludes, so nothing returns to
  ;; the start.  The refusal above is therefore attributable to the cycle and not to
  ;; the search visiting a node twice, and the extra state is shown not to invent one.
  (tu/with-terms [p q r base OpenContext]
    (is (v/assert kb (vr/rule-sentence [(list base '?x)] (list q '?x)) OpenContext))
    (is (v/assert kb (vr/rule-sentence [(list q '?x)] (list r '?x)) OpenContext))
    (testing "the walk reaches q's rule twice and terminates with no cycle"
      (is (v/assert kb (except-rule (list r '?x) [(list q '?x)] (list p '?x))
                    OpenContext)))))

;; ---- positive recursion survives a negative edge pointing into it ------------
;;
;; `stratification-test/mutual-positive-recursion-is-accepted` pins a two-rule
;; positive cycle with no negative edge anywhere near it.  The case that exercises the
;; state is the same cycle *entered* negatively: every node in the loop is then
;; visited with `negative?` true, and the walk has to go all the way round it and stop
;; without claiming a cycle — the start is not in the loop, and `seen` is the only
;; thing that terminates the traversal.

(tu/deftest-kb an-exception-may-point-into-a-two-rule-positive-cycle
  ;; The "reject everything" guard.  A check that treated any negatively-reached node
  ;; on a cycle as a violation would refuse this, and ordinary mutual recursion would
  ;; become unwritable next to any excepted rule.
  (tu/with-terms [a b c base LoopContext]
    (is (v/assert kb (vr/rule-sentence [(list b '?x)] (list a '?x)) LoopContext))
    (is (v/assert kb (vr/rule-sentence [(list a '?x)] (list b '?x)) LoopContext)
        "a purely positive two-rule cycle: ordinary recursion")
    (testing "an exception on a predicate the cycle concludes is not a cycle through
              negation — the negative edge leads into the loop, never back to the rule"
      (is (v/assert kb (except-rule (list a '?x) [(list base '?x)] (list c '?x))
                    LoopContext)))))

(tu/deftest-kb a-positive-cycle-the-exception-can-reach-back-through-is-refused
  ;; The dual of the test above, and the reason it cannot simply be "cycles are fine":
  ;; the same positive loop, but now the excepted rule's own consequent feeds it, so
  ;; the negative edge does return.  Accepting this one would be the real bug.
  (tu/with-terms [a b c LoopContext]
    (is (v/assert kb (vr/rule-sentence [(list b '?x)] (list a '?x)) LoopContext))
    (is (v/assert kb (vr/rule-sentence [(list c '?x)] (list b '?x)) LoopContext))
    (let [data (refusal kb (except-rule (list a '?x) [(list b '?x)] (list c '?x))
                        LoopContext)]
      (is (= :not-stratified (:type data))))))

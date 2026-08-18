;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.rejoin-belief-test
  "A rule the KB does not believe does not fire — on the **re-join** paths too, not only
  the trigger path `generator_test`'s `a-disbelieved-rule-does-not-fire` pins.

  A qualitative fact or a moved preserved predicate re-joins its rules in full rather
  than at a trigger position (`chain/rejoin-qualitative`, `chain/rejoin-preserving`),
  because the arriving sentence need not unify with the antecedent it enabled.  Those
  rules come off the antecedent index, which posts on **storage**, so a rule whose
  support has been defeated is still a candidate there while the settle runs.  Fired
  anyway, its conclusion labels OUT (the rule handle is one of its justification's
  antecedents), so a read of *belief* cannot see the difference — but the firing's
  *unconditional* side effects land, and the sharpest is a `violations/report` entry
  filed against a rule the KB does not hold.

  **The oracle is the trigger path.**  `res/rule-believed?` is what `fire-rules-for`
  already asks before the trigger match fires, and in the exact scenario below the
  trigger path refuses the rule and files nothing (checked by hand while writing this:
  the same mint reached by a plain antecedent reports zero).  These pin that the two
  re-join paths refuse it identically, rather than the shortest join deciding whether a
  report is filed.

  The rule is minted by a generator and then **defeated** (not retracted): a defeated
  default's mint stays stored and indexed while it is OUT, which is the window the
  re-join reaches into; a *retracted* fill forgets the mint outright and never tests the
  gate.  The observable is a dropped-conclusion report (`v/violations`): the conclusion
  is given a declared arity it does not have, so a firing files an `:arity` entry."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.rules :as vr]
            [vaelii.impl.space :as space]
            [vaelii.impl.starter :as starter]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded starter/load-into))
(use-fixtures :each (tu/neutral))

(defn- stamped-rule
  "The one minted rule — a *derived* stored rule, not a premise, not a generator — in
  `ctx`, or nil.  Excluding premises is what keeps this off the marker `defaultRule` the
  generator fires on: that rule concludes a *fact*, so `generator-sentex?` is false of it,
  and it is an asserted premise that sorts ahead of the mint.  Grabbing it instead reads a
  believed premise after the defeat and mistakes it for a still-believed mint — the trap
  `mint_belief_test` exists to pin apart."
  [kb ctx]
  (->> (v/sentexes-in-context kb ctx)
       (filter :antecedent)
       (remove vr/generator-sentex?)
       (remove #(v/premise? kb (:id %)))
       first))

(defn- arity-reports-for
  "The `:arity` dropped-conclusion reports whose dropped sentence is on `pred`."
  [kb pred]
  (filter #(and (= :arity (:violation %))
                (= pred (some-> (:sentence %) first)))
          (v/violations kb)))

;; ---- the preserving re-join ---------------------------------------------

(tu/deftest-kb a-disbelieved-rule-is-not-fired-by-the-preserving-rejoin
  (tu/with-terms [pbigger pseen pmark trig dog cat pom CxRB]
    ;; `pbigger` is preserved along genl, so a rule on it re-joins in full when a genl
    ;; edge moves what it licenses — the preserving path, not the trigger index.  Its
    ;; conclusion `(pseen ?x)` is arity 1; declaring pseen arity 2 makes any firing of it
    ;; a dropped `:arity` report we can see.
    (v/assert kb (list 'transitiveInArg pbigger 1 'genl) CxRB)
    (v/assert kb (list 'transitiveInArg pbigger 2 'genl) CxRB)
    (v/assert kb (list 'arity pseen 2) CxRB)
    (v/assert kb (list 'implies (list pmark '?rel)
                       (list 'implies (list '?rel '?x '?y) (list pseen '?x)))
              CxRB)
    ;; pmark is a DEFAULT, so defeating it leaves the mint stored and indexed while OUT
    (v/assert kb (list 'set/defaultRule
                       (list 'implies (list 'and (list trig '?p)) (list pmark '?p)))
              CxRB)
    (v/assert kb (list trig pbigger) CxRB)
    (is (some? (stamped-rule kb CxRB)) "the rule was stamped")
    (testing "the mint's support is defeated, then a genl edge moves the preserved predicate"
      (v/assert kb (list 'not (list pmark pbigger)) CxRB {:strength :monotonic})
      ;; `(pbigger pom cat)` becomes entailed by preservation down the new edge — a tuple
      ;; no trigger index connects to the rule, reached only by the preserving re-join.
      (v/assert kb (list pbigger dog cat) CxRB)
      (v/assert kb (list 'genl pom dog) CxRB)
      (is (empty? (arity-reports-for kb pseen))
          "the preserving re-join refuses the rule the trigger path would refuse"))))

;; ---- the qualitative re-join --------------------------------------------

(defn- with-spatial
  "Register the RCC-8 prover, returning a teardown that removes it."
  [kb]
  (let [before @(:provers kb)]
    (v/add-prover kb (space/spatial-prover))
    (fn [] (reset! (:provers kb) before))))

(tu/deftest-kb a-disbelieved-rule-is-not-fired-by-the-qualitative-rejoin
  (tu/with-terms [qseen qmark trig ra rb rc CxRBQ]
    (let [undo (with-spatial kb)]
      (try
        (v/assert kb (list 'genlCx CxRBQ 'CxWell) 'CxUniverse {:strength :monotonic})
        (v/assert kb (list 'arity qseen 2) CxRBQ)
        ;; a generator that stamps out `(implies (partOfRegion ?x ?y) (qseen ?x))` — an
        ;; antecedent on a DERIVED spatial relation nothing stores, so the stamped rule
        ;; only ever fires through the qualitative re-join over the pairs that moved.
        (v/assert kb (list 'implies (list qmark '?rel)
                           (list 'implies (list '?rel '?x '?y) (list qseen '?x)))
                  CxRBQ)
        (v/assert kb (list 'set/defaultRule
                           (list 'implies (list 'and (list trig '?p)) (list qmark '?p)))
                  CxRBQ)
        (v/assert kb (list trig 'partOfRegion) CxRBQ)
        (is (some? (stamped-rule kb CxRBQ)) "the rule was stamped")
        (testing "the mint's support is defeated, then containment moves the calculus"
          (v/assert kb (list 'not (list qmark 'partOfRegion)) CxRBQ {:strength :monotonic})
          ;; entails `(partOfRegion ra rc)` and moves the calculus — the arriving `ntpp`
          ;; fact queues the re-join that finds the tuple no trigger index connects.
          (v/assert kb (list 'nonTangentialProperPart ra rb) CxRBQ {:strength :monotonic})
          (v/assert kb (list 'nonTangentialProperPart rb rc) CxRBQ {:strength :monotonic})
          (is (empty? (arity-reports-for kb qseen))
              "the qualitative re-join refuses the rule the trigger path would refuse"))
        (finally (undo))))))

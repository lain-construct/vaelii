;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.argpreserving-meta-test
  "The meta-predicates carry `transitiveInArg` / `transitiveInArgInverse` on their own
  argument positions, so the query surface answers the same generalizations `check`
  already walks internally.  Before this, a stored `(argIsa petMammal 1 mammal)` was
  the only thing `(ask (argIsa petMammal 1 animal))` could return — nothing — even
  though `(genl mammal animal)` holds and `check` would accept an animal there.  The
  fix is data, not engine: declaring the meta-predicates preserved along `genl` on
  themselves (position 3/5 up the type, position 1 down the predicate) closes #20.

  The KB here is CxCore alone, so what these tests read is the *shipped* declaration
  and not one they stated."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.core-context :as core-context]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh #(doto (tu/fresh) (core-context/load-into))))

(def ^:private C 'CxCore)

;; ---- argIsa, both directions --------------------------------------------

(tu/deftest-kb argIsa-answers-up-the-genl-chain-via-transitiveInArgInverse
  ;; position 3 is a TYPE: a stored constraint on mammal answers up to animal
  (tu/with-terms [petMammal mammal animal dog]
    (v/assert kb (list 'genl animal 'thing) C)
    (v/assert kb (list 'genl mammal animal) C)
    (v/assert kb (list 'genl dog mammal) C)
    (v/assert kb (list 'argIsa petMammal 1 mammal) C)
    (testing "the literally stored declaration is answerable, and it is stored"
      (is (v/ask? kb (list 'argIsa petMammal 1 mammal) C))
      (is (seq (v/sentexes-matching kb (list 'argIsa petMammal 1 mammal) '?ctx))))
    (testing "the supertype answers even though nobody stored it — the gap #20 names"
      (is (v/ask? kb (list 'argIsa petMammal 1 animal) C))
      (is (empty? (v/sentexes-matching kb (list 'argIsa petMammal 1 animal) '?ctx))
          "answered on demand, never materialized"))
    (testing "and the default context read (unscoped) finds it too"
      (is (v/ask? kb (list 'argIsa petMammal 1 animal))))
    (testing "but the constraint does not descend at position 3 — inverse is up only"
      (is (not (v/ask? kb (list 'argIsa petMammal 1 dog) C))))))

(tu/deftest-kb argIsa-inherits-down-the-predicate-via-transitiveInArg
  ;; position 1 is the PREDICATE: a constraint on a general predicate reaches its
  ;; genl-specializations, and not the other way
  (tu/with-terms [mySuper mySub myOver myType]
    (v/assert kb (list 'genl myType 'thing) C)
    (v/assert kb (list 'genl mySub mySuper) C)
    (v/assert kb (list 'genl mySuper myOver) C)
    (v/assert kb (list 'argIsa mySuper 1 myType) C)
    (testing "a specialization of the constrained predicate inherits the constraint"
      (is (v/ask? kb (list 'argIsa mySub 1 myType) C))
      (is (empty? (v/sentexes-matching kb (list 'argIsa mySub 1 myType) '?ctx))))
    (testing "but a generalization does not — transitiveInArg reaches down, not up"
      (is (not (v/ask? kb (list 'argIsa myOver 1 myType) C))))))

;; ---- argGenl, interArgIsa, arity: the same shape, smoke-tested ----------

(tu/deftest-kb argGenl-answers-up-the-genl-chain-at-position-3
  (tu/with-terms [typeRel mammal animal]
    (v/assert kb (list 'genl animal 'thing) C)
    (v/assert kb (list 'genl mammal animal) C)
    (v/assert kb (list 'argGenl typeRel 1 mammal) C)
    (testing "the stored subtype constraint answers up to the supertype"
      (is (v/ask? kb (list 'argGenl typeRel 1 animal) C))
      (is (empty? (v/sentexes-matching kb (list 'argGenl typeRel 1 animal) '?ctx))))))

(tu/deftest-kb interArgIsa-answers-up-both-type-positions
  ;; positions 3 and 5 are the two types; each is transitiveInArgInverse along genl
  (tu/with-terms [myRel carnivore predator meat food]
    (v/assert kb (list 'genl predator 'thing) C)
    (v/assert kb (list 'genl carnivore predator) C)
    (v/assert kb (list 'genl food 'thing) C)
    (v/assert kb (list 'genl meat food) C)
    (v/assert kb (list 'interArgIsa myRel 1 carnivore 2 meat) C)
    (testing "position 3 generalizes up its type"
      (is (v/ask? kb (list 'interArgIsa myRel 1 predator 2 meat) C)))
    (testing "position 5 generalizes up its type"
      (is (v/ask? kb (list 'interArgIsa myRel 1 carnivore 2 food) C)))
    (testing "neither is materialized"
      (is (empty? (v/sentexes-matching kb (list 'interArgIsa myRel 1 predator 2 meat) '?ctx))))))

(tu/deftest-kb arity-does-not-generalize-down-the-predicate
  ;; arity is deliberately NOT among the generalized meta-predicates.  Unlike a type
  ;; constraint, a sub-predicate may carry a signature of its own — a ternary
  ;; specialization of a binary — so its arity is not answered down `genl` as a fact,
  ;; and answering it would in any case need the forward `(arity ?p 2) ⊢
  ;; (binaryPredicate ?p)` cycle a backward prover cannot fire.  `check`'s
  ;; `inherited-arity` still holds a sub-predicate that declares NOTHING of its own to
  ;; its supers at assert time — a refusal, not an answerable `(arity sub n)`.
  (tu/with-terms [mySuper mySub]
    (v/assert kb (list 'genl mySub mySuper) C)
    (v/assert kb (list 'arity mySuper 2) C)
    (testing "the specialization does not inherit the arity as an answerable fact"
      (is (not (v/ask? kb (list 'arity mySub 2) C))))
    (testing "so the derive cycle concludes no predicate type for it either"
      (is (not (v/ask? kb (list 'binaryPredicate mySub) C))))))

;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.rewrite-test
  "The pure oriented-rewriting engine (`vaelii.impl.rewrite`): orientation by a
  reduction order, one-way matching, and normalization to a fixpoint.  No store, no
  belief — just term algebra, so these are ordinary unit tests with no KB."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.impl.rewrite :as rw]))

(deftest term-size-counts-leaves
  (is (= 1 (rw/term-size 'Tom)))
  (is (= 1 (rw/term-size '?x)))
  (is (= 2 (rw/term-size '(grandfatherOf ?x))))
  (is (= 3 (rw/term-size '(fatherOf (fatherOf ?x))))))

(deftest orient-picks-the-shrinking-direction
  (testing "the bigger side rewrites to the smaller"
    (is (= '[(fatherOf (fatherOf ?x)) (grandfatherOf ?x)]
           (rw/orient '(fatherOf (fatherOf ?x)) '(grandfatherOf ?x))))
    (is (= '[(fatherOf (fatherOf ?x)) (grandfatherOf ?x)]
           (rw/orient '(grandfatherOf ?x) '(fatherOf (fatherOf ?x))))
        "orientation is content-derived, independent of the written order"))
  (testing "an equal-weight pair is oriented by the symbol precedence, either way written"
    ;; g ≻_F f by name, so both spellings orient (g …) → (f …)
    (is (= '[(g ?x) (f ?x)] (rw/orient '(f ?x) '(g ?x))))
    (is (= '[(g ?x) (f ?x)] (rw/orient '(g ?x) '(f ?x))))
    (testing "and an equal-size nesting orients too, where size-only refused"
      (is (= '[(g (f ?x)) (f (g ?x))] (rw/orient '(f (g ?x)) '(g (f ?x)))))))
  (testing "a permutative equation cannot be oriented by any term order"
    (is (nil? (rw/orient '(rel ?x ?y) '(rel ?y ?x)))))
  (testing "the bigger side shrinks even when it repeats a variable"
    ;; (g ?x ?x) -> (f ?x) is a valid terminating rewrite; the reverse would grow
    (is (= '[(g ?x ?x) (f ?x)] (rw/orient '(f ?x) '(g ?x ?x)))))
  (testing "a bigger side carrying a variable the smaller lacks is refused"
    ;; (g ?x ?x) -> (f ?y) would introduce an unbound ?y
    (is (nil? (rw/orient '(f ?y) '(g ?x ?x))))))

(deftest match-is-one-way
  (testing "a ground subject binds the pattern's variables"
    (is (= '{?x Tom} (rw/match '(fatherOf (fatherOf ?x)) '(fatherOf (fatherOf Tom))))))
  (testing "a variable-bearing subject binds the pattern var to the subject term"
    (is (= '{?x ?y} (rw/match '(fatherOf (fatherOf ?x)) '(fatherOf (fatherOf ?y))))))
  (testing "a repeated pattern variable demands consistency"
    (is (= '{?x Tom} (rw/match '(rel ?x ?x) '(rel Tom Tom))))
    (is (nil? (rw/match '(rel ?x ?x) '(rel Tom Sue)))))
  (testing "arity / head mismatch does not match"
    (is (nil? (rw/match '(fatherOf ?x) '(motherOf Tom))))
    (is (nil? (rw/match '(fatherOf ?x) '(fatherOf Tom Extra))))))

(deftest normalize-reduces-to-the-normal-form
  (let [rules [{:lhs '(fatherOf (fatherOf ?x)) :rhs '(grandfatherOf ?x)}]]
    (testing "a term is rewritten to its normal form"
      (is (= '(grandfatherOf Tom) (rw/normalize rules '(fatherOf (fatherOf Tom))))))
    (testing "a nested application normalizes innermost-first, cascading"
      ;; fatherOf(fatherOf(fatherOf(fatherOf Tom)))) -> grandfatherOf(grandfatherOf Tom)
      (is (= '(grandfatherOf (grandfatherOf Tom))
             (rw/normalize rules '(fatherOf (fatherOf (fatherOf (fatherOf Tom))))))))
    (testing "an already-normal term is unchanged"
      (is (= '(grandfatherOf Tom) (rw/normalize rules '(grandfatherOf Tom)))))
    (testing "a variable-bearing term normalizes too"
      (is (= '(grandfatherOf ?y) (rw/normalize rules '(fatherOf (fatherOf ?y))))))))

(deftest normalize-sentence-protects-the-predication
  (let [rules [{:lhs '(fatherOf (fatherOf ?x)) :rhs '(grandfatherOf ?x)}]]
    (testing "each argument normalizes; the sentence functor is left alone"
      (is (= '(parentChain (grandfatherOf Tom))
             (rw/normalize-sentence rules '(parentChain (fatherOf (fatherOf Tom)))))))
    (testing "a bare predication matching the rule shape is NOT rewritten"
      ;; (fatherOf (fatherOf Tom)) as a top-level fact keeps its predicate
      (is (= '(fatherOf (fatherOf Tom))
             (rw/normalize-sentence rules '(fatherOf (fatherOf Tom))))))
    (testing "no rules is a no-op"
      (is (= '(parentChain (fatherOf (fatherOf Tom)))
             (rw/normalize-sentence [] '(parentChain (fatherOf (fatherOf Tom)))))))))

(deftest schematic-equation-detection
  (is (rw/schematic-equation? '(equals (fatherOf (fatherOf ?x)) (grandfatherOf ?x))))
  (testing "not schematic: ground compound (reifies to symbols), symbol merge, sameAs"
    (is (not (rw/schematic-equation? '(equals (FruitFn AppleA) (FruitFn AppleB)))))
    (is (not (rw/schematic-equation? '(equals Obama BarackObama))))
    (is (not (rw/schematic-equation? '(sameAs (fatherOf ?x) (dadOf ?x)))))))

(deftest rule-applies-tracks-contribution
  (let [rule {:lhs '(fatherOf (fatherOf ?x)) :rhs '(grandfatherOf ?x)}]
    (is (rw/rule-applies? rule '(parentChain (fatherOf (fatherOf Tom)))))
    (is (not (rw/rule-applies? rule '(parentChain (motherOf Tom)))))))

(deftest non-joining-pairs-surfaces-inter-rule-conflicts
  (let [r1 {:handle 1 :lhs '(f (f ?x)) :rhs '(g ?x)}
        r2 {:handle 2 :lhs '(f (f ?x)) :rhs '(h ?x)}   ; same LHS, different RHS → conflict
        p1 {:handle 3 :lhs '(p (p ?x)) :rhs '(q ?x)}]  ; disjoint predicates
    (testing "two rules disagreeing about a shared term are reported"
      (let [njs (rw/non-joining-pairs r2 [r1 r2])]
        (is (seq njs))
        (is (every? #(= 1 (:with %)) njs))
        (is (every? #(not= (:form-a %) (:form-b %)) njs))))
    (testing "disjoint rules overlap nowhere, so nothing is reported"
      (is (empty? (rw/non-joining-pairs p1 [r1 p1]))))
    (testing "a lone rule reports nothing — self-overlaps are excluded"
      (is (empty? (rw/non-joining-pairs r1 [r1]))))))

;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.wff-test
  "Well-formedness checking of genl, genlContext, disjoint, disjointMetatype, argIsa."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- ill-formed?
  "Did asserting this into the KB under test fail well-formedness?"
  [& args]
  (try (apply v/assert tu/*kb* args) false
       (catch clojure.lang.ExceptionInfo e
         (boolean (re-find #"not well-formed" (.getMessage e))))))

(tu/deftest-kb genl-well-formedness
  (let [dog (tu/tmp-type) animal (tu/tmp-type) mammal (tu/tmp-type)
        muffet (tu/tmp-ind) rover (tu/tmp-ind)]
    (testing "well-formed genl is accepted"
      (is (v/assert kb (list 'genl dog animal) 'UniverseContext)))
    (testing "genl relates types, not individuals"
      (is (ill-formed? (list 'genl muffet animal) 'UniverseContext))
      (is (ill-formed? (list 'genl dog rover) 'UniverseContext)))
    (testing "genl of a type with itself is ill-formed"
      (is (ill-formed? (list 'genl dog dog) 'UniverseContext)))
    (testing "a genl cycle is rejected"
      (v/assert kb (list 'genl mammal animal) 'UniverseContext)
      (is (ill-formed? (list 'genl animal mammal) 'UniverseContext)))))   ; would close mammal→animal→mammal

(tu/deftest-kb disjoint-well-formedness
  (let [dog (tu/tmp-type) cat (tu/tmp-type) mammal (tu/tmp-type) muffet (tu/tmp-ind)]
    (testing "well-formed disjoint is accepted"
      (is (v/assert kb (list 'disjoint dog cat) 'UniverseContext)))
    (testing "disjoint relates types, not individuals"
      (is (ill-formed? (list 'disjoint muffet cat) 'UniverseContext)))
    (testing "genl-related types can't be disjoint"
      (v/assert kb (list 'genl dog mammal) 'UniverseContext)
      (is (ill-formed? (list 'disjoint dog mammal) 'UniverseContext)))))

(tu/deftest-kb argIsa-and-genlContext-well-formedness
  (let [parentOf (tu/tmp-pred) animal (tu/tmp-type) muffet (tu/tmp-ind) a-ctx (tu/tmp-ctx)]
    (testing "argIsa needs a predicate, a positive integer, and a type"
      (is (v/assert kb (list 'argIsa parentOf 1 animal) 'UniverseContext))
      (is (ill-formed? (list 'argIsa parentOf 0 animal) 'UniverseContext))    ; position must be positive
      (is (ill-formed? (list 'argIsa parentOf 1 muffet) 'UniverseContext)))     ; type is an individual
    (testing "genlContext relates contexts"
      (is (v/assert kb (list 'genlContext a-ctx 'UniverseContext) 'UniverseContext))
      (is (ill-formed? (list 'genlContext animal 'UniverseContext) 'UniverseContext)))))  ; not a context

(tu/deftest-kb an-argument-constraint-may-be-about-a-function
  ;; A function has argument positions exactly as a predicate does — `(argIsa Milli 1
  ;; unit_of_measure)` says what the argument of a NAT `(Milli Meter)` must be, the same
  ;; kind of claim `resultIsa` makes about its result — and a function is spelled
  ;; CapitalCamelCase, which is also how an individual is spelled.  So the constrained
  ;; relation cannot be held to a spelling without refusing the whole vocabulary of
  ;; function argument types.
  (tu/with-terms [Milli a_unit]
    (v/assert kb (list 'genl a_unit 'thing) 'UniverseContext)
    (v/assert kb (list 'unreifiableFunction Milli) 'UniverseContext)
    (is (v/assert kb (list 'argIsa Milli 1 a_unit) 'UniverseContext))
    (testing "and both constraints may be about it, since they ask different questions"
      (is (v/assert kb (list 'argGenl Milli 1 a_unit) 'UniverseContext)))
    (testing "what is decidable from the sentence is still checked"
      (is (ill-formed? (list 'argIsa Milli 1 (tu/tmp-ind)) 'UniverseContext))   ; type is an individual
      (is (ill-formed? (list 'argIsa Milli 0 a_unit) 'UniverseContext)))))      ; position not positive

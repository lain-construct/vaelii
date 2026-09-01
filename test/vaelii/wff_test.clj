;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.wff-test
  "Well-formedness checking of genl, genlCx, disjoint, disjoint_metatype, arg."
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
      (is (v/assert kb (list 'genl dog animal) 'CxUniverse)))
    (testing "genl relates types, not individuals"
      (is (ill-formed? (list 'genl muffet animal) 'CxUniverse))
      (is (ill-formed? (list 'genl dog rover) 'CxUniverse)))
    (testing "genl of a type with itself is ill-formed"
      (is (ill-formed? (list 'genl dog dog) 'CxUniverse)))
    (testing "a genl cycle is rejected"
      (v/assert kb (list 'genl mammal animal) 'CxUniverse)
      (is (ill-formed? (list 'genl animal mammal) 'CxUniverse)))))   ; would close mammal→animal→mammal

(tu/deftest-kb disjoint-well-formedness
  (let [dog (tu/tmp-type) cat (tu/tmp-type) mammal (tu/tmp-type) muffet (tu/tmp-ind)]
    (testing "well-formed disjoint is accepted"
      (is (v/assert kb (list 'disjoint dog cat) 'CxUniverse)))
    (testing "disjoint relates types, not individuals"
      (is (ill-formed? (list 'disjoint muffet cat) 'CxUniverse)))
    (testing "genl-related types can't be disjoint"
      (v/assert kb (list 'genl dog mammal) 'CxUniverse)
      (is (ill-formed? (list 'disjoint dog mammal) 'CxUniverse)))))

(tu/deftest-kb arg-and-genlCx-well-formedness
  (let [parentOf (tu/tmp-pred) animal (tu/tmp-type) muffet (tu/tmp-ind) a-ctx (tu/tmp-ctx)]
    (testing "arg needs a predicate, a positive integer, and a type"
      (is (v/assert kb (list 'arg parentOf 1 animal) 'CxUniverse))
      (is (ill-formed? (list 'arg parentOf 0 animal) 'CxUniverse))    ; position must be positive
      (is (ill-formed? (list 'arg parentOf 1 muffet) 'CxUniverse)))     ; type is an individual
    (testing "genlCx relates contexts"
      (is (v/assert kb (list 'genlCx a-ctx 'CxUniverse) 'CxUniverse))
      (is (ill-formed? (list 'genlCx animal 'CxUniverse) 'CxUniverse)))))  ; not a context

(tu/deftest-kb an-argument-constraint-may-be-about-a-function
  ;; A function has argument positions exactly as a predicate does — `(arg Milli 1
  ;; unit_of_measure)` says what the argument of a NAT `(Milli Meter)` must be, the same
  ;; kind of claim `result` makes about its result — and a function is spelled
  ;; CapitalCamelCase, which is also how an individual is spelled.  So the constrained
  ;; relation cannot be held to a spelling without refusing the whole vocabulary of
  ;; function argument types.
  (tu/with-terms [Milli a_unit]
    (v/assert kb (list 'genl a_unit 'thing) 'CxUniverse)
    (v/assert kb (list 'unreifiable_function Milli) 'CxUniverse)
    (is (v/assert kb (list 'arg Milli 1 a_unit) 'CxUniverse))
    (testing "and both constraints may be about it, since they ask different questions"
      (is (v/assert kb (list 'genlArg Milli 1 a_unit) 'CxUniverse)))
    (testing "what is decidable from the sentence is still checked"
      (is (ill-formed? (list 'arg Milli 1 (tu/tmp-ind)) 'CxUniverse))   ; type is an individual
      (is (ill-formed? (list 'arg Milli 0 a_unit) 'CxUniverse)))))      ; position not positive

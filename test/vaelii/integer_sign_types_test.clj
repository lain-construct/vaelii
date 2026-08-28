;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.integer-sign-types-test
  "The four sign-refined integer types and their executable `defnIff` boundaries."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.starter :as starter]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded starter/load-into))
(use-fixtures :each (tu/neutral))

(def cases
  [['positive_integer     '(and (integer ?x) (greaterThan ?x 0))       1  0]
   ['negative_integer     '(and (integer ?x) (lessThan ?x 0))         -1  0]
   ['non_negative_integer '(and (integer ?x) (greaterThan ?x -1)) 0 -1]
   ['non_positive_integer '(and (integer ?x) (lessThan ?x 1))     0  1]])

(def positive-position-slots
  "Every core argument slot whose value is a one-based position."
  [['genlArg 2]
   ['arg 2]
   ['quotedArg 2]
   ['interArg 2]
   ['interArg 4]
   ['contextArgSubrelation 2]
   ['transitiveInArg 2]
   ['transitiveInArgInverse 2]])

(tu/deftest-kb sign-refined-integers-are-specializations-of-integer
  (doseq [[type] cases]
    (is (v/genl? kb type 'integer) (str type " specializes integer"))))

(tu/deftest-kb sign-refined-integers-state-their-boundaries-with-defniff
  (doseq [[type condition] cases]
    (is (some? (v/handle-of kb (list 'defnIff type condition) 'CxCore))
        (str type " has the expected executable definition"))))

(tu/deftest-kb sign-refined-integer-definitions-materialize-both-rules
  (doseq [[type condition] cases]
    (testing (str type)
      (let [[_ & conjuncts] condition]
        (doseq [conjunct conjuncts]
          (is (some? (v/handle-of kb (list 'implies (list type '?x) conjunct) 'CxCore))
              "membership entails every defining conjunct"))
        (is (some? (v/handle-of kb (list 'implies condition (list type '?x)) 'CxCore))
            "the complete condition entails membership")))))

(tu/deftest-kb sign-refined-integers-work-as-literal-argument-types
  (tu/with-terms [takesPositive takesNegative takesNonNegative takesNonPositive]
    (doseq [[pred type accepted rejected]
            [[takesPositive 'positive_integer 1 0]
             [takesNegative 'negative_integer -1 0]
             [takesNonNegative 'non_negative_integer 0 -1]
             [takesNonPositive 'non_positive_integer 0 1]]]
      (v/assert kb (list 'unaryPredicate pred) 'CxUniverse)
      (v/assert kb (list 'arg pred 1 type) 'CxUniverse)
      (is (integer? (v/assert kb (list pred accepted) 'CxUniverse))
          (str type " accepts a member literal"))
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list pred rejected) 'CxUniverse))
          (str type " rejects a literal outside its boundary")))))

(tu/deftest-kb core-integer-constraints-use-the-tightest-sign-type
  (doseq [[pred slot] positive-position-slots]
    (is (some? (v/handle-of kb (list 'arg pred slot 'positive_integer) 'CxCore))
        (str pred " argument " slot " is a one-based position")))
  (is (some? (v/handle-of kb '(arg arity 2 non_negative_integer) 'CxCore))
      "a predicate may have zero arguments, but never a negative arity"))

(tu/deftest-kb arity-is-non-negative-rather-than-positive
  (tu/with-terms [nullary impossible]
    (is (integer? (v/assert kb (list 'arity nullary 0) 'CxUniverse))
        "zero is a valid arity")
    (is (integer? (v/assert kb (list nullary) 'CxUniverse))
        "a declared nullary predicate can be asserted")
    (is (thrown? clojure.lang.ExceptionInfo
                 (v/assert kb (list 'arity impossible -1) 'CxUniverse))
        "a negative arity is impossible")))

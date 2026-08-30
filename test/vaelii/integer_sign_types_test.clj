;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.integer-sign-types-test
  "The four sign-refined integer types and their executable boundaries — defined by a
  `defnSufficient` + `defnNecessary` pair (not `defnIff`) so membership resolves by
  evaluation at query time, with the readable rule kept as an inert quoted
  JustificationRule fact (docs/defns.md)."
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

(tu/deftest-kb sign-refined-integers-state-their-boundaries-with-defns
  (doseq [[type condition] cases]
    (is (some? (v/handle-of kb (list 'defnSufficient type condition) 'CxCore))
        (str type " has the expected sufficient condition"))
    (is (some? (v/handle-of kb (list 'defnNecessary type condition) 'CxCore))
        (str type " has the expected necessary condition"))
    (is (nil? (v/handle-of kb (list 'defnIff type condition) 'CxCore))
        (str type " is no longer defined by a single defnIff (the rules never fired on a "
             "computed condition — it is a defnSufficient + defnNecessary pair now)"))))

(tu/deftest-kb sign-refined-integers-carry-their-readable-rule-as-a-quoted-justification
  (doseq [[type condition] cases]
    (is (some? (v/handle-of kb (list 'defnSufficientJustificationRule type
                                     (list 'Quote (list 'implies condition (list type '?x))))
                            'CxCore))
        (str type " cites the sufficient-direction rule for a positive proof"))
    (is (some? (v/handle-of kb (list 'defnNecessaryJustificationRule type
                                     (list 'Quote (list 'implies (list type '?x) condition)))
                            'CxCore))
        (str type " cites the necessary-direction rule for a negation"))))

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

;; ---- the mention reading -------------------------------------------------

;; Putting the sign types in the `genl` lattice under `integer` put them inside
;; `quotedArg`'s domain too, `checks/syntactic-type?` admitting any type below a
;; syntactic root.  Judged by EDN kind alone the comparison ran the wrong way round —
;; asking whether `integer` is below `positive_integer` — so the check refused every
;; integer literal written in such a position (#55).  A literal denotes itself, which is
;; why the two readings share `checks/literal-value-types` and agree here.

(tu/deftest-kb sign-refined-integers-work-as-quoted-argument-types
  (tu/with-terms [tagPositive tagNegative tagNonNegative tagNonPositive]
    (doseq [[pred type accepted rejected]
            [[tagPositive 'positive_integer 1 0]
             [tagNegative 'negative_integer -1 0]
             [tagNonNegative 'non_negative_integer 0 -1]
             [tagNonPositive 'non_positive_integer 0 1]]]
      (v/assert kb (list 'unaryPredicate pred) 'CxUniverse)
      (v/assert kb (list 'quotedArg pred 1 type) 'CxUniverse)
      (is (integer? (v/assert kb (list pred accepted) 'CxUniverse))
          (str type " admits a member literal written in the position"))
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list pred rejected) 'CxUniverse))
          (str type " refuses a literal outside its boundary")))))

(tu/deftest-kb the-quoted-reading-still-refuses-across-kinds
  ;; The regression half: widening the comparison to the value types must not make the
  ;; check admit what it always refused, and must not disturb the non-integer kinds.
  (tu/with-terms [needsString needsInteger]
    (v/assert kb (list 'unaryPredicate needsString) 'CxUniverse)
    (v/assert kb (list 'quotedArg needsString 1 'string) 'CxUniverse)
    (is (integer? (v/assert kb (list needsString "Bob") 'CxUniverse))
        "a string satisfies string")
    (is (thrown? clojure.lang.ExceptionInfo
                 (v/assert kb (list needsString 5) 'CxUniverse))
        "5 is a number, not a string")
    (v/assert kb (list 'unaryPredicate needsInteger) 'CxUniverse)
    (v/assert kb (list 'quotedArg needsInteger 1 'integer) 'CxUniverse)
    (is (integer? (v/assert kb (list needsInteger -7) 'CxUniverse))
        "an unrefined integer position still takes either sign")))

(tu/deftest-kb a-refused-sign-refinement-names-the-value-type
  ;; "it is a integer" says nothing useful about -5 refused a positive_integer, so the
  ;; message names what the value actually is when the refinement is what failed.
  (tu/with-terms [tagPositive]
    (v/assert kb (list 'unaryPredicate tagPositive) 'CxUniverse)
    (v/assert kb (list 'quotedArg tagPositive 1 'positive_integer) 'CxUniverse)
    (let [m (try (v/assert kb (list tagPositive -5) 'CxUniverse) nil
                 (catch clojure.lang.ExceptionInfo e (ex-message e)))]
      (is (some? m) "the assert is refused")
      (is (re-find #"negative_integer" (str m))
          (str "the message names the value's own type, not the bare EDN kind: " m)))))

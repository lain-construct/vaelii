;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.sign-integer-defn-test
  "The four sign-refined integer collections of CxCore — `positive_integer`,
  `negative_integer`, `non_negative_integer`, `non_positive_integer` — resolve **by
  evaluation** from a bare number, at zero sentex cost.

  They are defined with `defnSufficient` / `defnNecessary` over the computed predicates
  `integer` and `greaterThan` / `lessThan`, so membership is decided at query time by
  `DefnSufficientProver` (a passing sufficient admits) and non-membership by
  `DefnNecessaryNegationProver` (a failing necessary disproves) — no stored membership and
  no forward rule firing, which a computed condition never triggers (docs/defns.md)."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.core-context :as core-context]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh #(doto (tu/fresh) (core-context/load-into))))

;; ---- 1. the primitive: `integer` is computable from a bare value ----

(tu/deftest-kb integer-is-a-computed-kind-check
  (is (v/ask? kb (list 'integer 5) 'CxUniverse)      "5 is an integer, computed")
  (is (v/ask? kb (list 'integer -212) 'CxUniverse)   "a negative integer too")
  (is (not (v/ask? kb (list 'integer 3.5) 'CxUniverse))   "3.5 is not an integer")
  (is (not (v/ask? kb (list 'integer "str") 'CxUniverse)) "a string is not an integer")
  (is (not (v/ask? kb (list 'integer 'foo) 'CxUniverse))  "a symbol is not an integer"))

;; ---- 2. positive membership resolves by evaluation, from a bare number ----

(tu/deftest-kb sign-types-admit-by-evaluation
  (testing "each sign-type admits the numbers its condition holds for"
    (is (v/ask? kb (list 'positive_integer 5) 'CxUniverse)         "5 > 0")
    (is (v/ask? kb (list 'negative_integer -212) 'CxUniverse)      "-212 < 0 — the demo case")
    (is (v/ask? kb (list 'non_negative_integer 0) 'CxUniverse)     "0 ≥ 0")
    (is (v/ask? kb (list 'non_negative_integer 7) 'CxUniverse)     "7 ≥ 0")
    (is (v/ask? kb (list 'non_positive_integer 0) 'CxUniverse)     "0 ≤ 0")
    (is (v/ask? kb (list 'non_positive_integer -4) 'CxUniverse)    "-4 ≤ 0"))
  (testing "and does not admit a number its condition fails for"
    (is (not (v/ask? kb (list 'positive_integer -5) 'CxUniverse))     "-5 is not > 0")
    (is (not (v/ask? kb (list 'positive_integer 0) 'CxUniverse))      "0 is not > 0")
    (is (not (v/ask? kb (list 'negative_integer 5) 'CxUniverse))      "5 is not < 0")
    (is (not (v/ask? kb (list 'non_negative_integer -3) 'CxUniverse)) "-3 is not ≥ 0")
    (is (not (v/ask? kb (list 'non_positive_integer 3) 'CxUniverse))  "3 is not ≤ 0")))

;; ---- 3. non-membership is provable via a failing necessary ----

(tu/deftest-kb sign-types-disprove-via-a-failing-necessary
  (is (v/ask? kb (list 'not (list 'positive_integer -5)) 'CxUniverse)
      "-5 fails (greaterThan ?x 0), so ¬(positive_integer -5)")
  (is (v/ask? kb (list 'not (list 'positive_integer 0)) 'CxUniverse)
      "0 fails (greaterThan ?x 0)")
  (is (v/ask? kb (list 'not (list 'negative_integer 5)) 'CxUniverse)
      "5 fails (lessThan ?x 0)")
  (is (v/ask? kb (list 'not (list 'positive_integer "str")) 'CxUniverse)
      "a string fails (integer ?x), so ¬(positive_integer str)")
  (is (v/ask? kb (list 'not (list 'positive_integer 'unary_predicate)) 'CxUniverse)
      "a predicate symbol fails (integer ?x)")
  (testing "but a genuine member is NOT disproved (no false negation)"
    (is (not (v/ask? kb (list 'not (list 'positive_integer 5)) 'CxUniverse))
        "5 IS a positive integer, so ¬(positive_integer 5) must not be provable")
    (is (not (v/ask? kb (list 'not (list 'negative_integer -212)) 'CxUniverse))
        "-212 IS a negative integer")))

;; ---- 4. open-world silence: an unevidenced non-number is neither ----

(tu/deftest-kb open-world-silence-on-a-plain-individual
  ;; A plain named individual is not a number, so its necessary (integer ?x) fails and
  ;; ¬membership IS provable; but it is never a member.  (This mirrors the string/symbol
  ;; cases and keeps the two-valued reading honest.)
  (tu/with-terms [Fred]
    (is (not (v/ask? kb (list 'positive_integer Fred) 'CxUniverse))
        "Fred is not a positive integer")
    (is (v/ask? kb (list 'not (list 'positive_integer Fred)) 'CxUniverse)
        "Fred fails (integer ?x), so ¬(positive_integer Fred) is provable")))

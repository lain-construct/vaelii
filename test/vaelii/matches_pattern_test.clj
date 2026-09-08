;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.matches-pattern-test
  "`matchesPattern` — the computed string-shape check that lets a `defn` over a string
  subtype resolve **by evaluation**, the way `integer` lets the sign-refined integer
  collections resolve (docs/defns.md).  `(matchesPattern ?string ?pattern)` holds when the
  whole of `?string` matches the regular expression `?pattern`, both ground strings; the
  match runs through a step-limited view, and a pattern that does not compile is refused at
  the assert entry point."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.core-context :as core-context]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh #(doto (tu/fresh) (core-context/load-into))))

(def ^:private ipv4-pattern
  "A dotted-quad shape, loose on the digit count — enough to separate an address-shaped
  string from one that is not, which is what these tests need."
  "\\d+\\.\\d+\\.\\d+\\.\\d+")

;; ---- 1. the primitive: matchesPattern is computed from two ground strings ----

(tu/deftest-kb matchesPattern-is-a-computed-string-shape-check
  (testing "the whole string matches, or it does not"
    (is (v/ask? kb (list 'matchesPattern "192.168.1.1" ipv4-pattern) 'CxUniverse)
        "an address-shaped string matches")
    (is (not (v/ask? kb (list 'matchesPattern "not-an-ip" ipv4-pattern) 'CxUniverse))
        "a non-address does not"))
  (testing "the match is anchored to the whole string, not a substring"
    (is (not (v/ask? kb (list 'matchesPattern "192.168.1.1 and more" ipv4-pattern) 'CxUniverse))
        "a trailing tail fails a whole-string match"))
  (testing "a non-string subject is a sound no, the way integer is for a non-integer"
    (is (not (v/ask? kb (list 'matchesPattern 5 ipv4-pattern) 'CxUniverse))
        "5 is not a string")))

;; ---- 2. a string subtype defined over matchesPattern admits by evaluation ----

(tu/deftest-kb a-string-subtype-admits-by-evaluation
  ;; matchesPattern already answers false for a non-string subject, so the shape check
  ;; alone defines the subtype — no separate (string ?x) conjunct, which is not evaluable.
  (tu/with-terms [dotted_quad]
    (v/assert kb (list 'genl dotted_quad 'string) 'CxUniverse)
    (v/assert kb (list 'defnSufficient dotted_quad (list 'matchesPattern '?x ipv4-pattern)) 'CxUniverse)
    (v/assert kb (list 'defnNecessary  dotted_quad (list 'matchesPattern '?x ipv4-pattern)) 'CxUniverse)
    (testing "a member is admitted from a bare string, at zero sentex cost"
      (is (v/ask? kb (list dotted_quad "192.168.1.1") 'CxUniverse) "an address-shaped string")
      (is (v/ask? kb (list dotted_quad "10.0.0.1") 'CxUniverse)    "another"))
    (testing "and a non-member is not"
      (is (not (v/ask? kb (list dotted_quad "not-an-ip") 'CxUniverse))    "wrong shape")
      (is (not (v/ask? kb (list dotted_quad "192.168.1.1x") 'CxUniverse)) "a trailing character"))))

;; ---- 3. non-membership is provable via a failing necessary ----

(tu/deftest-kb a-string-subtype-disproves-via-a-failing-necessary
  (tu/with-terms [dotted_quad]
    (v/assert kb (list 'genl dotted_quad 'string) 'CxUniverse)
    (v/assert kb (list 'defnNecessary dotted_quad (list 'matchesPattern '?x ipv4-pattern)) 'CxUniverse)
    (is (v/ask? kb (list 'not (list dotted_quad "not-an-ip")) 'CxUniverse)
        "a wrong-shape string fails the necessary, so ¬membership is provable")
    (is (v/ask? kb (list 'not (list dotted_quad 5)) 'CxUniverse)
        "a non-string fails matchesPattern too")
    (testing "but a genuine member is NOT disproved"
      (is (not (v/ask? kb (list 'not (list dotted_quad "192.168.1.1")) 'CxUniverse))
          "an address-shaped string IS a member, so its negation must not be provable"))))

;; ---- 4. an uncompilable pattern is refused at the assert entry point ----

(tu/deftest-kb an-uncompilable-pattern-is-refused-at-the-assert-entry-point
  (testing "a pattern that does not compile is a :bad-pattern refusal"
    (let [problems (v/check kb (list 'matchesPattern "x" "(") 'CxCore)]
      (is (= :bad-pattern (:type (first problems)))
          "the unclosed group is reported, not left to fail silently at query time")))
  (testing "a compilable pattern raises no problem"
    (is (empty? (v/check kb (list 'matchesPattern "x" ipv4-pattern) 'CxCore))
        "a valid pattern is admitted")))

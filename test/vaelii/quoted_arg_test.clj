;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.quoted-arg-test
  "`(quotedArg pred n type)` — the mention twin of `arg` (docs/argtypes.md).  Where `arg`
  types what an argument *denotes*, `quotedArg` types the argument *as a term*: its EDN
  kind (string, number with integer below it, symbol) checked through genl against a
  syntactic type.  `(quotedArg nameOfGuy 1 string)` refuses `(nameOfGuy 5)` — 5 is a
  number, not a string — and admits `(nameOfGuy \"Bob\")`."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.core-context :as core-context]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded core-context/load-into))
(use-fixtures :each (tu/neutral))

(defn- refusal
  "The violation type `check` predicts for `sentence` in CxUniverse, or nil when it is
  well-formed."
  [kb sentence]
  (:type (first (v/check kb sentence 'CxUniverse))))

(tu/deftest-kb quotedarg-types-an-argument-by-its-literal-kind
  (tu/with-terms [nameOfGuy]
    (v/assert kb (list 'unaryPredicate nameOfGuy) 'CxUniverse)
    (v/assert kb (list 'quotedArg nameOfGuy 1 'string) 'CxUniverse)
    (testing "a string literal satisfies it — and stores"
      (is (nil? (refusal kb (list nameOfGuy "Bob"))))
      (is (some? (v/assert kb (list nameOfGuy "Bob") 'CxUniverse))))
    (testing "a number does not — 5 is not a string as a term"
      (is (= :quoted-arg-type (refusal kb (list nameOfGuy 5)))))
    (testing "nor does a symbol — a name is not a string, whatever it denotes"
      (is (= :quoted-arg-type (refusal kb (list nameOfGuy 'Muffet)))))))

(tu/deftest-kb quotedarg-follows-genl-among-the-syntactic-types
  (tu/with-terms [countOf]
    (v/assert kb (list 'unaryPredicate countOf) 'CxUniverse)
    (v/assert kb (list 'quotedArg countOf 1 'number) 'CxUniverse)
    (testing "an integer is a number, so (quotedArg countOf 1 number) admits it"
      (is (nil? (refusal kb (list countOf 5)))))
    (testing "a string is not a number"
      (is (= :quoted-arg-type (refusal kb (list countOf "five")))))))

(tu/deftest-kb quotedarg-is-open-world-about-a-kind-it-does-not-type
  ;; a keyword has no string/number/symbol kind, so `literal-type` is nil and the check is
  ;; silent — the same open-world floor `arg` gives an argument outside the hierarchy.
  (tu/with-terms [holds]
    (v/assert kb (list 'unaryPredicate holds) 'CxUniverse)
    (v/assert kb (list 'quotedArg holds 1 'string) 'CxUniverse)
    (is (nil? (refusal kb (list holds :a-keyword)))
        "an untyped literal kind is exempt, not convicted")))

(tu/deftest-kb quotedarg-and-arg-are-independent
  ;; `arg` (referent) and `quotedArg` (term) are separate checks on one position: the same
  ;; sentence can satisfy one and violate the other.
  (tu/with-terms [tagOf label]
    (v/assert kb (list 'unaryPredicate tagOf) 'CxUniverse)
    (v/assert kb (list 'genl label 'thing) 'CxUniverse)
    (v/assert kb (list 'arg tagOf 1 'label) 'CxUniverse)          ; the REFERENT must be a label
    (v/assert kb (list 'quotedArg tagOf 1 'string) 'CxUniverse)   ; the TERM must be a string
    (testing "a string literal passes quotedArg but is outside the label hierarchy — arg exempts it open-world"
      (is (nil? (refusal kb (list tagOf "x")))))))

(tu/deftest-kb quotedarg-is-open-world-about-a-non-syntactic-declared-type
  ;; a declared type outside the syntactic lattice (a domain collection, e.g. an imported
  ;; Cyc quoted-type that did not map to string/number/symbol) leaves the constraint
  ;; open-world — the check never convicts a literal against a type it cannot judge.
  (tu/with-terms [speaks agent]
    (v/assert kb (list 'unaryPredicate speaks) 'CxUniverse)
    (v/assert kb (list 'genl agent 'thing) 'CxUniverse)
    (v/assert kb (list 'quotedArg speaks 1 'agent) 'CxUniverse)   ; agent is not a syntactic type
    (is (nil? (refusal kb (list speaks "Bob")))
        "a string against a non-syntactic type is not convicted")
    (is (nil? (refusal kb (list speaks 5)))
        "nor is a number — the constraint is out of quotedArg's domain")))

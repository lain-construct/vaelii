;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.vocabulary-audit-test
  "Declared and enforced, against declared and ignored.

  Nothing about a declaration's *shape* says whether anything reads it.
  `(maxCardinality parentOf 2)` is a well-formed ternary fact, storable, believed, and
  read by nobody — so a KB author gets identical silence from a constraint that is
  enforced and one that was never implemented.  `vaelii.impl.vocabulary` answers the
  question for the engine's own grammar, and these tests are what keep the answer true:
  a term `CxCore` declares that the roster says nothing about fails here, and so
  does a roster entry naming a term the grammar has retired.

  A CxCore baseline is the whole population, which is why this is its own namespace
  — the constraint tests beside it (`constraint-vocabulary-test`) need a cleared KB."
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.core-context :as core-context]
            [vaelii.impl.special :as special]
            [vaelii.impl.vocabulary :as vocab]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh #(doto (tu/fresh) (core-context/load-into))))

(tu/deftest-kb every-term-the-grammar-declares-is-classified
  ;; The durable half.  A functor added to CxCore without anybody deciding whether
  ;; the engine reads it lands in `:unclassified`, and this fails — which is the whole
  ;; point: `interArgIsa` sat in the design notes as a plausible declaration for as long
  ;; as nothing was checking.
  (let [a (v/vocabulary-audit kb)]
    (is (empty? (:unclassified a))
        "a term CxCore declares that vocabulary/roster says nothing about")
    (is (empty? (:retired a))
        "a roster entry naming a term CxCore no longer declares")
    (is (empty? (:contradicted a))
        "a term the special-predicate table gives an arm to and the roster calls inert")
    (is (seq (:enforced a)))
    (is (seq (:inert a)) "and the inert set is not empty — that is the honest answer")))

(tu/deftest-kb a-new-grammar-declaration-nobody-classified-is-reported
  ;; The test above only fails if this mechanism works, so drive it: a term added to the
  ;; grammar shows up unclassified rather than passing quietly.
  (tu/with-terms [maxCardinality]
    (v/assert kb (list 'comment maxCardinality "a plausible-looking declaration")
              'CxCore)
    (is (= [maxCardinality] (:unclassified (v/vocabulary-audit kb))))))

(tu/deftest-kb the-special-predicate-table-and-the-roster-agree
  ;; The one cross-check that needs no judgement: the table is a data structure, and an
  ;; entry in it is proof that the functor has behaviour.
  (let [a        (v/vocabulary-audit kb)
        enforced (into #{} (map first) (:enforced a))
        inert    (into #{} (map first) (:inert a))]
    (doseq [[f _] special/entries
            :when (or (contains? enforced f) (contains? inert f))]
      (is (contains? enforced f)
          (str f " has a special-predicate table arm, so it is not inert")))))

(tu/deftest-kb the-two-new-constraints-are-on-the-enforced-side
  ;; Ties the implementations in `constraint-vocabulary-test` to the roster, so removing
  ;; one and leaving the claim is a failing test rather than a stale sentence.
  (is (:enforced (v/interpreted 'interArgIsa)))
  (is (:enforced (v/interpreted 'arity)))
  (is (nil? (v/interpreted 'maxCardinality))
      "a term the grammar does not declare is out of scope, not answered")
  (is (:inert (v/interpreted 'typeToInstancePred))
      "and a declared term nothing reads says so rather than reading as enforced"))

(deftest the-roster-answers-in-exactly-one-of-the-two-classes
  (doseq [[term entry] vocab/roster]
    (is (= 1 (count (select-keys entry [:enforced :inert])))
        (str term " must be enforced or inert, and say which"))
    (is (seq (or (:enforced entry) (:inert entry)))
        (str term " carries no reason"))))

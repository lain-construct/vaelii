;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.emptiness-test
  "`empty` and `nonempty` partition `unary_predicate` by extension: an `empty` type has no
  instance, and a `nonempty` type has at least one."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-core!))
(use-fixtures :each (tu/neutral))

(def ^:private U 'CxUniverse)

(defn- stored?
  "Whether `sentence` is answered facts-only from CxUniverse, so a rule's conclusion counts
  only once a forward firing has stored it."
  [kb sentence]
  (boolean (seq (v/query kb sentence U {:max-depth 0}))))

(defn- clashes-on
  "The exposed clashes whose term is `term`."
  [kb term]
  (filter #(= term (get-in % [:detail :term])) (v/exposed-clashes kb)))

;; ---- the partition ------------------------------------------------------

(tu/deftest-kb empty-and-nonempty-partition-unary-predicate
  (testing "each part is a subtype of unary_predicate"
    (is (v/genl? kb 'empty 'unary_predicate))
    (is (v/genl? kb 'nonempty 'unary_predicate)))
  (testing "the two parts are disjoint"
    (is (v/disjoint? kb 'empty 'nonempty)))
  (testing "each part holds types of any order"
    (doseq [t '[empty nonempty]]
      (is (v/isa? kb t 'variable_order_type))
      (is (v/isa? kb t 'at_least_metatype)))))

(tu/deftest-kb a-type-stated-both-empty-and-nonempty-is-an-exposed-clash
  (tu/with-terms [both_kind]
    (v/assert kb (list 'genl both_kind 'thing) U)
    (v/assert kb (list 'empty both_kind) U)
    (is (empty? (clashes-on kb both_kind)))
    (v/assert kb (list 'nonempty both_kind) U)
    (is (= [:disjoint] (map :violation (clashes-on kb both_kind))))))

(tu/deftest-kb an-empty-type-does-not-contradict-orthogonal
  ;; orthogonal says two types could share an instance, and an empty type shares none
  (tu/with-terms [unicorn horse]
    (v/assert kb (list 'genl unicorn 'thing) U)
    (v/assert kb (list 'genl horse 'thing) U)
    (v/assert kb (list 'orthogonal unicorn horse) U)
    (v/assert kb (list 'empty unicorn) U)
    (is (stored? kb (list 'empty unicorn)))
    (is (empty? (clashes-on kb unicorn)))
    (is (empty? (v/conflicts kb)))
    (is (= :orthogonal (v/subsumption-status kb unicorn horse)))))

(tu/deftest-kb one-type-empty-in-one-context-and-nonempty-in-a-sibling-is-no-clash
  ;; an empty claim holds for the context it is stated in, so two contexts no reader joins
  ;; may disagree
  (tu/with-terms [hobbit CxRealWorld CxMiddleEarth]
    (v/assert kb (list 'genl hobbit 'thing) U)
    (v/assert kb (list 'genlCx CxRealWorld U) U)
    (v/assert kb (list 'genlCx CxMiddleEarth U) U)
    (v/assert kb (list 'empty hobbit) CxRealWorld)
    (v/assert kb (list 'nonempty hobbit) CxMiddleEarth)
    (is (seq (v/query kb (list 'empty hobbit) CxRealWorld {:max-depth 0})))
    (is (seq (v/query kb (list 'nonempty hobbit) CxMiddleEarth {:max-depth 0})))
    (is (empty? (v/query kb (list 'nonempty hobbit) CxRealWorld {:max-depth 0})))
    (is (empty? (clashes-on kb hobbit)))
    (is (empty? (v/conflicts kb)))))

(tu/deftest-kb empty-and-nonempty-are-related-to-the-disjointness-terms
  (is (stored? kb '(termsRelated empty nonempty disjoint orthogonal))))

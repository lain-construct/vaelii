;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.relation-rigidity-test
  "The rigidity kinds of relation (core.txt): OntoClean's +R, -R and ~R read modally over
  every relation, functions and types included.

  `time_invariant_relation`, `time_agnostic_relation` and `time_varying_relation`
  partition `relation`; `possibly_time_invariant_relation` is the first two together,
  the other side of a second partition against `time_varying_relation`.  Possible
  invariance is preserved UP `genl` and time variance DOWN it, so a time-varying type
  over a time-invariant one is a clash the engine reports rather than a modelling slip
  nothing sees."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-core!))
(use-fixtures :each (tu/neutral))

(def ^:private U 'CxUniverse)
(def ^:private mono {:strength :monotonic})

(def ^:private rigidity-kinds
  '[time_invariant_relation time_agnostic_relation time_varying_relation])

(tu/deftest-kb the-rigidity-kinds-partition-relation
  (testing "each of the four is a commented type"
    (doseq [t (conj rigidity-kinds 'possibly_time_invariant_relation)]
      (is (seq (v/ask kb (list 'comment t '?c) 'CxUniverse)) (str t " is commented"))
      (is (v/isa? kb t 'unary_predicate) (str t " is a type"))
      (is (v/genl? kb t 'relation) (str t " is a kind of relation"))))
  (testing "the three kinds partition relation, and so do time variance and possible invariance"
    (is (v/ask? kb '(partition relation time_invariant_relation time_agnostic_relation
                               time_varying_relation) 'CxUniverse))
    (is (v/ask? kb '(partition relation time_varying_relation
                               possibly_time_invariant_relation) 'CxUniverse))
    (is (v/ask? kb '(partition possibly_time_invariant_relation time_invariant_relation
                               time_agnostic_relation) 'CxUniverse)))
  (testing "possible invariance is invariance or agnosticism"
    (is (v/genl? kb 'time_invariant_relation 'possibly_time_invariant_relation))
    (is (v/genl? kb 'time_agnostic_relation 'possibly_time_invariant_relation)))
  (testing "rigidity_kind classifies the three kinds, and not their union"
    (doseq [t rigidity-kinds]
      (is (v/ask? kb (list 'rigidity_kind t) 'CxUniverse) (str t " is a rigidity_kind")))
    (is (not (v/ask? kb '(rigidity_kind possibly_time_invariant_relation) 'CxUniverse)))))

(tu/deftest-kb possible-invariance-is-preserved-up-genl
  ;; transitiveInArg carries a claim along the genl arrow: (P W) with (genl W A) reaches
  ;; (P A).  A type whose spec could be held for good can be held for good.
  (tu/with-terms [person_kind animal_kind adult_kind]
    (v/assert kb (list 'genl animal_kind 'thing) U mono)
    (v/assert kb (list 'genl person_kind animal_kind) U mono)
    (v/assert kb (list 'genl adult_kind person_kind) U mono)
    (v/assert kb (list 'time_invariant_relation person_kind) U mono)
    (is (v/ask? kb (list 'possibly_time_invariant_relation animal_kind) U)
        "the genl inherits possible invariance from its spec")
    (is (not (v/ask? kb (list 'possibly_time_invariant_relation adult_kind) U))
        "and the spec does not inherit it from its genl")
    (is (not (v/ask? kb (list 'time_invariant_relation animal_kind) U))
        "only the union is preserved, never invariance itself")))

(tu/deftest-kb time-variance-is-preserved-down-genl
  ;; transitiveInArgInverse carries a claim against the genl arrow: (P W) with
  ;; (genl A W) reaches (P A).  Every spec of a type any of whose members could leave it
  ;; is one whose members could leave it.
  (tu/with-terms [student_kind honor_student_kind learner_kind]
    (v/assert kb (list 'genl learner_kind 'thing) U mono)
    (v/assert kb (list 'genl student_kind learner_kind) U mono)
    (v/assert kb (list 'genl honor_student_kind student_kind) U mono)
    (v/assert kb (list 'time_varying_relation student_kind) U mono)
    (is (v/ask? kb (list 'time_varying_relation honor_student_kind) U)
        "the spec inherits time variance from its genl")
    (is (not (v/ask? kb (list 'time_varying_relation learner_kind) U))
        "and the genl does not inherit it from its spec")))

(tu/deftest-kb a-time-varying-genl-of-a-time-invariant-type-is-a-clash
  ;; A person stays a person for as long as it exists; a student need not stay a student.
  ;; So a person cannot be a kind of student: every member of a time-varying type could
  ;; leave it, and a member that leaves student would leave person with it.
  (tu/with-terms [person_kind student_kind]
    (v/assert kb (list 'genl person_kind 'thing) U mono)
    (v/assert kb (list 'genl student_kind 'thing) U mono)
    (v/assert kb (list 'time_invariant_relation person_kind) U mono)
    (v/assert kb (list 'time_varying_relation student_kind) U mono)
    (is (empty? (v/conflicts kb)) "the two classifications alone clash with nothing")
    (v/assert kb (list 'genl person_kind student_kind) U mono)
    (let [clashes (set (map :sentence (filter #(= :inherited (:kind %)) (v/conflicts kb))))]
      (is (contains? clashes (list 'contradicts
                                   (list 'time_invariant_relation person_kind)
                                   (list 'time_varying_relation person_kind)))
          "time variance inherited down to person clashes with its invariance")
      (is (contains? clashes (list 'contradicts
                                   (list 'possibly_time_invariant_relation student_kind)
                                   (list 'time_varying_relation student_kind)))
          "possible invariance inherited up to student clashes with its variance"))))

(tu/deftest-kb every-relation-is-required-to-have-a-rigidity-kind
  ;; The partition says every relation IS of one kind; typeAllSpecified says the KB must
  ;; KNOW which.  Classifying the shipped relations is a to-do the sweep lists, so only
  ;; fictional relations are read here.
  (is (v/ask? kb '(typeAllSpecified rigidity_kind relation) 'CxUniverse))
  (tu/with-terms [ownsPet admiresPet]
    (v/assert kb (list 'binary_predicate ownsPet) U mono)
    (v/assert kb (list 'binary_predicate admiresPet) U mono)
    (v/assert kb (list 'time_varying_relation ownsPet) U mono)
    (let [r (get (:type-specified-violations
                  (v/kb-integrity kb #{} U {:categories #{:type-specified-violations}}))
                 '[typeAllSpecified rigidity_kind relation])]
      (is (= :audited (:status r)))
      (is (contains? (:violations r) admiresPet) "an unclassified relation is reported")
      (is (not (contains? (:violations r) ownsPet)) "a classified one is not"))))

;; ---- a function and its corresponding predicate share a rigidity kind ----------

(def ^:private correspondence #{:rigidity-correspondence})

(defn- corresponding-pair!
  "Declare `function` a unary function and `predicate` a binary predicate, linked by
  functionCorrespondingPredicate, the value position stated when `position` is given."
  [kb function predicate position]
  (v/assert kb (list 'unary_function function) U mono)
  (v/assert kb (list 'binary_predicate predicate) U mono)
  (v/assert kb (if position
                 (list 'functionCorrespondingPredicate function predicate position)
                 (list 'functionCorrespondingPredicate function predicate))
            U mono))

(tu/deftest-kb a-function-and-its-corresponding-predicate-must-share-a-rigidity-kind
  ;; (functionCorrespondingPredicate F P) says F and P state one relationship, so an
  ;; instance could lose the one exactly when it could lose the other.
  (tu/with-terms [HiveQueenFn hiveQueenOf]
    (corresponding-pair! kb HiveQueenFn hiveQueenOf nil)
    (v/assert kb (list 'time_invariant_relation HiveQueenFn) U mono)
    (testing "one side unclassified is silent: typeAllSpecified already reports it"
      (is (= {:status :audited :candidate-count 0}
             (v/kb-integrity kb #{} U {:categories correspondence}))))
    (testing "two different kinds are reported"
      (v/assert kb (list 'time_varying_relation hiveQueenOf) U mono)
      (is (= {:status :gap :candidate-count 0
              :rigidity-correspondence
              [{:function HiveQueenFn :predicate hiveQueenOf
                :function-kinds #{'time_invariant_relation}
                :predicate-kinds #{'time_varying_relation}}]}
             (v/kb-integrity kb #{} U {:categories correspondence}))))
    (testing "the default sweep runs the pass"
      (is (contains? (v/kb-integrity kb #{} U) :rigidity-correspondence)))))

(tu/deftest-kb a-function-and-its-corresponding-predicate-of-one-kind-are-not-reported
  (tu/with-terms [HiveQueenFn hiveQueenOf]
    (corresponding-pair! kb HiveQueenFn hiveQueenOf nil)
    (v/assert kb (list 'time_varying_relation HiveQueenFn) U mono)
    (v/assert kb (list 'time_varying_relation hiveQueenOf) U mono)
    (is (= {:status :audited :candidate-count 0}
           (v/kb-integrity kb #{} U {:categories correspondence})))))

(tu/deftest-kb a-correspondence-with-a-stated-position-is-read-too
  (tu/with-terms [NestMateFn nestMateOf]
    (corresponding-pair! kb NestMateFn nestMateOf 2)
    (v/assert kb (list 'time_agnostic_relation NestMateFn) U mono)
    (v/assert kb (list 'time_invariant_relation nestMateOf) U mono)
    (is (= [{:function NestMateFn :predicate nestMateOf
             :function-kinds #{'time_agnostic_relation}
             :predicate-kinds #{'time_invariant_relation}}]
           (:rigidity-correspondence
            (v/kb-integrity kb #{} U {:categories correspondence}))))))

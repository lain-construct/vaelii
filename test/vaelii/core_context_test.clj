(ns vaelii.core-context-test
  "The CoreContext ontology loads and documents the core predicates."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.core-context :as core-context]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh #(doto (tu/fresh) (core-context/load-into))))

(tu/deftest-kb core-predicates-are-documented
  (testing "every core predicate has a comment sentex in CoreContext"
    (doseq [term '[thing genl genlContext argIsa comment implies]]
      (is (= 1 (count (core-context/comment-of kb term))) (str "comment for " term))
      (is (string? (first (core-context/comment-of kb term))))))
  (testing "comments are ordinary sentexes living in CoreContext"
    (is (seq (v/sentexes-matching kb '(comment genl ?text) 'CoreContext)))))

(tu/deftest-kb extended-core-vocabulary-is-documented
  (testing "metadata, negation, and virtual rule wrappers each have a comment"
    (doseq [term '[not contradicts ist disjoint disjointMetatype and lessThan greaterThan
                   transitive symmetric reflexive functional inverse arity
                   decontextualizedPredicate
                   predicate unaryPredicate binaryPredicate ternaryPredicate
                   symmetricPredicate transitivePredicate reflexivePredicate functionalPredicate
                   set/forwardRule set/backwardRule set/inertRule set/defaultRule]]
      (is (= 1 (count (core-context/comment-of kb term))) (str "comment for " term))
      (is (string? (first (core-context/comment-of kb term)))))))

(tu/deftest-kb argisa-constraints-are-enforced-on-assert
  ;; argIsa is a core predicate the engine interprets, so a constraint on it is checked
  ;; on assert.  (The starter's domain argIsa live in the upper RelationContext now, not
  ;; the vocabulary head, so this defines its own vocabulary — wiring a data context to
  ;; see CoreContext directly, since a CoreContext-only KB has no spindle bands.)
  (let [animal (tu/tmp-type) rock (tu/tmp-type) kin (tu/tmp-pred)
        tom (tu/tmp-ind) boulder (tu/tmp-ind)]
    (v/assert kb '(genlContext DataContext CoreContext) 'UniverseContext)   ; a data context that sees core
    (v/assert kb (list 'genl animal 'thing) 'CoreContext)
    (v/assert kb (list 'genl rock   'thing) 'CoreContext)
    (v/assert kb (list 'argIsa kin 1 animal) 'CoreContext)                  ; the constraint
    (v/assert kb (list animal tom)    'DataContext)
    (v/assert kb (list rock   boulder) 'DataContext)
    (testing "the argIsa constraint applies on assert"
      (is (v/assert kb (list kin tom tom) 'DataContext))                    ; tom is an animal: OK
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list kin boulder tom) 'DataContext))))))   ; a rock is not an animal

(tu/deftest-kb arity-is-declared-functional
  ;; a predicate has one arity, and the two spellings derive each other — so a second,
  ;; different (arity P N) is a clash rather than a second belief.  Two numbers can
  ;; never merge into one thing, so this is the hard rejection, not an equality.
  (is (v/has-prop? kb :functional 'arity))
  (let [rel (tu/tmp-pred)]
    (v/assert kb (list 'binaryPredicate rel) 'CoreContext)
    (is (thrown? clojure.lang.ExceptionInfo
                 (v/assert kb (list 'arity rel 7) 'CoreContext)))))

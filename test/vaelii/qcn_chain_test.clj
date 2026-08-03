;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.qcn-chain-test
  "Forward chaining on a relation nobody stored.

  A forward rule's antecedents are matched against stored facts, and an *entailed*
  qualitative relation has no handle to match — so on its own it fires nothing, and a
  justification with no antecedent would be a conclusion nothing can withdraw.  Support
  closes that: an entailment names the stored facts it rests on, and those become the
  firing's antecedents.

  So these tests are about three things and not really about deriving at all: that the
  conclusion *arrives*, that `why` names the facts behind it, and that retracting any one
  of them takes it away again."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.space :as space]
            [vaelii.impl.starter :as starter]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded starter/load-into))
(use-fixtures :each (tu/neutral))

(defn- spatial-kb
  "Register the RCC-8 prover on the shared KB, and hand back a teardown that removes it
  again — the fixture guards sentexes, not the prover registry."
  [kb]
  (let [before @(:provers kb)]
    (v/add-prover kb (space/spatial-prover))
    (fn [] (reset! (:provers kb) before))))

(defmacro ^:private with-spatial
  "Run `body` with the RCC-8 prover registered, restoring the registry afterwards."
  [kb & body]
  `(let [undo# (spatial-kb ~kb)]
     (try ~@body (finally (undo#)))))

(defn- nest!
  "Assert a containment chain, returning the handles in order."
  [kb ctx regions]
  (mapv (fn [[a b]]
          (v/assert kb (list 'nonTangentialProperPart a b) ctx {:strength :monotonic}))
        (partition 2 1 regions)))

;; ---- the thing that could not happen before -----------------------------

(tu/deftest-kb an-entailed-relation-fires-a-forward-rule
  (tu/with-terms [RegA RegB RegC contained ChainSpaceContext]
    (with-spatial kb
      (v/assert kb (list 'genlContext ChainSpaceContext 'WellContext) 'UniverseContext
                {:strength :monotonic})
      (v/assert kb (list 'argIsa contained 1 'thing) 'CoreContext {:strength :monotonic})
      ;; a rule over a DERIVED spatial predicate: partOfRegion denotes a disjunction, so
      ;; nothing stores it — it is only ever entailed
      (v/assert-rule kb [(list 'properPartOfRegion '?x '?y)] (list contained '?x)
                     ChainSpaceContext)
      (nest! kb ChainSpaceContext [RegA RegB RegC])
      (testing "the transitive relation is entailed and genuinely not stored"
        (is (nil? (v/handle-of kb (list 'properPartOfRegion RegA RegC) ChainSpaceContext)))
        (is (= #{:ntpp} (v/possible-relations kb :rcc8 ChainSpaceContext RegA RegC))))
      (testing "and the rule fired on it"
        (is (seq (v/sentexes-matching kb (list contained RegA) '?ctx))
            "A is contained — from the asserted step")
        (is (seq (v/sentexes-matching kb (list contained RegB) '?ctx))
            "B is contained — B is a proper part of C")))))

(tu/deftest-kb the-conclusion-names-the-facts-the-entailment-rests-on
  (tu/with-terms [RegA RegB RegC deepIn ChainWhyContext]
    (with-spatial kb
      (v/assert kb (list 'genlContext ChainWhyContext 'WellContext) 'UniverseContext
                {:strength :monotonic})
      (v/assert kb (list 'argIsa deepIn 1 'thing) 'CoreContext {:strength :monotonic})
      ;; the antecedent pins A to C specifically, so the only way to satisfy it is the
      ;; two-step entailment
      (v/assert-rule kb [(list 'properPartOfRegion RegA RegC)] (list deepIn RegA)
                     ChainWhyContext)
      (let [[h-ab h-bc] (nest! kb ChainWhyContext [RegA RegB RegC])
            concl (first (v/sentexes-matching kb (list deepIn RegA) '?ctx))
            h     (:id concl)]
        (is (some? h) "the conclusion arrived")
        (testing "why names both stored steps — the support the network reported"
          (let [named (set (tree-seq coll? seq (v/why kb h)))]
            (is (contains? named h-ab) "the A-B fact is in the proof")
            (is (contains? named h-bc) "the B-C fact is in the proof")))
        (testing "and it is derived, not a premise"
          (is (false? (v/premise? kb h))))))))

(tu/deftest-kb retracting-any-supporting-fact-withdraws-the-conclusion
  (tu/with-terms [RegA RegB RegC deepIn RetractSpaceContext]
    (with-spatial kb
      (v/assert kb (list 'genlContext RetractSpaceContext 'WellContext) 'UniverseContext
                {:strength :monotonic})
      (v/assert kb (list 'argIsa deepIn 1 'thing) 'CoreContext {:strength :monotonic})
      (v/assert-rule kb [(list 'properPartOfRegion RegA RegC)] (list deepIn RegA)
                     RetractSpaceContext)
      (let [[_ h-bc] (nest! kb RetractSpaceContext [RegA RegB RegC])]
        (is (seq (v/sentexes-matching kb (list deepIn RegA) '?ctx)) "believed while both steps stand")
        (testing "dropping the second step breaks the chain, and the conclusion goes"
          (v/retract! kb h-bc)
          (is (empty? (v/sentexes-matching kb (list deepIn RegA) '?ctx))
              "the entailment is gone, so what rested on it is gone")
          (is (= 8 (count (v/possible-relations kb :rcc8 RetractSpaceContext RegA RegC)))
              "unconstrained is the whole universe — `#{}` would mean *inconsistent*"))
        (testing "and re-asserting it brings the conclusion back"
          (v/assert kb (list 'nonTangentialProperPart RegB RegC) RetractSpaceContext
                    {:strength :monotonic})
          (is (seq (v/sentexes-matching kb (list deepIn RegA) '?ctx))
              "re-derived, at a fresh handle"))))))

;; ---- the boundaries ------------------------------------------------------

(tu/deftest-kb without-the-prover-registered-nothing-changes
  (tu/with-terms [RegA RegB RegC contained InertSpaceContext]
    (v/assert kb (list 'genlContext InertSpaceContext 'WellContext) 'UniverseContext
              {:strength :monotonic})
    (v/assert kb (list 'argIsa contained 1 'thing) 'CoreContext {:strength :monotonic})
    (v/assert-rule kb [(list 'properPartOfRegion '?x '?y)] (list contained '?x)
                   InertSpaceContext)
    (nest! kb InertSpaceContext [RegA RegB RegC])
    (testing "the vocabulary loads, the facts store, and the rule simply does not fire —
              registering a prover is the opt-in, and this is the KB that never did"
      (is (empty? (v/sentexes-matching kb (list contained RegA) '?ctx)))
      (is (empty? (v/sentexes-matching kb (list contained RegB) '?ctx))))))

(tu/deftest-kb an-asserted-relation-still-fires-as-it-always-did
  (tu/with-terms [RegA RegB touching AssertedSpaceContext]
    (with-spatial kb
      (v/assert kb (list 'genlContext AssertedSpaceContext 'WellContext) 'UniverseContext
                {:strength :monotonic})
      (v/assert kb (list 'argIsa touching 1 'thing) 'CoreContext {:strength :monotonic})
      (v/assert-rule kb [(list 'externallyConnected '?x '?y)] (list touching '?x)
                     AssertedSpaceContext)
      (v/assert kb (list 'externallyConnected RegA RegB) AssertedSpaceContext
                {:strength :monotonic})
      (testing "the ordinary matched route is untouched — entailment is a union with it,
                never a replacement, so nothing that fired before stops firing"
        (is (seq (v/sentexes-matching kb (list touching RegA) '?ctx)))))))

(tu/deftest-kb the-diagonal-entails-but-supports-nothing-so-it-concludes-nothing
  (tu/with-terms [RegA RegB reflexive DiagonalSpaceContext]
    (with-spatial kb
      (v/assert kb (list 'genlContext DiagonalSpaceContext 'WellContext) 'UniverseContext
                {:strength :monotonic})
      (v/assert kb (list 'argIsa reflexive 1 'thing) 'CoreContext {:strength :monotonic})
      ;; partOfRegion contains the identity, so (partOfRegion ?x ?x) is entailed of every
      ;; region by the algebra alone — with no stored fact behind it
      (v/assert-rule kb [(list 'partOfRegion '?x '?x)] (list reflexive '?x)
                     DiagonalSpaceContext)
      (v/assert kb (list 'nonTangentialProperPart RegA RegB) DiagonalSpaceContext
                {:strength :monotonic})
      (testing "the algebra's identity is not evidence: a conclusion drawn from it would
                rest on nothing retractable, so the empty support is dropped"
        (is (empty? (v/sentexes-matching kb (list reflexive RegA) '?ctx)))
        (is (= #{:eq} (v/possible-relations kb :rcc8 DiagonalSpaceContext RegA RegA))
            "the diagonal is still entailed — it is only unusable as support")))))

(tu/deftest-kb an-entailment-in-an-unsatisfiable-network-concludes-nothing
  (tu/with-terms [RegA RegB RegC contained ClashChainContext]
    (with-spatial kb
      (v/assert kb (list 'genlContext ClashChainContext 'WellContext) 'UniverseContext
                {:strength :monotonic})
      (v/assert kb (list 'argIsa contained 1 'thing) 'CoreContext {:strength :monotonic})
      (v/assert-rule kb [(list 'properPartOfRegion '?x '?y)] (list contained '?x)
                     ClashChainContext)
      (nest! kb ClashChainContext [RegA RegB RegC])
      (is (seq (v/sentexes-matching kb (list contained RegA) '?ctx)) "believed while consistent")
      (let [clash (v/assert kb (list 'spatiallyDisconnected RegA RegB) ClashChainContext
                            {:strength :monotonic})]
        (testing "an impossible theory should not be mined for conclusions"
          (is (false? (:consistent? (v/qualitative-network kb :rcc8 ClashChainContext))))
          (is (empty? (v/sentexes-matching kb (list contained RegA) '?ctx))
              "the conclusion goes, though every fact it listed as support is still believed
               — which is the whole reason this cannot ride on the antecedents alone"))
        (testing "and retracting the clash brings it back"
          (v/retract! kb clash)
          (is (true? (:consistent? (v/qualitative-network kb :rcc8 ClashChainContext))))
          (is (seq (v/sentexes-matching kb (list contained RegA) '?ctx))
              "blocked, not destroyed — the same revival an excepted conclusion gets"))))))

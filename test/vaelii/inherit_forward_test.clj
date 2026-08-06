;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.inherit-forward-test
  "Forward chaining on a claim nobody stored.

  `(argPreserving largerThan 1 genl)` beside `(largerThan dog cat)` licenses
  `(largerThan chihuahua maine_coon)`, and a rule over `largerThan` has to fire on it —
  or `sentexes-matching` reads one answer out of the fixpoint while `ask` re-derives
  another through `ArgPreservingProver`, which is the same knowledge giving two answers
  depending on which door the reader came in.

  What makes that possible is that an inherited claim, while it is not stored, was
  *read from* things that are: the claim that was stated, the declaration licensing the
  move, and the relation edges the reach travelled.  The firing names them, so the
  tests below are mostly about that list — `why` reads it back, retraction walks it,
  and placement is computed from it."
  (:require [clojure.set :as set]
            [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(def ^:private ctx 'UniverseContext)

(defn- holds?
  "Does the KB **hold** this sentence — is it in what the fixpoint derived, rather than
  what a prover would re-derive on demand?  The half of the disagreement this whole
  namespace is about."
  [kb s]
  (boolean (seq (v/sentexes-matching kb s ctx))))

(defn- kinds!
  "dog ⊃ {golden_retriever chihuahua}, cat ⊃ {maine_coon siamese}."
  [kb {:keys [dog cat gr chi mc sia]}]
  (v/with-deferred-settle kb
    (doseq [[sub sup] [[gr dog] [chi dog] [mc cat] [sia cat]]]
      (v/assert kb (list 'genl sub sup) ctx))))

(defn- preserving!
  "Both positions of `pred` preserved along genl, and the asymmetry that gives a
  converse the standing to deny an inherited claim."
  [kb pred]
  (v/with-deferred-settle kb
    (v/assert kb (list 'asymmetric pred) ctx)
    (v/assert kb (list 'argPreserving pred 1 'genl) ctx)
    (v/assert kb (list 'argPreserving pred 2 'genl) ctx)))

;; ---- the disagreement itself ---------------------------------------------

(tu/deftest-kb the-two-doors-give-the-same-answer
  (tu/with-terms [dog_t cat_t golden_retriever_t maine_coon_t chihuahua_t siamese_t
                  largerThan outweighs]
    (kinds! kb {:dog dog_t :cat cat_t :gr golden_retriever_t
                :chi chihuahua_t :mc maine_coon_t :sia siamese_t})
    (preserving! kb largerThan)
    (v/assert kb (list largerThan dog_t cat_t) ctx)
    (v/assert kb (list 'implies (list largerThan '?x '?y) (list outweighs '?x '?y)) ctx)
    (testing "the stored antecedent, which always fired"
      (is (holds? kb (list outweighs dog_t cat_t)))
      (is (v/ask? kb (list outweighs dog_t cat_t) ctx)))
    (testing "and the inherited one, which is the point"
      (is (holds? kb (list outweighs chihuahua_t maine_coon_t)))
      (is (v/ask? kb (list outweighs chihuahua_t maine_coon_t) ctx)))
    (testing "every tuple the claim licenses, and no tuple it does not"
      (is (= 9 (count (v/sentexes-matching kb (list outweighs '?x '?y) ctx)))
          "3 terms below-or-at dog × 3 below-or-at cat")
      (is (not (holds? kb (list outweighs maine_coon_t chihuahua_t)))
          "preservation runs down the edges, never back up them"))))

(tu/deftest-kb the-firing-names-the-claim-the-declaration-and-the-edges
  (tu/with-terms [dog_t cat_t golden_retriever_t maine_coon_t chihuahua_t siamese_t
                  largerThan outweighs]
    (kinds! kb {:dog dog_t :cat cat_t :gr golden_retriever_t
                :chi chihuahua_t :mc maine_coon_t :sia siamese_t})
    (preserving! kb largerThan)
    (v/assert kb (list largerThan dog_t cat_t) ctx)
    (v/assert kb (list 'implies (list largerThan '?x '?y) (list outweighs '?x '?y)) ctx)
    (let [w (v/why kb (v/handle-of kb (list outweighs chihuahua_t maine_coon_t) ctx))
          reasons (into #{} (comp (mapcat :because) (map :sentence)) (:support w))]
      (is (:believed? w))
      (testing "the actual reasons, and the reader can read them"
        (is (contains? reasons (list largerThan dog_t cat_t)))
        (is (contains? reasons (list 'genl chihuahua_t dog_t)))
        (is (contains? reasons (list 'genl maine_coon_t cat_t))))
      (testing "and the declarations, which license the move and are as retractable"
        (is (contains? reasons (list 'argPreserving largerThan 1 'genl)))
        (is (contains? reasons (list 'argPreserving largerThan 2 'genl))))
      (testing "nothing else — a witness, not a transcript"
        (is (= 5 (count reasons)) (pr-str reasons))))))

(tu/deftest-kb a-claim-stated-at-the-tuple-is-justified-once
  ;; The diagonal.  `witness-terms` is reflexive, so the stored claim is among the
  ;; claims bearing on its own tuple — and it already has the ordinary matcher's
  ;; justification.  A second one resting on nothing new would be manufactured.
  (tu/with-terms [dog_t cat_t golden_retriever_t maine_coon_t chihuahua_t siamese_t
                  largerThan outweighs]
    (kinds! kb {:dog dog_t :cat cat_t :gr golden_retriever_t
                :chi chihuahua_t :mc maine_coon_t :sia siamese_t})
    (preserving! kb largerThan)
    (v/assert kb (list largerThan dog_t cat_t) ctx)
    (v/assert kb (list 'implies (list largerThan '?x '?y) (list outweighs '?x '?y)) ctx)
    (let [w (v/why kb (v/handle-of kb (list outweighs dog_t cat_t) ctx))]
      (is (= 1 (count (:support w))))
      (is (= [(list largerThan dog_t cat_t)]
             (mapv :sentence (:because (first (:support w)))))
          "the stored claim alone, with no edge and no declaration beneath it"))))

;; ---- retraction reaches it ----------------------------------------------

(tu/deftest-kb retracting-any-reason-withdraws-the-conclusion
  (tu/with-terms [dog_t cat_t golden_retriever_t maine_coon_t chihuahua_t siamese_t
                  largerThan outweighs]
    (kinds! kb {:dog dog_t :cat cat_t :gr golden_retriever_t
                :chi chihuahua_t :mc maine_coon_t :sia siamese_t})
    (preserving! kb largerThan)
    (v/assert kb (list largerThan dog_t cat_t) ctx)
    (v/assert kb (list 'implies (list largerThan '?x '?y) (list outweighs '?x '?y)) ctx)
    (let [goal (list outweighs chihuahua_t maine_coon_t)]
      (doseq [reason [(list 'genl chihuahua_t dog_t)
                      (list 'genl maine_coon_t cat_t)
                      (list largerThan dog_t cat_t)
                      (list 'argPreserving largerThan 1 'genl)]]
        (testing (str "retracting " (pr-str reason))
          (let [h (v/handle-of kb reason ctx)]
            (v/retract! kb h)
            (is (not (holds? kb goal)))
            (v/assert kb reason ctx)
            (is (holds? kb goal) "and re-asserting brings it back")))))
    (testing "and the rule, which every firing rests on"
      (let [r (list 'implies (list largerThan '?x '?y) (list outweighs '?x '?y))]
        (v/retract! kb (v/handle-of kb r ctx))
        (is (empty? (v/sentexes-matching kb (list outweighs '?x '?y) ctx)))
        (v/assert kb r ctx)
        (is (holds? kb (list outweighs chihuahua_t maine_coon_t)))))))

(tu/deftest-kb an-untouched-pair-survives-a-retraction-that-takes-its-neighbour
  (tu/with-terms [dog_t cat_t golden_retriever_t maine_coon_t chihuahua_t siamese_t
                  largerThan outweighs]
    (kinds! kb {:dog dog_t :cat cat_t :gr golden_retriever_t
                :chi chihuahua_t :mc maine_coon_t :sia siamese_t})
    (preserving! kb largerThan)
    (v/assert kb (list largerThan dog_t cat_t) ctx)
    (v/assert kb (list 'implies (list largerThan '?x '?y) (list outweighs '?x '?y)) ctx)
    (v/retract! kb (v/handle-of kb (list 'genl chihuahua_t dog_t) ctx))
    (is (not (holds? kb (list outweighs chihuahua_t maine_coon_t))))
    (is (holds? kb (list outweighs golden_retriever_t maine_coon_t))
        "the edge it did not travel is still there")
    (is (holds? kb (list outweighs dog_t cat_t)))))

;; ---- withdrawal with nothing retracted ----------------------------------

(tu/deftest-kb a-more-specific-contrary-claim-withdraws-the-conclusion
  ;; The case the antecedents cannot express: every one of them is still stored and
  ;; believed, and a claim about a *narrower* pair has undercut what they licensed.
  (tu/with-terms [dog_t cat_t golden_retriever_t maine_coon_t chihuahua_t siamese_t
                  typicallyLargerThan outweighs]
    (kinds! kb {:dog dog_t :cat cat_t :gr golden_retriever_t
                :chi chihuahua_t :mc maine_coon_t :sia siamese_t})
    (preserving! kb typicallyLargerThan)
    (v/assert kb (list typicallyLargerThan dog_t cat_t) ctx)
    (v/assert kb (list 'implies (list typicallyLargerThan '?x '?y)
                       (list outweighs '?x '?y))
              ctx)
    (is (holds? kb (list outweighs chihuahua_t maine_coon_t)))
    (let [specific (list typicallyLargerThan maine_coon_t chihuahua_t)]
      (v/assert kb specific ctx)
      (testing "the general claim stops firing for that pair, and nothing was retracted"
        (is (not (holds? kb (list outweighs chihuahua_t maine_coon_t))))
        (is (not (v/ask? kb (list outweighs chihuahua_t maine_coon_t) ctx))
            "and the two doors still agree")
        (is (v/in? kb (v/handle-of kb (list typicallyLargerThan dog_t cat_t) ctx))
            "the general claim is undercut for one pair, not defeated"))
      (testing "the pairs it says nothing about are untouched"
        (is (holds? kb (list outweighs golden_retriever_t maine_coon_t)))
        (is (holds? kb (list outweighs dog_t cat_t))))
      (testing "and the specific claim fires in its own direction"
        (is (holds? kb (list outweighs maine_coon_t chihuahua_t))))
      (testing "retracting it brings the inherited conclusion back"
        (v/retract! kb (v/handle-of kb specific ctx))
        (is (holds? kb (list outweighs chihuahua_t maine_coon_t)))
        (is (v/ask? kb (list outweighs chihuahua_t maine_coon_t) ctx))))))

;; ---- the relation is a parameter ----------------------------------------

(tu/deftest-kb a-fact-relation-carries-a-firing-the-same-way
  ;; No types in sight: the reach is walked over stored `partOf` facts, and the
  ;; justification names those facts and the `(transitive partOf)` that licensed
  ;; closing them.
  (tu/with-terms [partOf needsMaintenance schedule Car Engine Piston]
    (v/with-deferred-settle kb
      (v/assert kb (list 'transitive partOf) ctx)
      (v/assert kb (list 'argPreserving needsMaintenance 1 partOf) ctx)
      (v/assert kb (list partOf Engine Car) ctx)
      (v/assert kb (list partOf Piston Engine) ctx))
    (v/assert kb (list needsMaintenance Car) ctx)
    (v/assert kb (list 'implies (list needsMaintenance '?x) (list schedule '?x)) ctx)
    (is (holds? kb (list schedule Piston)) "two hops down the part chain")
    (is (v/ask? kb (list schedule Piston) ctx))
    (let [reasons (into #{}
                        (comp (mapcat :because) (map :sentence))
                        (:support (v/why kb (v/handle-of kb (list schedule Piston) ctx))))]
      (is (contains? reasons (list needsMaintenance Car)))
      (is (contains? reasons (list partOf Piston Engine)))
      (is (contains? reasons (list partOf Engine Car)))
      (is (contains? reasons (list 'transitive partOf))
          "read at use, so a firing that rests on it says so"))
    (testing "and withdrawing the transitivity withdraws what it closed"
      (v/retract! kb (v/handle-of kb (list 'transitive partOf) ctx))
      (is (not (holds? kb (list schedule Piston))))
      (is (holds? kb (list schedule Car)) "the stated claim is untouched"))))

(tu/deftest-kb the-inverse-declaration-fires-upward
  (tu/with-terms [dog_t animal_t thing_t hasA aboutIt]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genl dog_t animal_t) ctx)
      (v/assert kb (list 'genl animal_t thing_t) ctx)
      (v/assert kb (list 'argPreservingInverse hasA 1 'genl) ctx))
    (v/assert kb (list hasA dog_t) ctx)
    (v/assert kb (list 'implies (list hasA '?x) (list aboutIt '?x)) ctx)
    (is (holds? kb (list aboutIt animal_t)) "one edge up")
    (is (holds? kb (list aboutIt thing_t)) "and two")
    (is (holds? kb (list aboutIt dog_t)) "the stated one, by the ordinary matcher")))

;; ---- joining with an ordinary antecedent --------------------------------

(tu/deftest-kb an-inherited-antecedent-joins-with-a-matched-one
  ;; The other shape: the ordinary antecedent binds the variables first, so the
  ;; preserved one reaches the join closed and asks one question per binding.  The
  ;; rule goes in **first** here, so the join runs at the arriving fact's trigger
  ;; position rather than as the rule's own full pass.
  (tu/with-terms [dog_t cat_t golden_retriever_t maine_coon_t chihuahua_t siamese_t
                  largerThan competing winsAgainst]
    (kinds! kb {:dog dog_t :cat cat_t :gr golden_retriever_t
                :chi chihuahua_t :mc maine_coon_t :sia siamese_t})
    (preserving! kb largerThan)
    (v/assert kb (list largerThan dog_t cat_t) ctx)
    (v/assert kb (list 'implies (list 'and (list competing '?x '?y) (list largerThan '?x '?y))
                       (list winsAgainst '?x '?y))
              ctx)
    (v/assert kb (list competing chihuahua_t maine_coon_t) ctx)
    (v/assert kb (list competing maine_coon_t chihuahua_t) ctx)
    (is (holds? kb (list winsAgainst chihuahua_t maine_coon_t)))
    (is (not (holds? kb (list winsAgainst maine_coon_t chihuahua_t)))
        "the other direction is not licensed, so the join finds nothing")))

(tu/deftest-kb a-derived-claim-licenses-the-inheritance-a-stated-one-does
  ;; A claim the fixpoint concluded is a datum like any other, so it re-joins the rules
  ;; over its predicate — or which claims inherit would depend on whether somebody
  ;; wrote them or a rule reached them.
  (tu/with-terms [dog_t cat_t golden_retriever_t maine_coon_t chihuahua_t siamese_t
                  largerThan outweighs bulkierThan]
    (kinds! kb {:dog dog_t :cat cat_t :gr golden_retriever_t
                :chi chihuahua_t :mc maine_coon_t :sia siamese_t})
    (preserving! kb largerThan)
    (v/assert kb (list 'implies (list bulkierThan '?x '?y) (list largerThan '?x '?y)) ctx)
    (v/assert kb (list 'implies (list largerThan '?x '?y) (list outweighs '?x '?y)) ctx)
    (v/assert kb (list bulkierThan dog_t cat_t) ctx)
    (is (holds? kb (list largerThan dog_t cat_t)) "the first rule concluded the claim")
    (is (holds? kb (list outweighs chihuahua_t maine_coon_t))
        "and the second fired on what that claim licenses")))

;; ---- placement ----------------------------------------------------------

(tu/deftest-kb the-conclusion-lands-where-its-reasons-can-be-seen
  (tu/with-terms [dog_t cat_t chihuahua_t maine_coon_t largerThan outweighs
                  UpperContext LowerContext]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genlContext UpperContext ctx) ctx)
      (v/assert kb (list 'genlContext LowerContext UpperContext) ctx))
    (v/with-deferred-settle kb
      (v/assert kb (list 'asymmetric largerThan) UpperContext)
      (v/assert kb (list 'argPreserving largerThan 1 'genl) UpperContext)
      (v/assert kb (list 'argPreserving largerThan 2 'genl) UpperContext)
      (v/assert kb (list largerThan dog_t cat_t) UpperContext))
    ;; the edges are stated only in the lower context, so only it can see the reach
    (v/with-deferred-settle kb
      (v/assert kb (list 'genl chihuahua_t dog_t) LowerContext)
      (v/assert kb (list 'genl maine_coon_t cat_t) LowerContext))
    (v/assert kb (list 'implies (list largerThan '?x '?y) (list outweighs '?x '?y))
              UpperContext)
    (let [sx (first (v/sentexes-matching kb (list outweighs chihuahua_t maine_coon_t)
                                         LowerContext))]
      (is (some? sx) "derived, from the one context that sees the rule, the claim and both edges")
      (is (= LowerContext (:context sx))
          "and it descends to the edges rather than sitting above them"))
    (is (empty? (v/sentexes-matching kb (list outweighs chihuahua_t maine_coon_t) UpperContext))
        "the context that cannot see the edges does not hold the conclusion")))

(tu/deftest-kb a-firing-with-no-common-context-is-reported-rather-than-dropped
  (tu/with-terms [dog_t cat_t chihuahua_t maine_coon_t largerThan outweighs
                  BaseContext LeftContext RightContext]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genlContext BaseContext ctx) ctx)
      (v/assert kb (list 'genlContext LeftContext BaseContext) ctx)
      (v/assert kb (list 'genlContext RightContext BaseContext) ctx))
    (v/with-deferred-settle kb
      (v/assert kb (list 'argPreserving largerThan 1 'genl) BaseContext)
      (v/assert kb (list 'argPreserving largerThan 2 'genl) BaseContext)
      (v/assert kb (list largerThan dog_t cat_t) BaseContext))
    ;; incomparable contexts hold one edge each: no context sees both
    (v/assert kb (list 'genl chihuahua_t dog_t) LeftContext)
    (v/assert kb (list 'genl maine_coon_t cat_t) RightContext)
    (v/assert kb (list 'implies (list largerThan '?x '?y) (list outweighs '?x '?y))
              BaseContext)
    (is (empty? (v/sentexes-matching kb (list outweighs chihuahua_t maine_coon_t) LeftContext)))
    (is (empty? (v/sentexes-matching kb (list outweighs chihuahua_t maine_coon_t) RightContext)))
    (is (some #(and (= :no-placement (:violation %))
                    (= (list outweighs chihuahua_t maine_coon_t) (:sentence %)))
              (v/violations kb))
        "a completed firing that lands nowhere is recorded, never silently dropped")))

;; ---- a KB that declares nothing ----------------------------------------

(tu/deftest-kb no-declaration-derives-nothing-new
  (tu/with-terms [dog_t cat_t golden_retriever_t maine_coon_t chihuahua_t siamese_t
                  largerThan outweighs]
    (kinds! kb {:dog dog_t :cat cat_t :gr golden_retriever_t
                :chi chihuahua_t :mc maine_coon_t :sia siamese_t})
    (v/assert kb (list largerThan dog_t cat_t) ctx)
    (v/assert kb (list 'implies (list largerThan '?x '?y) (list outweighs '?x '?y)) ctx)
    (is (= [(list outweighs dog_t cat_t)]
           (mapv :sentence (v/sentexes-matching kb (list outweighs '?x '?y) ctx)))
        "the stored claim's own tuple and nothing else")))

;; ---- order independence -------------------------------------------------

(defn- derived-outweighs
  "The derived content and the justifications behind it, by **content** — handles are
  allocated in assertion order, which is the one thing a reordering must not move."
  [kb pred]
  (let [sentences (into #{} (map :sentence) (v/sentexes-matching kb (list pred '?x '?y) ctx))]
    {:derived sentences
     :because (into #{}
                    (map (fn [s]
                           [s (into #{}
                                    (comp (mapcat :because) (map :sentence))
                                    (:support (v/why kb (v/handle-of kb s ctx))))]))
                    sentences)}))

(defn- shuffled
  "A permutation of `xs` from `rng` — `clojure.core/shuffle` reads a global source, and
  a randomized oracle that cannot be replayed from its seed is not one."
  [xs ^java.util.Random rng]
  (let [a (java.util.ArrayList. ^java.util.Collection (vec xs))]
    (java.util.Collections/shuffle a rng)
    (vec a)))

(tu/deftest-kb the-same-content-in-any-order-reaches-the-same-firings
  ;; Every failure on this path is a *missing* answer — a firing the trigger index
  ;; could not connect — and a KB that is merely less informative than it should be
  ;; reads as correct against anything except another order of the same content.  So
  ;; the declaration, the edges, the claim and the rule are permuted together: "the
  ;; rule arrived last" is what a rule's own full join would otherwise paper over.
  (tu/with-terms [dog_t cat_t golden_retriever_t maine_coon_t chihuahua_t siamese_t
                  largerThan outweighs]
    (let [content [(list 'genl chihuahua_t dog_t)
                   (list 'genl golden_retriever_t dog_t)
                   (list 'genl maine_coon_t cat_t)
                   (list 'genl siamese_t cat_t)
                   (list 'argPreserving largerThan 1 'genl)
                   (list 'argPreserving largerThan 2 'genl)
                   (list largerThan dog_t cat_t)
                   (list 'implies (list largerThan '?x '?y) (list outweighs '?x '?y))]
          go   (fn [order]
                 (let [k (tu/isolated-fresh)]
                   (try
                     (doseq [s order] (v/assert k s ctx))
                     (derived-outweighs k outweighs)
                     (finally (tu/clear-kb! k)))))
          rng  (java.util.Random. 20260804)
          runs (mapv (fn [_] (go (shuffled content rng))) (range 8))]
      (is (= 9 (count (:derived (first runs)))) "the run is not vacuous")
      (doseq [[i r] (map-indexed vector (rest runs))]
        (is (= (first runs) r)
            (str "order " (inc i) " reached a different fixpoint:\n"
                 (pr-str (set/difference (:derived (first runs)) (:derived r)))
                 " / "
                 (pr-str (set/difference (:derived r) (:derived (first runs))))))))))

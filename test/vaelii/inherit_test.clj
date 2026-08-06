;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.inherit-test
  "Argument-position preservation: `(argPreserving P n R)` /
  `(argPreservingInverse P n R)`, the specificity that lets a stated claim override an
  inherited one, and the `(asymmetric P)` conflict that a strict claim raises instead.

  The running example is the one that makes the semantics necessary: `(largerThan dog
  cat)` reaches a golden retriever and a maine coon, and it also reaches a *chihuahua*
  and a maine coon, where it is false.  Which of those two the KB gets is decided by
  how the general claim was asserted, not by the vocabulary — known-true content is a
  fixed background that a contrary specific claim contradicts, a default is a
  generality a specific claim is entitled to override."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.inherit :as inherit]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- kinds!
  "dog ⊃ {golden_retriever chihuahua}, cat ⊃ {maine_coon siamese}."
  [kb {:keys [dog cat gr chi mc sia]}]
  (v/with-deferred-settle kb
    (doseq [[sub sup] [[gr dog] [chi dog] [mc cat] [sia cat]]]
      (v/assert kb (list 'genl sub sup) 'UniverseContext))))

(defn- preserving! [kb pred]
  (v/with-deferred-settle kb
    (v/assert kb (list 'asymmetric pred) 'UniverseContext)
    (v/assert kb (list 'argPreserving pred 1 'genl) 'UniverseContext)
    (v/assert kb (list 'argPreserving pred 2 'genl) 'UniverseContext)))

;; ---- the inheritance itself ----------------------------------------------

(tu/deftest-kb a-claim-about-two-kinds-reaches-their-subkinds
  (tu/with-terms [dog_t cat_t golden_retriever_t maine_coon_t chihuahua_t siamese_t largerThan]
    (kinds! kb {:dog dog_t :cat cat_t :gr golden_retriever_t
                :chi chihuahua_t :mc maine_coon_t :sia siamese_t})
    (preserving! kb largerThan)
    (v/assert kb (list largerThan dog_t cat_t) 'UniverseContext)
    (testing "both positions inherit, together and singly"
      (is (v/ask? kb (list largerThan golden_retriever_t maine_coon_t) 'UniverseContext))
      (is (v/ask? kb (list largerThan golden_retriever_t cat_t) 'UniverseContext))
      (is (v/ask? kb (list largerThan dog_t maine_coon_t) 'UniverseContext))
      (is (v/ask? kb (list largerThan dog_t cat_t) 'UniverseContext)))
    (testing "and it does not run backwards, or sideways to an unrelated kind"
      (is (not (v/ask? kb (list largerThan maine_coon_t golden_retriever_t) 'UniverseContext)))
      (is (not (v/ask? kb (list largerThan cat_t dog_t) 'UniverseContext))))))

(tu/deftest-kb no-declaration-means-no-inheritance
  ;; The default for every predicate: a claim about two kinds says nothing about their
  ;; subkinds until someone says it does.
  (tu/with-terms [dog_t cat_t golden_retriever_t maine_coon_t chihuahua_t siamese_t largerThan]
    (kinds! kb {:dog dog_t :cat cat_t :gr golden_retriever_t
                :chi chihuahua_t :mc maine_coon_t :sia siamese_t})
    (v/assert kb (list largerThan dog_t cat_t) 'UniverseContext)
    (is (v/ask? kb (list largerThan dog_t cat_t) 'UniverseContext))
    (is (not (v/ask? kb (list largerThan golden_retriever_t maine_coon_t) 'UniverseContext)))
    (is (nil? (inherit/verdict kb (list largerThan golden_retriever_t maine_coon_t)
                               'UniverseContext)))))

(tu/deftest-kb one-position-can-be-preserved-without-the-other
  (tu/with-terms [dog_t cat_t golden_retriever_t maine_coon_t chihuahua_t siamese_t chases]
    (kinds! kb {:dog dog_t :cat cat_t :gr golden_retriever_t
                :chi chihuahua_t :mc maine_coon_t :sia siamese_t})
    (v/assert kb (list 'argPreserving chases 1 'genl) 'UniverseContext)
    (v/assert kb (list chases dog_t cat_t) 'UniverseContext)
    (is (v/ask? kb (list chases golden_retriever_t cat_t) 'UniverseContext))
    (is (not (v/ask? kb (list chases dog_t maine_coon_t) 'UniverseContext))
        "position 2 was not declared, so it is pinned")))

;; ---- the relation is a parameter -----------------------------------------

(tu/deftest-kb the-preserved-relation-need-not-be-genl
  ;; `(argPreserving P n R)` names R.  Here it is an ordinary declared-transitive
  ;; predicate over individuals, with no types in sight.
  (tu/with-terms [partOf needsMaintenance Car Engine Piston]
    (v/with-deferred-settle kb
      (v/assert kb (list 'transitive partOf) 'UniverseContext)
      (v/assert kb (list partOf Engine Car) 'UniverseContext)
      (v/assert kb (list partOf Piston Engine) 'UniverseContext)
      (v/assert kb (list 'argPreserving needsMaintenance 1 partOf) 'UniverseContext)
      (v/assert kb (list needsMaintenance Car) 'UniverseContext))
    (testing "one hop and two, through the transitive relation that was named"
      (is (v/ask? kb (list needsMaintenance Engine) 'UniverseContext))
      (is (v/ask? kb (list needsMaintenance Piston) 'UniverseContext)))
    (testing "and not upward"
      (is (not (v/ask? kb (list needsMaintenance 'TmpUnrelatedThing) 'UniverseContext))))))

(tu/deftest-kb the-inverse-form-reads-the-relation-backwards
  ;; So the other direction never needs an inverse predicate declared for its own sake.
  (tu/with-terms [dog_t cat_t golden_retriever_t maine_coon_t chihuahua_t siamese_t
                  hasMemberSomewhere Earth]
    (kinds! kb {:dog dog_t :cat cat_t :gr golden_retriever_t
                :chi chihuahua_t :mc maine_coon_t :sia siamese_t})
    (v/assert kb (list 'argPreservingInverse hasMemberSomewhere 1 'genl) 'UniverseContext)
    (v/assert kb (list hasMemberSomewhere chihuahua_t Earth) 'UniverseContext)
    (is (v/ask? kb (list hasMemberSomewhere dog_t Earth) 'UniverseContext)
        "upward: a subkind's claim reaches the kind")
    (is (not (v/ask? kb (list hasMemberSomewhere siamese_t Earth) 'UniverseContext))
        "but not back down to a sibling")))

(tu/deftest-kb a-relation-nobody-declared-transitive-is-refused
  ;; The declaration's reach is walked to a **fixpoint**, so naming a relation that was
  ;; never said to compose would manufacture transitivity for it: two hops of `begat`
  ;; licensing a claim only one hop was ever evidence for.  `(argIsa argPreserving 3
  ;; transitivePredicate)` cannot say so — argIsa is open-world, so it bites for a
  ;; relation carrying some other type and waves through the one carrying none — and the
  ;; second is the common authoring order.  Both spellings must reach the same outcome.
  (tu/with-terms [cursed begat sired A B D]
    (doseq [[what rel] [["untyped" begat] ["typed" sired]]]
      (when (= "typed" what)
        (v/assert kb (list 'binaryPredicate sired) 'UniverseContext))
      (let [e (try (v/assert kb (list 'argPreserving cursed 1 rel) 'UniverseContext)
                   nil
                   (catch clojure.lang.ExceptionInfo e e))]
        (is (some? e) (str what " relation: the declaration is refused"))
        (is (= :not-well-formed (:type (ex-data e))) what)))
    (testing "nothing was stored, so no closure is walked"
      (v/with-deferred-settle kb
        (v/assert kb (list begat A B) 'UniverseContext)
        (v/assert kb (list begat B D) 'UniverseContext)
        (v/assert kb (list cursed D) 'UniverseContext))
      (is (not (v/ask? kb (list cursed A) 'UniverseContext)))
      (is (not (v/ask? kb (list cursed B) 'UniverseContext))))
    (testing "declaring the transitivity first admits it, and then it walks"
      (v/assert kb (list 'transitive begat) 'UniverseContext)
      (is (integer? (v/assert kb (list 'argPreserving cursed 1 begat) 'UniverseContext)))
      (is (v/ask? kb (list cursed B) 'UniverseContext) "one hop")
      (is (v/ask? kb (list cursed A) 'UniverseContext) "two"))))

(tu/deftest-kb the-declaration-is-about-a-relation-however-that-relation-is-written
  ;; The inheriting relation is held to what `argIsa`'s first argument is held to, and
  ;; for the same reasons: a function is spelled like an individual, and a relation can
  ;; be *denoted* by a NAT rather than named.  A `nm/individual?` test gets this exactly
  ;; backwards — a compound is not an individual, so it refuses the conventional
  ;; CapitalCamelCase spelling and waves the exotic one through.
  (tu/with-terms [Milli inheritsAlong chases]
    (v/assert kb (list 'transitive inheritsAlong) 'UniverseContext)
    (testing "a CapitalCamelCase relation — a function name — is admitted, as argIsa's is"
      (is (integer? (v/assert kb (list 'argIsa Milli 1 'thing) 'UniverseContext)))
      (is (integer? (v/assert kb (list 'argPreserving Milli 1 inheritsAlong)
                              'UniverseContext))))
    (testing "and so is a relation a NAT denotes"
      (is (integer? (v/assert kb (list 'argPreserving (list Milli 'thing) 1 inheritsAlong)
                              'UniverseContext))))
    (testing "but the relation preserved *along* stays a symbol: the reach walk builds
              (R x ?v) from it, and there is no transitivity to read off a compound"
      (let [e (try (v/assert kb (list 'argPreserving chases 1 (list Milli 'thing))
                             'UniverseContext)
                   nil
                   (catch clojure.lang.ExceptionInfo e e))]
        (is (some? e))
        (is (= :not-well-formed (:type (ex-data e))))))))

(tu/deftest-kb a-self-tuple-is-not-a-claim-against-itself
  ;; At `[a a]` the converse of `(P a b)` *is* `(P a b)`, so reading it as opposition
  ;; would file one sentex on both sides and report a dilemma the KB does not hold —
  ;; `contradictions` says nothing about it, and neither should this.
  (tu/with-terms [outranks Ann]
    (v/with-deferred-settle kb
      (v/assert kb (list 'asymmetric outranks) 'UniverseContext)
      (v/assert kb (list 'argPreserving outranks 1 'genl) 'UniverseContext)
      (v/assert kb (list 'argPreserving outranks 2 'genl) 'UniverseContext)
      (v/assert kb (list outranks Ann Ann) 'UniverseContext))
    (is (empty? (v/contradictions kb)) "the KB reports no clash here")
    (is (= :for (inherit/verdict kb (list outranks Ann Ann) 'UniverseContext))
        "so the one believed claim is what bears on it")
    (testing "a converse at a tuple of two different terms still denies"
      (tu/with-terms [Bob]
        (v/assert kb (list outranks Bob Ann) 'UniverseContext)
        (is (= :against (inherit/verdict kb (list outranks Ann Bob) 'UniverseContext))
            "nothing states (outranks Ann Bob), and its mirror is believed")
        (testing "and once both directions are believed, that is the dilemma"
          (v/assert kb (list outranks Ann Bob) 'UniverseContext)
          (is (= :ambiguous (inherit/verdict kb (list outranks Ann Bob)
                                             'UniverseContext))))))))

(tu/deftest-kb the-transitivity-licence-is-read-from-the-asking-context
  ;; `usable-relation?` reads `(transitive R)` from the vantage, exactly as the
  ;; declaration itself is read: a transitivity some context this one cannot see
  ;; states is not a licence it holds.
  ;;
  ;; The pair lives here rather than in `context_scoping_test` because it cannot be
  ;; built on a KB carrying CoreContext: `transitive` is a `decontextualizedPredicate`
  ;; there, so every declaration is lifted into UniverseContext and every context sees
  ;; it (that is the *control*, and it is stated over there).  This KB has no such
  ;; declaration, so nothing lifts and the scoped read is observable.
  (tu/with-terms [cursed3 begat3 A3 B3 AContext BContext]
    (v/assert kb (list 'genlContext AContext 'UniverseContext) 'UniverseContext)
    (v/assert kb (list 'genlContext BContext 'UniverseContext) 'UniverseContext)
    (v/assert kb (list 'transitive begat3) AContext)
    (is (integer? (v/assert kb (list 'argPreserving cursed3 1 begat3) BContext))
        "admitted: the structural check asks whether the relation is transitive at all,
         and leaves what this writer may do with it to the read")
    (v/assert kb (list begat3 A3 B3) BContext)
    (v/assert kb (list cursed3 B3) BContext)
    (is (not (v/ask? kb (list cursed3 A3) BContext))
        "B holds the claim and the edge, and no licence to walk the relation")
    (testing "and the same declaration walks once the licence is where B can see it"
      (v/assert kb (list 'transitive begat3) 'UniverseContext)
      (is (v/ask? kb (list cursed3 A3) BContext)))))

(tu/deftest-kb withdrawing-the-transitivity-withdraws-the-inheritance
  ;; Read at use and not only at assert: the declaration is still stored, but a relation
  ;; nobody currently says composes is one whose reach we have no right to close.
  (tu/with-terms [cursed begat A B D]
    (v/with-deferred-settle kb
      (v/assert kb (list 'transitive begat) 'UniverseContext)
      (v/assert kb (list 'argPreserving cursed 1 begat) 'UniverseContext)
      (v/assert kb (list begat A B) 'UniverseContext)
      (v/assert kb (list begat B D) 'UniverseContext)
      (v/assert kb (list cursed D) 'UniverseContext))
    (is (v/ask? kb (list cursed A) 'UniverseContext))
    (v/retract! kb (v/handle-of kb (list 'transitive begat) 'UniverseContext))
    (is (not (v/ask? kb (list cursed A) 'UniverseContext)))
    (is (nil? (inherit/verdict kb (list cursed A) 'UniverseContext))
        "the position is not walked at all, so the predicate inherits nothing")
    (is (v/ask? kb (list cursed D) 'UniverseContext) "the stated claim is untouched")))

;; ---- the scope: kinds, and not their members -----------------------------

(tu/deftest-kb preservation-along-genl-stays-at-the-level-of-kinds
  ;; `genl` relates types, so `(largerThan dog cat)` reaches the subkinds and stops.
  ;; It says nothing about Rex and Whiskers, and that silence is the semantics rather
  ;; than a gap: `relationKind` is a disjointMetatype over `typeRelationPredicate` and
  ;; `instanceRelationPredicate`, so one predicate symbol relates kinds *or* instances
  ;; and never both.  Preservation moves an *argument* along a relation; the predicate
  ;; and the level it relates at are left alone.  Crossing the line links two
  ;; predicates and has a quantifier reading to pin down — `typeToInstancePred`, which
  ;; the engine does not act on.
  (tu/with-terms [dog_t cat_t golden_retriever_t maine_coon_t chihuahua_t siamese_t
                  largerThan Rex Whiskers]
    (kinds! kb {:dog dog_t :cat cat_t :gr golden_retriever_t
                :chi chihuahua_t :mc maine_coon_t :sia siamese_t})
    (v/with-deferred-settle kb
      (v/assert kb (list golden_retriever_t Rex) 'UniverseContext)
      (v/assert kb (list maine_coon_t Whiskers) 'UniverseContext)
      (v/assert kb (list 'argPreserving largerThan 1 'genl) 'UniverseContext)
      (v/assert kb (list 'argPreserving largerThan 2 'genl) 'UniverseContext)
      (v/assert kb (list largerThan dog_t cat_t) 'UniverseContext))
    (is (v/ask? kb (list largerThan golden_retriever_t maine_coon_t) 'UniverseContext)
        "the subkinds")
    (is (not (v/ask? kb (list largerThan Rex Whiskers) 'UniverseContext))
        "and not their members")
    (is (nil? (inherit/verdict kb (list largerThan Rex Whiskers) 'UniverseContext))
        "nothing bears on the pair at all — it is not an ambiguity, it is silence")))

(tu/deftest-kb two-declarations-at-one-position-union-their-reaches
  ;; Each declaration independently licenses the claim, so a position declared twice
  ;; reaches what either reaches — rather than the second one filed silently replacing
  ;; the first.
  (tu/with-terms [partOf locatedIn needsAttention Car Engine Garage Bike]
    (v/with-deferred-settle kb
      (v/assert kb (list 'transitive partOf) 'UniverseContext)
      (v/assert kb (list 'transitive locatedIn) 'UniverseContext)
      (v/assert kb (list partOf Engine Car) 'UniverseContext)
      (v/assert kb (list locatedIn Bike Garage) 'UniverseContext)
      (v/assert kb (list 'argPreserving needsAttention 1 partOf) 'UniverseContext)
      (v/assert kb (list 'argPreserving needsAttention 1 locatedIn) 'UniverseContext)
      (v/assert kb (list needsAttention Car) 'UniverseContext)
      (v/assert kb (list needsAttention Garage) 'UniverseContext))
    (is (v/ask? kb (list needsAttention Engine) 'UniverseContext)
        "the first declaration reaches, down partOf")
    (is (v/ask? kb (list needsAttention Bike) 'UniverseContext)
        "and so does the second, along locatedIn — from the same argument position")))

;; ---- specificity: the stated claim overrides the inherited one -----------

(tu/deftest-kb a-specific-default-claim-undercuts-the-general-one
  (tu/with-terms [dog_t cat_t golden_retriever_t maine_coon_t chihuahua_t siamese_t
                  typicallyLargerThan]
    (kinds! kb {:dog dog_t :cat cat_t :gr golden_retriever_t
                :chi chihuahua_t :mc maine_coon_t :sia siamese_t})
    (preserving! kb typicallyLargerThan)
    (v/assert kb (list typicallyLargerThan dog_t cat_t) 'UniverseContext)   ; :default
    (is (v/ask? kb (list typicallyLargerThan chihuahua_t maine_coon_t) 'UniverseContext)
        "inherited before anything contradicts it")
    (testing "the more specific contrary claim is accepted, not refused"
      (is (integer? (v/assert kb (list typicallyLargerThan maine_coon_t chihuahua_t)
                              'UniverseContext))))
    (testing "and it wins for that pair"
      (is (v/ask? kb (list typicallyLargerThan maine_coon_t chihuahua_t) 'UniverseContext))
      (is (not (v/ask? kb (list typicallyLargerThan chihuahua_t maine_coon_t) 'UniverseContext))))
    (testing "without defeating the general claim or leaving anything to arbitrate"
      (is (v/ask? kb (list typicallyLargerThan dog_t cat_t) 'UniverseContext))
      (is (empty? (v/contradictions kb)))
      (is (empty? (v/conflicts kb))))
    (testing "and untouched pairs still inherit"
      (is (v/ask? kb (list typicallyLargerThan golden_retriever_t siamese_t) 'UniverseContext))
      (is (v/ask? kb (list typicallyLargerThan golden_retriever_t maine_coon_t) 'UniverseContext)))))

(tu/deftest-kb an-explicit-negation-undercuts-the-same-way
  (tu/with-terms [dog_t cat_t golden_retriever_t maine_coon_t chihuahua_t siamese_t
                  typicallyLargerThan]
    (kinds! kb {:dog dog_t :cat cat_t :gr golden_retriever_t
                :chi chihuahua_t :mc maine_coon_t :sia siamese_t})
    (v/assert kb (list 'argPreserving typicallyLargerThan 1 'genl) 'UniverseContext)
    (v/assert kb (list 'argPreserving typicallyLargerThan 2 'genl) 'UniverseContext)
    (v/assert kb (list typicallyLargerThan dog_t cat_t) 'UniverseContext)
    (is (v/ask? kb (list typicallyLargerThan chihuahua_t maine_coon_t) 'UniverseContext))
    (v/assert kb (list 'not (list typicallyLargerThan chihuahua_t maine_coon_t)) 'UniverseContext)
    (is (not (v/ask? kb (list typicallyLargerThan chihuahua_t maine_coon_t) 'UniverseContext))
        "the negation is the most specific claim about that pair")
    (is (v/ask? kb (list typicallyLargerThan golden_retriever_t maine_coon_t) 'UniverseContext)
        "and says nothing about any other")))

(tu/deftest-kb a-claim-and-its-negation-at-one-tuple-are-not-a-clean-for
  ;; The KB holds both `P` and `(not P)` of one pair, reports the dilemma through
  ;; `contradictions`, and believes both at `:default`.  Every probe per tuple is
  ;; therefore made: taking whichever answered first would read this as a clean `:for`
  ;; and hand `verdict` a decision the engine, looking at the same two sentexes,
  ;; refuses to make.
  (tu/with-terms [dog_t cat_t golden_retriever_t maine_coon_t chihuahua_t siamese_t
                  rankedOver]
    (kinds! kb {:dog dog_t :cat cat_t :gr golden_retriever_t
                :chi chihuahua_t :mc maine_coon_t :sia siamese_t})
    (v/with-deferred-settle kb
      (v/assert kb (list 'argPreserving rankedOver 1 'genl) 'UniverseContext)
      (v/assert kb (list 'argPreserving rankedOver 2 'genl) 'UniverseContext)
      (v/assert kb (list rankedOver dog_t cat_t) 'UniverseContext)
      (v/assert kb (list 'not (list rankedOver dog_t cat_t)) 'UniverseContext))
    (is (seq (v/contradictions kb))
        "the engine represents the pair rather than deciding it")
    (is (= :ambiguous (inherit/verdict kb (list rankedOver dog_t cat_t) 'UniverseContext))
        "and so does this, about the same two sentexes")
    (is (= :ambiguous (inherit/verdict kb (list rankedOver chihuahua_t maine_coon_t)
                                       'UniverseContext))
        "the pair the contradictory tuple reaches inherits the ambiguity, not the :for")
    (is (not (v/ask? kb (list rankedOver chihuahua_t maine_coon_t) 'UniverseContext))
        "so nothing is answered for the inherited pair")
    (is (v/ask? kb (list rankedOver dog_t cat_t) 'UniverseContext)
        "while the stated pair is still answered — by the fact prover, which reads the
         believed positive sentex and is not this prover")))

(tu/deftest-kb incomparable-claims-are-not-decided
  ;; Two claims that disagree and neither of which is more specific.  The engine's
  ;; stance on an unresolvable clash is to represent it, so the prover answers nothing
  ;; rather than picking a side.
  (tu/with-terms [dog_t cat_t golden_retriever_t maine_coon_t chihuahua_t siamese_t
                  pet_t predator_t rankedOver]
    (kinds! kb {:dog dog_t :cat cat_t :gr golden_retriever_t
                :chi chihuahua_t :mc maine_coon_t :sia siamese_t})
    (v/with-deferred-settle kb
      (v/assert kb (list 'genl chihuahua_t pet_t) 'UniverseContext)
      (v/assert kb (list 'genl maine_coon_t predator_t) 'UniverseContext)
      (v/assert kb (list 'argPreserving rankedOver 1 'genl) 'UniverseContext)
      (v/assert kb (list 'argPreserving rankedOver 2 'genl) 'UniverseContext)
      (v/assert kb (list rankedOver dog_t cat_t) 'UniverseContext)
      (v/assert kb (list 'not (list rankedOver pet_t predator_t)) 'UniverseContext))
    (is (= :ambiguous (inherit/verdict kb (list rankedOver chihuahua_t maine_coon_t)
                                       'UniverseContext))
        "[dog cat] and [pet predator] both reach the pair and neither is below the other")
    (is (not (v/ask? kb (list rankedOver chihuahua_t maine_coon_t) 'UniverseContext))
        "so nothing is answered")))

;; ---- strict: the same shape, refused instead of overridden ---------------

(tu/deftest-kb a-contrary-claim-against-known-true-content-is-refused
  (tu/with-terms [dog_t cat_t golden_retriever_t maine_coon_t chihuahua_t siamese_t largerThan]
    (kinds! kb {:dog dog_t :cat cat_t :gr golden_retriever_t
                :chi chihuahua_t :mc maine_coon_t :sia siamese_t})
    (preserving! kb largerThan)
    (v/assert kb (list largerThan dog_t cat_t) 'UniverseContext {:strength :monotonic})
    (testing "the inherited claim is as binding as the one that was written"
      (let [e (try (v/assert kb (list largerThan maine_coon_t chihuahua_t) 'UniverseContext)
                   nil
                   (catch clojure.lang.ExceptionInfo e e))]
        (is (some? e))
        (is (= :asymmetric (:type (ex-data e))))
        (is (= (list largerThan dog_t cat_t) (:opposing (ex-data e)))
            "the message names the general claim actually responsible")))
    (testing "and so is the plain converse of a directly-stated one"
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list largerThan cat_t dog_t) 'UniverseContext))))
    (testing "nothing was stored by either refusal"
      (is (not (v/ask? kb (list largerThan maine_coon_t chihuahua_t) 'UniverseContext)))
      (is (v/ask? kb (list largerThan chihuahua_t maine_coon_t) 'UniverseContext)))))

(tu/deftest-kb asymmetry-alone-catches-a-converse-with-no-inheritance
  ;; The check does not need a preserved position: an asymmetric predicate's converse
  ;; contradicts it wherever both are known true.
  (tu/with-terms [dog_t cat_t largerThan]
    (v/assert kb (list 'asymmetric largerThan) 'UniverseContext)
    (v/assert kb (list largerThan dog_t cat_t) 'UniverseContext {:strength :monotonic})
    (is (thrown? clojure.lang.ExceptionInfo
                 (v/assert kb (list largerThan cat_t dog_t) 'UniverseContext)))))

(tu/deftest-kb a-default-general-claim-does-not-refuse-anything
  ;; The whole strict/typical difference, isolated: same vocabulary, same declarations,
  ;; only the strength of the general claim differs.
  (tu/with-terms [dog_t cat_t golden_retriever_t maine_coon_t chihuahua_t siamese_t largerThan]
    (kinds! kb {:dog dog_t :cat cat_t :gr golden_retriever_t
                :chi chihuahua_t :mc maine_coon_t :sia siamese_t})
    (preserving! kb largerThan)
    (v/assert kb (list largerThan dog_t cat_t) 'UniverseContext)     ; :default, not monotonic
    (is (integer? (v/assert kb (list largerThan maine_coon_t chihuahua_t) 'UniverseContext))
        "accepted, where the monotonic version refuses")))

;; ---- order independence ---------------------------------------------------

(defn- admits-converse?
  "State `(P a b)` in a super-context and a sub-context at the two given strengths, in
  the given order, then report whether the converse is admitted from the sub-context."
  [kb {:keys [pred a b super sub order]}]
  ;; the declarations below live in UniverseContext, and the asymmetry check reads
  ;; them from the asserting context's cone — so the lattice is wired below it
  (v/assert kb (list 'genlContext super 'UniverseContext) 'UniverseContext)
  (v/assert kb (list 'genlContext sub super) 'UniverseContext)
  (v/assert kb (list 'asymmetric pred) 'UniverseContext)
  (v/assert kb (list 'argPreserving pred 1 'genl) 'UniverseContext)
  (v/assert kb (list 'argPreserving pred 2 'genl) 'UniverseContext)
  (doseq [[where strength] order]
    (v/assert kb (list pred a b) (if (= where :super) super sub) {:strength strength}))
  (try (v/assert kb (list pred b a) sub) true
       (catch clojure.lang.ExceptionInfo e
         ;; **Only the asymmetry check's refusal counts as one.**  Every assertion below
         ;; is `(is (false? …))`, so mapping any ex-info to false would let a `:naming`
         ;; or `:arg-type` regression read as the intended refusal — the converse would
         ;; be "refused" for a reason that has nothing to do with `(asymmetric P)`.
         ;; Anything else is rethrown, which is an error rather than a silent pass.
         (if (= :asymmetric (:type (ex-data e)))
           false
           (throw e)))))

(tu/deftest-kb the-strongest-visible-claim-decides-not-the-first-one-stored
  ;; One sentence, two visible contexts, two strengths.  `:class` decides whether the
  ;; asymmetry check refuses, so reading it off whichever handle `matches-visible`
  ;; happened to yield first would key an *admission* on arrival order — and handles
  ;; are allocated in assertion order.
  ;;
  ;; Every combination of (which context holds the monotonic claim) x (which was
  ;; asserted first) must give the same answer, and it must be the strong one: a claim
  ;; that is known true anywhere the asking context can see is a fixed background.
  (doseq [[i strong] (map-indexed vector [:super :sub])
          [j first-where] (map-indexed vector [:super :sub])]
    (tu/with-terms [dog_t cat_t largerThan SuperContext SubContext]
      (v/assert kb (list 'genl dog_t 'thing) 'UniverseContext)
      (v/assert kb (list 'genl cat_t 'thing) 'UniverseContext)
      (let [strength (fn [w] (if (= w strong) :monotonic :default))
            order    (if (= first-where :super)
                       [[:super (strength :super)] [:sub (strength :sub)]]
                       [[:sub (strength :sub)] [:super (strength :super)]])]
        (is (false? (admits-converse? kb {:pred largerThan :a dog_t :b cat_t
                                          :super SuperContext :sub SubContext
                                          :order order}))
            (str "monotonic in " (name strong) ", " (name first-where) " asserted first ["
                 i j "]: the converse of known-true content is refused either way"))))))

;; ---- the exception re-check trigger ---------------------------------------

(tu/deftest-kb a-genl-edge-among-the-arguments-rechecks-an-exception
  ;; `ArgPreservingProver` answers a level-6 exception query by walking the *arguments'*
  ;; genl closure, so an edge between two types can flip an exception stated over a
  ;; predicate neither type appears in.  The predicate-keyed re-check cannot see that;
  ;; without the argument-side trigger the firings that predate the edge keep a
  ;; conclusion the firings after it correctly drop.
  (tu/with-terms [dog_t cat_t maine_coon_t chihuahua_t largerThan fitsIn Tiny Other]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genl maine_coon_t cat_t) 'UniverseContext)
      (v/assert kb (list 'argPreserving largerThan 1 'genl) 'UniverseContext)
      (v/assert kb (list 'argPreserving largerThan 2 'genl) 'UniverseContext)
      (v/assert kb (list largerThan dog_t cat_t) 'UniverseContext))
    ;; a chihuahua fits in the box, unless a chihuahua is larger than a maine coon
    (v/assert kb (list 'exceptWhen (list largerThan chihuahua_t maine_coon_t)
                       (list 'set/defaultRule
                             (list 'implies (list 'and (list chihuahua_t '?x))
                                   (list fitsIn '?x))))
              'UniverseContext)
    (v/assert kb (list chihuahua_t Tiny) 'UniverseContext)
    (is (seq (v/sentexes-matching kb (list fitsIn Tiny) 'UniverseContext))
        "baseline: the exception does not hold, so the rule fires")

    ;; the edge makes the exception hold, by inheritance from (largerThan dog cat)
    (v/assert kb (list 'genl chihuahua_t dog_t) 'UniverseContext)
    (is (v/ask? kb (list largerThan chihuahua_t maine_coon_t) 'UniverseContext)
        "the exception's query is now answered by argument preservation")
    (is (empty? (v/sentexes-matching kb (list fitsIn Tiny) 'UniverseContext))
        "so the conclusion that predates the edge is withdrawn")

    (v/assert kb (list chihuahua_t Other) 'UniverseContext)
    (is (empty? (v/sentexes-matching kb (list fitsIn Other) 'UniverseContext))
        "and a fresh firing agrees with it")))

(ns vaelii-bridge.tests
  "Vaelii integration tests. Muffet is the canonical dog,
   after Ken Murray's poodle from the Cyc unit tests.

   Every test runs under both :refuse and :arbitrate constraint policies.
   Pure derivation tests use deftest-both-modes; constraint-sensitive tests
   are split into explicit -refuse and -arbitrate deftest functions."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii-bridge.utils :as bridge]
            [vaelii.core :as v]
            [vaelii.impl.rules :as vr]
            [vaelii.impl.starter :as starter]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded starter/load-into))
(use-fixtures :each (tu/neutral))

(defmacro with-literal-fixtures
  "Document stable, behavior-scoped fixture symbols without pretending quoted
   sentexes receive lexical substitution. tu/neutral retracts each test's added
   premises; these identities are intentionally stable literals with test-scoped
   facts."
  [syms & body]
  (assert (and (vector? syms) (every? simple-symbol? syms))
          "with-literal-fixtures takes a vector of plain symbols")
  `(do ~@body))

(defmacro deftest-both-modes
  "Generates two deftest functions — one for :refuse, one for :arbitrate — that
   run the body on a fork of the fixture KB with the named constraint policy.
   Use for pure derivation tests that should pass identically under both modes."
  [name & body]
  `(do
     (deftest ~(symbol (str name "-refuse"))
       (let [~'kb (v/fork tu/*kb* {:constraints :refuse})]
         ~@body))
     (deftest ~(symbol (str name "-arbitrate"))
       (let [~'kb (v/fork tu/*kb* {:constraints :arbitrate})]
         ~@body))))

(defn first-if-singleton [coll]
  (let [s (seq coll)]
    (when (and s (nil? (next s)))
      (first s))))

(defn sentex-matching [kb sentence context]
  (first-if-singleton (v/sentexes-matching kb sentence context)))

(def ^:private extends-to-future-generator
  '(set/forwardRule
    (implies
     (extendsToFuture ?pred)
     (set/forwardRule
      (implies
       (and (before ?early ?late)
            (?pred ?x ?y))
       (ist ?late (?pred ?x ?y)))))))

(def ^:private former-version-of-generator
  '(set/forwardRule
    (implies
     (formerVersionOf ?pred ?formerPred)
     (set/forwardRule
      (implies
       (and (before ?early ?late)
            (?pred ?x ?y))
       (ist ?late (?formerPred ?x ?y)))))))

(defn- assert-temporal-generators!
  [kb]
  (v/assert kb extends-to-future-generator 'CxUniverse)
  (v/assert kb former-version-of-generator 'CxUniverse))

(defn- stamped-temporal-rule
  "Returns the unique stamped temporal rule with the requested concrete functors."
  [kb source-pred conclusion-pred]
  (first-if-singleton
   (filter
    #(and (not (vr/generator-sentex? %))
          (= #{'before source-pred}
             (set (vr/antecedent-predicates (:sentence %))))
          (= conclusion-pred (vr/consequent-predicate (:sentence %))))
    (filter :antecedent (v/sentexes-in-context kb 'CxUniverse)))))

;; ============================================================
;; PURE DERIVATION TESTS
;; These pass identically under both :refuse and :arbitrate.
;; ============================================================
(deftest-both-modes meta-predicate-extends-to-future
  (with-literal-fixtures [knows CxNineties CxPresent Alice Bob]
    ;; set up temporal contexts
    (v/assert kb '(genlCx CxNineties CxUniverse) 'CxUniverse)
    (v/assert kb '(genlCx CxPresent CxUniverse) 'CxUniverse)
    (v/assert kb '(before CxNineties CxPresent) 'CxTime)

    ;; declare predicates
    (v/assert kb '(binaryPredicate knows) 'CxCore)
    (v/assert kb '(unaryPredicate extendsToFuture) 'CxCore)

    (assert-temporal-generators! kb)

    ;; mark knows as temporally monotonic, minting its concrete lifting rule
    (let [license (v/assert kb '(extendsToFuture knows) 'CxCore)]
      (v/assert kb '(knows Alice Bob) 'CxNineties)

      (testing "the generator stamps a rule with concrete functors"
        (let [minted (stamped-temporal-rule kb 'knows 'knows)]
          (is (some? minted))
          (when minted
            (is (= #{'before 'knows}
                   (set (vr/antecedent-predicates (:sentence minted)))))
            (is (= 'knows (vr/consequent-predicate (:sentence minted))))

            (testing "knows propagates to CxPresent via extendsToFuture"
              (is (v/ask? kb '(knows Alice Bob) 'CxPresent)))

            (v/retract! kb license)
            (testing "retracting the license retracts the stamped rule and conclusion"
              (is (not (v/in? kb (:id minted))))
              (is (not (v/ask? kb '(knows Alice Bob) 'CxPresent))))))))))

(deftest-both-modes meta-predicate-extends-to-future-fill-first
  (with-literal-fixtures [knows CxEighties CxCurrent Carol Dana]
    (v/assert kb '(genlCx CxEighties CxUniverse) 'CxUniverse)
    (v/assert kb '(genlCx CxCurrent CxUniverse) 'CxUniverse)
    (v/assert kb '(before CxEighties CxCurrent) 'CxTime)
    (v/assert kb '(binaryPredicate knows) 'CxCore)
    (v/assert kb '(unaryPredicate extendsToFuture) 'CxCore)

    ;; Both the fill and the stamped rule's input precede the generator.
    (v/assert kb '(extendsToFuture knows) 'CxCore)
    (v/assert kb '(knows Carol Dana) 'CxEighties)
    (assert-temporal-generators! kb)

    (testing "a late generator sees the existing fill and temporal fact"
      (is (some? (stamped-temporal-rule kb 'knows 'knows)))
      (is (v/ask? kb '(knows Carol Dana) 'CxCurrent)))))

(deftest-both-modes meta-predicate-former-version-of
  (with-literal-fixtures [girlfriend exGirlfriend CxPrior CxPresent PartnerOne PartnerTwo]
    ;; set up temporal contexts
    (v/assert kb '(genlCx CxPrior CxUniverse) 'CxUniverse)
    (v/assert kb '(genlCx CxPresent CxUniverse) 'CxUniverse)
    (v/assert kb '(before CxPrior CxPresent) 'CxTime)

    ;; declare predicates
    (v/assert kb '(binaryPredicate girlfriend) 'CxCore)
    (v/assert kb '(binaryPredicate exGirlfriend) 'CxCore)
    (v/assert kb '(binaryPredicate formerVersionOf) 'CxCore)

    (assert-temporal-generators! kb)

    ;; register the former-version pair, minting its concrete projection rule
    (let [license (v/assert kb '(formerVersionOf girlfriend exGirlfriend) 'CxCore)]
      (v/assert kb '(girlfriend PartnerOne PartnerTwo) 'CxPrior)

      (testing "the generator stamps a rule with concrete source and target functors"
        (let [minted (stamped-temporal-rule kb 'girlfriend 'exGirlfriend)]
          (is (some? minted))
          (when minted
            (is (= #{'before 'girlfriend}
                   (set (vr/antecedent-predicates (:sentence minted)))))
            (is (= 'exGirlfriend (vr/consequent-predicate (:sentence minted))))

            (testing "exGirlfriend derives in CxPresent via formerVersionOf"
              (is (v/ask? kb '(exGirlfriend PartnerOne PartnerTwo) 'CxPresent)))

            (testing "girlfriend does not hold in CxPresent"
              (is (not (v/ask? kb '(girlfriend PartnerOne PartnerTwo) 'CxPresent))))

            (v/retract! kb license)
            (testing "retracting the license retracts the stamped rule and conclusion"
              (is (not (v/in? kb (:id minted))))
              (is (not (v/ask? kb '(exGirlfriend PartnerOne PartnerTwo)
                               'CxPresent))))))))))

(deftest-both-modes meta-predicate-former-version-of-fill-first
  (with-literal-fixtures [dating formerlyDating CxEarlier CxCurrent Pat Quinn]
    (v/assert kb '(genlCx CxEarlier CxUniverse) 'CxUniverse)
    (v/assert kb '(genlCx CxCurrent CxUniverse) 'CxUniverse)
    (v/assert kb '(before CxEarlier CxCurrent) 'CxTime)
    (v/assert kb '(binaryPredicate dating) 'CxCore)
    (v/assert kb '(binaryPredicate formerlyDating) 'CxCore)
    (v/assert kb '(binaryPredicate formerVersionOf) 'CxCore)

    ;; Both the fill and the stamped rule's input precede the generator.
    (v/assert kb '(formerVersionOf dating formerlyDating) 'CxCore)
    (v/assert kb '(dating Pat Quinn) 'CxEarlier)
    (assert-temporal-generators! kb)

    (testing "a late generator sees the existing fill and temporal fact"
      (is (some? (stamped-temporal-rule kb 'dating 'formerlyDating)))
      (is (v/ask? kb '(formerlyDating Pat Quinn) 'CxCurrent)))))

(defn- setup-relationship-vocab!
  "Define the ratified relationship predicate hierarchy."
  [kb]
  ;; predicate type hierarchy
  (v/assert kb '(unaryPredicate predicate) 'CxCore)
  (v/assert kb '(comment predicate "A predicate of any ty.") 'CxCore)
  (v/assert kb '(binaryPredicate predicateTypeByty) 'CxCore)
  (v/assert kb '(comment predicateTypeByArity "Maps an arity-specific predicate type to its arity. Derives genl under predicate and arity.") 'CxCore)
  (v/assert kb '(functional predicateTypeByArity) 'CxCore)
  (v/assert kb '(argIsa predicateTypeByArity 1 predicate) 'CxCore)
  (v/assert kb '(argIsa predicateTypeByArity 2 thing) 'CxCore)
  (v/assert kb '(comment (argIsa predicateTypeByArity 2 thing) "Should be (argQuotedIsa predicateTypeByArity 2 positiveInteger) when that vocabulary exists.") 'CxCore)
  (v/assert kb '(predicateTypeByArity unaryPredicate 1) 'CxCore)
  (v/assert kb '(predicateTypeByArity binaryPredicate 2) 'CxCore)
  (v/assert kb '(predicateTypeByArity ternaryPredicate 3) 'CxCore)

  (v/assert-rule kb
    ['(predicateTypeByArity ?pred ?arity)]
    '(genl ?pred predicate)
    'CxCore
    {:direction :forward})
  (v/assert-rule kb
    ['(predicateTypeByArity ?pred ?arity)]
    '(arity ?pred ?arity)
    'CxCore
    {:direction :forward})
  ;; partition: different predicate types are disjoint
  (v/assert-rule kb
    ['(predicateTypeByArity ?x ?a1) '(predicateTypeByArity ?y ?a2) '(different ?x ?y)]
    '(disjoint ?x ?y)
    'CxCore
    {:direction :forward})

  ;; unaryMetaPredicate — bootstrap before first use
  (v/assert kb '(unaryPredicate unaryMetaPredicate) 'CxCore)
  (v/assert kb '(comment unaryMetaPredicate "A unary predicate whose argument is itself a predicate.") 'CxCore)
  (v/assert kb '(genl unaryMetaPredicate unaryPredicate) 'CxCore)
  (v/assert-rule kb ['(unaryMetaPredicate ?pred)] '(argIsa ?pred 1 predicate) 'CxCore {:direction :forward})

  ;; symmetric vs asymmetric — mutually exclusive
  ;; (disjoint symmetricBinaryPredicate asymmetricBinaryPredicate) is derived via genl
  (v/assert kb '(disjoint symmetric asymmetric) 'CxCore)

  ;; symmetricBinaryPredicate
  ;; Two layers needed (not redundant):
  ;;   genl asents → taxonomy classification + disjoint propagation
  ;;   forward rules → instance-level behavioral effects (v's symmetric/asymmetric/transitive
  ;;     machinery reads from asserted/forward-derived property facts, not from genl-derived ones)
  (v/assert kb '(unaryMetaPredicate symmetricBinaryPredicate) 'CxCore)
  (v/assert kb '(comment symmetricBinaryPredicate "A binary predicate that is symmetric — (P x y) implies (P y x).") 'CxCore)
  (v/assert kb '(genl symmetricBinaryPredicate symmetric) 'CxCore)
  (v/assert kb '(genl symmetricBinaryPredicate binaryPredicate) 'CxCore)
  (v/assert-rule kb ['(symmetricBinaryPredicate ?p)] '(binaryPredicate ?p) 'CxCore {:direction :forward})
  (v/assert-rule kb ['(symmetricBinaryPredicate ?p)] '(symmetric ?p) 'CxCore {:direction :forward})
  (v/assert-rule kb ['(symmetric ?p) '(binaryPredicate ?p)] '(symmetricBinaryPredicate ?p) 'CxCore {:direction :forward})

  ;; asymmetricBinaryPredicate (same two-layer pattern)
  (v/assert kb '(unaryMetaPredicate asymmetricBinaryPredicate) 'CxCore)
  (v/assert kb '(comment asymmetricBinaryPredicate "A binary predicate that is asymmetric — (P x y) implies not (P y x).") 'CxCore)
  (v/assert kb '(genl asymmetricBinaryPredicate asymmetric) 'CxCore)
  (v/assert kb '(genl asymmetricBinaryPredicate binaryPredicate) 'CxCore)
  (v/assert-rule kb ['(asymmetricBinaryPredicate ?p)] '(binaryPredicate ?p) 'CxCore {:direction :forward})
  (v/assert-rule kb ['(asymmetricBinaryPredicate ?p)] '(asymmetric ?p) 'CxCore {:direction :forward})
  (v/assert-rule kb ['(asymmetric ?p) '(binaryPredicate ?p)] '(asymmetricBinaryPredicate ?p) 'CxCore {:direction :forward})

  ;; transitiveBinaryPredicate (same two-layer pattern)
  (v/assert kb '(unaryMetaPredicate transitiveBinaryPredicate) 'CxCore)
  (v/assert kb '(comment transitiveBinaryPredicate "A binary predicate that is transitive — (P x y) and (P y z) implies (P x z).") 'CxCore)
  (v/assert kb '(genl transitiveBinaryPredicate transitive) 'CxCore)
  (v/assert kb '(genl transitiveBinaryPredicate binaryPredicate) 'CxCore)
  (v/assert-rule kb ['(transitiveBinaryPredicate ?p)] '(binaryPredicate ?p) 'CxCore {:direction :forward})
  (v/assert-rule kb ['(transitiveBinaryPredicate ?p)] '(transitive ?p) 'CxCore {:direction :forward})
  (v/assert-rule kb ['(transitive ?p) '(binaryPredicate ?p)] '(transitiveBinaryPredicate ?p) 'CxCore {:direction :forward})

  ;; symmetric predicates — derives both binaryPredicate and symmetric
  (doseq [pred '[knows friendOf romanticPartnerOf marriedTo
                 relativeOf siblingOf coworkerOf roommateOf
                 nestingPartnerOf formerlyMarriedTo exPartnerOf
                 formerCoworkerOf]]
    (v/assert kb (list 'symmetricBinaryPredicate pred) 'CxCore))

  ;; asymmetric binary predicates (alterOf declared in setup-plurality-vocab!)
  (doseq [pred '[originatorOf parentOf founderOf]]
    (v/assert kb (list 'asymmetricBinaryPredicate pred) 'CxCore))
  (v/assert kb '(binaryPredicate formerVersionOf) 'CxCore)

  (v/assert kb '(unaryMetaPredicate extendsToFuture) 'CxCore)
  (v/assert kb '(ternaryPredicate relationshipLabel) 'CxCore)
  (v/assert kb '(comment relationshipLabel "Perspectival relationship label — (relationshipLabel namer named label) means namer calls their relationship with named by label. Not necessarily symmetric in arg1 and arg2.") 'CxSociety)

  ;; meta-predicate argIsas — derived via unaryMetaPredicate for generic ones
  (v/assert kb '(argIsa formerVersionOf 1 predicate) 'CxCore)
  (v/assert kb '(argIsa formerVersionOf 2 predicate) 'CxCore)
  ;; these are more specific than predicate — keep explicit argIsas
  (v/assert kb '(argIsa symmetricBinaryPredicate 1 binaryPredicate) 'CxCore)
  (v/assert kb '(argIsa asymmetricBinaryPredicate 1 binaryPredicate) 'CxCore)
  (v/assert kb '(argIsa transitiveBinaryPredicate 1 binaryPredicate) 'CxCore)
  (v/assert kb '(argIsa equivalenceRelation 1 binaryPredicate) 'CxCore)

  ;; notAssertible — derived-only predicates
  (v/assert kb '(unaryMetaPredicate notAssertible) 'CxCore)
  (v/assert kb '(comment notAssertible "May only be derived, never directly asserted. Bridge-enforced.") 'CxCore)
  (v/assert-rule kb
    ['(formerVersionOf ?pred ?formerPred)]
    '(notAssertible ?formerPred)
    'CxCore
    {:direction :forward})

  ;; comments
  (v/assert kb '(comment knows "Acquaintanceship. Top of the social predicate hierarchy; most social relations imply knows (exception: headmateOf).") 'CxSociety)
  (v/assert kb '(comment friendOf "Friendship.") 'CxSociety)
  (v/assert kb '(comment romanticPartnerOf "Romantic relationship. Umbrella term — covers dating, life partnership, and any romantic connection. Use more specific predicates (marriedTo, etc.) or relationshipLabel for precision. Genl under friendOf (optimistic — not every romance is a friendship, but we treat it so).") 'CxSociety)
  (v/assert kb '(comment marriedTo "Married. Spec of romanticPartnerOf.") 'CxSociety)
  (v/assert kb '(comment relativeOf "Family. Covers biological and chosen kinship.") 'CxSociety)
  (v/assert kb '(comment siblingOf "Siblings. Derived from shared originatorOf or asserted directly for chosen kinship.") 'CxSociety)
  (v/assert kb '(comment originatorOf "Brought the second arg into being. Common genl of parentOf (biological) and founderOf (construct).") 'CxSociety)
  (v/assert kb '(comment parentOf "Biological parent. Spec of originatorOf.") 'CxSociety)
  (v/assert kb '(comment founderOf "Founded a construct. Spec of originatorOf.") 'CxSociety)
  (v/assert kb '(comment coworkerOf "Work together.") 'CxSociety)
  (v/assert kb '(comment roommateOf "Live together. Does not imply romantic involvement.") 'CxSociety)
  (v/assert kb '(comment nestingPartnerOf "Romantic partners who live together. Derived: romanticPartnerOf AND roommateOf.") 'CxSociety)
  (v/assert kb '(comment extendsToFuture "Temporally monotonic — once true, stays true in all later contexts. Bridge meta-predicate: generates per-predicate temporal lifting rules.") 'CxCore)
  (v/assert kb '(comment formerVersionOf "The former-version relationship between predicates. Bridge meta-predicate: generates temporal projection rules that derive the former-version in later contexts.") 'CxCore)
  (v/assert kb '(functional formerVersionOf) 'CxCore)
  (assert-temporal-generators! kb)

  ;; argIsas — explicit for all predicates, even if redundant with genl
  ;; social person × person
  (doseq [pred '[knows friendOf romanticPartnerOf marriedTo
                 relativeOf siblingOf coworkerOf roommateOf
                 nestingPartnerOf formerlyMarriedTo exPartnerOf
                 formerCoworkerOf]]
    (v/assert kb (list 'argIsa pred 1 'person) 'CxSociety)
    (v/assert kb (list 'argIsa pred 2 'person) 'CxSociety))
  ;; originatorOf: person × person
  (v/assert kb '(argIsa originatorOf 1 person) 'CxSociety)
  (v/assert kb '(argIsa originatorOf 2 person) 'CxSociety)
  ;; parentOf: human × human (biological, scoped to our bridge)
  (v/assert kb '(argIsa parentOf 1 human) 'CxSociety)
  (v/assert kb '(argIsa parentOf 2 human) 'CxSociety)
  ;; founderOf: person × construct
  (v/assert kb '(argIsa founderOf 1 person) 'CxSociety)
  (v/assert kb '(argIsa founderOf 2 construct) 'CxSociety)
  ;; relationshipLabel: person × person × thing (ternary)
  (v/assert kb '(argIsa relationshipLabel 1 person) 'CxSociety)
  (v/assert kb '(argIsa relationshipLabel 2 person) 'CxSociety)
  (v/assert kb '(argIsa relationshipLabel 3 thing) 'CxSociety)
  (v/assert kb '(comment (argIsa relationshipLabel 3 thing) "Should be (argQuotedIsa relationshipLabel 3 string) when that vocabulary exists.") 'CxSociety)

  ;; dwellsIn — spec of starter livesIn
  (v/assert kb '(binaryPredicate dwellsIn) 'CxCore)
  (v/assert kb '(genl dwellsIn livesIn) 'CxSociety)
  (v/assert kb '(comment dwellsIn "Lives in a specific dwelling. Spec of livesIn restricted to human × dwelling. Derives roommateOf for co-dwellers.") 'CxSociety)
  (v/assert kb '(unaryPredicate dwelling) 'CxCore)
  (v/assert kb '(comment dwelling "A residential unit — house, apartment, room. Not a city, country, or arbitrary building.") 'CxCore)
  (v/assert kb '(argIsa dwellsIn 1 human) 'CxSociety)
  (v/assert kb '(argIsa dwellsIn 2 dwelling) 'CxSociety)
  ;; derive roommateOf from shared dwellsIn
  (v/assert-rule kb
    ['(dwellsIn ?x ?d) '(dwellsIn ?y ?d) '(different ?x ?y)]
    '(roommateOf ?x ?y)
    'CxUniverse
    {:direction :forward})

  ;; equivalenceRelation definition — genl for forward, rule for converse
  (v/assert kb '(unaryMetaPredicate equivalenceRelation) 'CxCore)
  (v/assert kb '(comment equivalenceRelation "An equivalence relation: symmetric, transitive, and reflexive.") 'CxCore)
  (v/assert kb '(genl equivalenceRelation symmetric) 'CxCore)
  (v/assert kb '(genl equivalenceRelation transitive) 'CxCore)
  (v/assert kb '(genl equivalenceRelation reflexive) 'CxCore)
  (v/assert-rule kb
    ['(symmetric ?p) '(transitive ?p) '(reflexive ?p)]
    '(equivalenceRelation ?p)
    'CxCore
    {:direction :forward})

  ;; genl hierarchy: knows at the top
  (v/assert kb '(genl friendOf knows) 'CxUniverse)
  (v/assert kb '(genl relativeOf knows) 'CxUniverse)
  (v/assert kb '(genl coworkerOf knows) 'CxUniverse)
  (v/assert kb '(genl roommateOf knows) 'CxUniverse)
  ;; romanticPartnerOf under friendOf (optimistic ontology)
  (v/assert kb '(genl romanticPartnerOf friendOf) 'CxUniverse)
  ;; marriedTo under romanticPartnerOf
  (v/assert kb '(genl marriedTo romanticPartnerOf) 'CxUniverse)
  ;; originatorOf under relativeOf
  (v/assert kb '(genl originatorOf relativeOf) 'CxUniverse)
  ;; parentOf and founderOf under originatorOf
  (v/assert kb '(genl parentOf originatorOf) 'CxUniverse)
  (v/assert kb '(genl founderOf originatorOf) 'CxUniverse)
  ;; siblingOf under relativeOf
  (v/assert kb '(genl siblingOf relativeOf) 'CxUniverse)

  ;; formerVersionOf pairs
  (v/assert kb '(formerVersionOf marriedTo formerlyMarriedTo) 'CxCore)
  (v/assert kb '(formerVersionOf romanticPartnerOf exPartnerOf) 'CxCore)
  (v/assert kb '(formerVersionOf coworkerOf formerCoworkerOf) 'CxCore)
  (v/assert kb '(comment formerlyMarriedTo "Formerly married. Derived via temporal projection from marriedTo.") 'CxSociety)
  (v/assert kb '(comment exPartnerOf "Former romantic partner. Derived via temporal projection from romanticPartnerOf.") 'CxSociety)
  (v/assert kb '(comment formerCoworkerOf "Former coworker. Derived via temporal projection from coworkerOf.") 'CxSociety)

  ;; extendsToFuture
  (v/assert kb '(extendsToFuture knows) 'CxCore)

  ;; nestingPartnerOf: genl of both romanticPartnerOf and roommateOf
  (v/assert kb '(genl nestingPartnerOf romanticPartnerOf) 'CxUniverse)
  (v/assert kb '(genl nestingPartnerOf roommateOf) 'CxUniverse)

  ;; also derive nestingPartnerOf when both components are asserted
  (v/assert-rule kb
    ['(romanticPartnerOf ?x ?y) '(roommateOf ?x ?y)]
    '(nestingPartnerOf ?x ?y)
    'CxUniverse
    {:direction :forward})

  ;; siblingOf derivation rule (shared originatorOf)
  (v/assert-rule kb
    ['(originatorOf ?p ?s1) '(originatorOf ?p ?s2) '(different ?s1 ?s2)]
    '(siblingOf ?s1 ?s2)
    'CxUniverse
    {:direction :forward})

  ;; lacunaSibling — chosen kinship group
  (v/assert kb '(unaryPredicate lacunaSibling) 'CxCore)
  (v/assert kb '(comment lacunaSibling "A member of a designated construct sibling set. Membership derives siblingOf for all pairs.") 'CxSociety)
  (v/assert-rule kb
    ['(lacunaSibling ?x) '(lacunaSibling ?y) '(different ?x ?y)]
    '(siblingOf ?x ?y)
    'CxUniverse
    {:direction :forward}))

(deftest-both-modes relationship-derivation-queries
  (with-literal-fixtures [RomanticOne RomanticTwo NestingOne NestingTwo
                  DwellerOne DwellerTwo SharedDwelling
                  OriginatorOne FoundedSiblingOne FoundedSiblingTwo
                  ChosenSiblingOne ChosenSiblingTwo]
    (setup-relationship-vocab! kb)

    ;; Each behavior uses an independent minimal graph.
    (v/assert kb '(romanticPartnerOf RomanticOne RomanticTwo) 'CxUniverse)
    (v/assert kb '(romanticPartnerOf NestingOne NestingTwo) 'CxUniverse)
    (v/assert kb '(roommateOf NestingOne NestingTwo) 'CxUniverse)

    (v/assert kb '(dwelling SharedDwelling) 'CxUniverse)
    (v/assert kb '(human DwellerOne) 'CxUniverse)
    (v/assert kb '(human DwellerTwo) 'CxUniverse)
    (v/assert kb '(dwellsIn DwellerOne SharedDwelling) 'CxUniverse)
    (v/assert kb '(dwellsIn DwellerTwo SharedDwelling) 'CxUniverse)

    (v/assert kb '(founderOf OriginatorOne FoundedSiblingOne) 'CxUniverse)
    (v/assert kb '(founderOf OriginatorOne FoundedSiblingTwo) 'CxUniverse)

    (v/assert kb '(lacunaSibling ChosenSiblingOne) 'CxUniverse)
    (v/assert kb '(lacunaSibling ChosenSiblingTwo) 'CxUniverse)

    (testing "nestingPartnerOf derived from romantic + roommate"
      (is (v/ask? kb '(nestingPartnerOf NestingOne NestingTwo) 'CxUniverse)))

    (testing "nestingPartnerOf is not derived from romance alone"
      (is (not (v/ask? kb '(nestingPartnerOf RomanticOne RomanticTwo) 'CxUniverse))))

    (testing "nestingPartnerOf is not derived from co-dwelling alone"
      (is (not (v/ask? kb '(nestingPartnerOf DwellerOne DwellerTwo) 'CxUniverse))))

    (testing "siblingOf derived from a shared originator"
      (is (v/ask? kb '(siblingOf FoundedSiblingOne FoundedSiblingTwo) 'CxUniverse)))

    (testing "origin-derived siblingOf is symmetric"
      (is (v/ask? kb '(siblingOf FoundedSiblingTwo FoundedSiblingOne) 'CxUniverse)))

    (testing "chosen siblings derive siblingOf"
      (is (v/ask? kb '(siblingOf ChosenSiblingOne ChosenSiblingTwo) 'CxUniverse)))

    (testing "chosen siblingOf is symmetric"
      (is (v/ask? kb '(siblingOf ChosenSiblingTwo ChosenSiblingOne) 'CxUniverse)))

    (testing "knows derived via genl chain"
      (is (v/ask? kb '(knows RomanticOne RomanticTwo) 'CxUniverse)
          "romanticPartnerOf → friendOf → knows"))

    (testing "friendOf derived from romanticPartnerOf"
      (is (v/ask? kb '(friendOf RomanticOne RomanticTwo) 'CxUniverse)
          "romanticPartnerOf → friendOf (optimistic ontology)"))

    (testing "relativeOf derived from founderOf"
      (is (v/ask? kb '(relativeOf OriginatorOne FoundedSiblingOne) 'CxUniverse)
          "founderOf → originatorOf → relativeOf"))

    (testing "knows derived from roommateOf"
      (is (v/ask? kb '(knows DwellerOne DwellerTwo) 'CxUniverse)
          "roommateOf → knows"))

    (testing "roommateOf derived from shared dwellsIn"
      (is (v/ask? kb '(roommateOf DwellerOne DwellerTwo) 'CxUniverse)
          "co-dwellers derive roommateOf"))

    (testing "dwellsIn-derived roommateOf is symmetric"
      (is (v/ask? kb '(roommateOf DwellerTwo DwellerOne) 'CxUniverse)
          "dwellsIn-derived roommateOf is symmetric"))))

(deftest-both-modes equivalence-relation-rules
  (with-literal-fixtures [sameHouseAs testEquiv]
    (setup-relationship-vocab! kb)

    (testing "forward: equivalenceRelation → symmetric + transitive + reflexive"
      (v/assert kb '(binaryPredicate testEquiv) 'CxCore)
      (v/assert kb '(equivalenceRelation testEquiv) 'CxCore)
      (is (v/ask? kb '(symmetric testEquiv) 'CxCore)
          "equivalenceRelation should derive symmetric")
      (is (v/ask? kb '(transitive testEquiv) 'CxCore)
          "equivalenceRelation should derive transitive")
      (is (v/ask? kb '(reflexive testEquiv) 'CxCore)
          "equivalenceRelation should derive reflexive"))

    (testing "converse: symmetric + transitive + reflexive → equivalenceRelation"
      (v/assert kb '(binaryPredicate sameHouseAs) 'CxCore)
      (v/assert kb '(symmetric sameHouseAs) 'CxUniverse)
      (v/assert kb '(transitive sameHouseAs) 'CxUniverse)
      (v/assert kb '(reflexive sameHouseAs) 'CxUniverse)
      (is (v/ask? kb '(equivalenceRelation sameHouseAs) 'CxUniverse)
          "symmetric + transitive + reflexive should derive equivalenceRelation"))

    (testing "derived properties actually work — not just stored"
      ;; testEquiv got symmetric/transitive/reflexive via equivalenceRelation rule.
      ;; verify the derived symmetric actually makes the predicate behave symmetrically.
      (v/assert kb '(testEquiv Alice Bob) 'CxUniverse)

      (is (v/ask? kb '(testEquiv Bob Alice) 'CxUniverse)
          "derived symmetry works — Bob-Alice from Alice-Bob")

      ;; verify derived transitivity
      (v/assert kb '(testEquiv Bob Carol) 'CxUniverse)
      (is (v/ask? kb '(testEquiv Alice Carol) 'CxUniverse)
          "derived transitivity works — Alice-Carol from Alice-Bob + Bob-Carol")

      ;; verify derived reflexivity
      (is (v/ask? kb '(testEquiv Alice Alice) 'CxUniverse)
          "derived reflexivity works — Alice-Alice"))))

(deftest-both-modes not-assertible-derivation
  (with-literal-fixtures []
    (setup-relationship-vocab! kb)

    (testing "former-version preds are derived notAssertible"
      (is (v/ask? kb '(notAssertible formerlyMarriedTo) 'CxCore)
          "formerlyMarriedTo should be notAssertible")
      (is (v/ask? kb '(notAssertible exPartnerOf) 'CxCore)
          "exPartnerOf should be notAssertible")
      (is (v/ask? kb '(notAssertible formerCoworkerOf) 'CxCore)
          "formerCoworkerOf should be notAssertible"))

    (testing "base preds are NOT notAssertible"
      (is (not (v/ask? kb '(notAssertible marriedTo) 'CxCore)))
      (is (not (v/ask? kb '(notAssertible romanticPartnerOf) 'CxCore)))
      (is (not (v/ask? kb '(notAssertible coworkerOf) 'CxCore))))

    (testing "assert-guarded blocks notAssertible preds"
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"notAssertible"
            (bridge/assert-guarded kb '(formerlyMarriedTo Alice Bob) 'CxUniverse))))

    (testing "assert-guarded allows normal preds"
      (is (bridge/assert-guarded kb '(marriedTo Alice Bob) 'CxUniverse)))

    (testing "assert-guarded blocks undeclared predicates"
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"not a declared predicate"
            (bridge/assert-guarded kb '(broommateOf Alice Bob) 'CxUniverse))
          "typo'd predicate should throw"))

    (testing "assert-guarded blocks undeclared unary predicates"
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"not a declared predicate"
            (bridge/assert-guarded kb '(fghgwgads 212) 'CxUniverse))
          "nonsense predicate should throw"))))

(defn- setup-synthetic-temporal-contexts!
  "Create independent, undated temporal contexts for projection tests."
  [kb]
  (doseq [ctx '[CxFormerMarriage CxFormerRomance CxFormerWork
                CxPresent]]
    (v/assert kb (list 'genlCx ctx 'CxUniverse) 'CxUniverse))
  ;; The current-data test context must see the rule contexts whose independent
  ;; micrographs it exercises.  A sibling of those contexts under CxUniverse
  ;; cannot host their derived conclusions.
  (doseq [parent '[CxSocial CxBiology CxKinship]]
    (v/assert kb (list 'genlCx 'CxSyntheticData parent) 'CxUniverse))
  (doseq [ctx '[CxFormerMarriage CxFormerRomance CxFormerWork]]
    (v/assert kb (list 'before ctx 'CxPresent) 'CxTime)))

(defn- setup-plurality-vocab!
  "Plurality ontology: pluralSystem, alter, singlet, alterOf, headmateOf."
  [kb]
  ;; asymmetric binary
  (v/assert kb '(asymmetricBinaryPredicate alterOf) 'CxCore)
  (v/assert kb '(comment alterOf "Maps an alter to the plural system it belongs to. (alterOf alter system).") 'CxCore)
  (v/assert kb '(argIsa alterOf 1 alter) 'CxSociety)
  (v/assert kb '(argIsa alterOf 2 pluralSystem) 'CxSociety)
  ;; symmetric binary
  (v/assert kb '(symmetricBinaryPredicate headmateOf) 'CxCore)
  (v/assert kb '(comment headmateOf "Alters in the same plural system.") 'CxSociety)
  (v/assert kb '(not (genl headmateOf knows)) 'CxUniverse)
  (v/assert kb '(comment (not (genl headmateOf knows)) "Amnesia walls mean headmates might not know each other.") 'CxSociety)
  (v/assert kb '(argIsa headmateOf 1 alter) 'CxSociety)
  (v/assert kb '(argIsa headmateOf 2 alter) 'CxSociety)
  ;; unary predicates
  (doseq [pred '[singlet pluralSystem alter construct]]
    (v/assert kb (list 'unaryPredicate pred) 'CxCore))
  (v/assert kb '(comment alter "An alter in a plural system. Distinct identity within a shared body.") 'CxCore)
  (v/assert kb '(comment construct "An entity with social agency, continuity, and accountability whose substrate is computational, not biological.") 'CxCore)
  (v/assert kb '(comment singlet "A non-plural person — exactly one identity, one body.") 'CxCore)
  (v/assert kb '(comment pluralSystem "A plural system — multiple alters sharing one body.") 'CxCore)
  ;; genl hierarchy for plurality types
  (v/assert kb '(genl construct person) 'CxUniverse)
  (v/assert kb '(genl singlet person) 'CxUniverse)
  (v/assert kb '(genl pluralSystem person) 'CxUniverse)
  (v/assert kb '(genl alter person) 'CxUniverse)
  (v/assert kb '(disjoint singlet pluralSystem) 'CxUniverse)
  (v/assert kb '(disjoint alter singlet) 'CxUniverse)
  (v/assert kb '(disjoint alter pluralSystem) 'CxUniverse)
  ;; (disjoint construct living_thing) must be asserted AFTER fix-starter-ontology!
  ;; retracts (genl person mammal) — otherwise construct is genl-related to living_thing
  ;; via person → mammal → animal → living_thing, making the disjoint ill-formed.
  ;; Callers that use fix-starter-ontology! should assert it separately.
  ;; headmateOf derivation: shared alterOf
  (v/assert-rule kb
    ['(alterOf ?a1 ?sys) '(alterOf ?a2 ?sys) '(different ?a1 ?a2)]
    '(headmateOf ?a1 ?a2)
    'CxUniverse
    {:direction :forward})
  ;; alters inherit their system's dwelling
  ;; vaelii's assertive entailment derives (human ?alter) from dwellsIn's argIsa
  (v/assert-rule kb
    ['(dwellsIn ?system ?place) '(alterOf ?alter ?system)]
    '(dwellsIn ?alter ?place)
    'CxUniverse
    {:direction :forward}))

(deftest-both-modes temporal-and-plurality-derivations
  (with-literal-fixtures [RomanceSource RomanceTarget NestingSource NestingTarget
                  ChosenSiblingOne ChosenSiblingTwo SharedOrigin
                  FoundedSiblingOne FoundedSiblingTwo
                  CoDwellerOne CoDwellerTwo CoDwelling
                  HeadmateSystem HeadmateOne HeadmateTwo
                  DwellingSystem DwellingAlter SystemDwelling
                  CreatorOne CreatedOne
                  FormerSpouseOne FormerSpouseTwo
                  FormerPartnerOne FormerPartnerTwo
                  FormerCoworkerOne FormerCoworkerTwo
                  CxFormerMarriage CxFormerRomance CxFormerWork
                  CxPresent CxSyntheticData]
    (setup-relationship-vocab! kb)
    (setup-synthetic-temporal-contexts! kb)
    (setup-plurality-vocab! kb)

    ;; Every behavior below uses a disconnected, invented micrograph.
    (v/assert kb '(romanticPartnerOf RomanceSource RomanceTarget) 'CxSyntheticData)
    (v/assert kb '(nestingPartnerOf NestingSource NestingTarget) 'CxSyntheticData)

    (v/assert kb '(lacunaSibling ChosenSiblingOne) 'CxSyntheticData)
    (v/assert kb '(lacunaSibling ChosenSiblingTwo) 'CxSyntheticData)
    (v/assert kb '(founderOf SharedOrigin FoundedSiblingOne) 'CxSyntheticData)
    (v/assert kb '(founderOf SharedOrigin FoundedSiblingTwo) 'CxSyntheticData)

    (v/assert kb '(dwelling CoDwelling) 'CxSyntheticData)
    (v/assert kb '(human CoDwellerOne) 'CxSyntheticData)
    (v/assert kb '(human CoDwellerTwo) 'CxSyntheticData)
    (v/assert kb '(dwellsIn CoDwellerOne CoDwelling) 'CxSyntheticData)
    (v/assert kb '(dwellsIn CoDwellerTwo CoDwelling) 'CxSyntheticData)

    (v/assert kb '(pluralSystem HeadmateSystem) 'CxSyntheticData)
    (v/assert kb '(alter HeadmateOne) 'CxSyntheticData)
    (v/assert kb '(alter HeadmateTwo) 'CxSyntheticData)
    (v/assert kb '(alterOf HeadmateOne HeadmateSystem) 'CxSyntheticData)
    (v/assert kb '(alterOf HeadmateTwo HeadmateSystem) 'CxSyntheticData)

    (v/assert kb '(human DwellingSystem) 'CxSyntheticData)
    (v/assert kb '(pluralSystem DwellingSystem) 'CxSyntheticData)
    (v/assert kb '(human DwellingAlter) 'CxSyntheticData)
    (v/assert kb '(alter DwellingAlter) 'CxSyntheticData)
    (v/assert kb '(dwelling SystemDwelling) 'CxSyntheticData)
    (v/assert kb '(dwellsIn DwellingSystem SystemDwelling) 'CxSyntheticData)
    (v/assert kb '(alterOf DwellingAlter DwellingSystem) 'CxSyntheticData)

    (v/assert kb '(founderOf CreatorOne CreatedOne) 'CxSyntheticData)

    (v/assert kb '(marriedTo FormerSpouseOne FormerSpouseTwo) 'CxFormerMarriage)
    (v/assert kb '(romanticPartnerOf FormerPartnerOne FormerPartnerTwo) 'CxFormerRomance)
    (v/assert kb '(coworkerOf FormerCoworkerOne FormerCoworkerTwo) 'CxFormerWork)

    (testing "knows via genl chain: romanticPartnerOf → friendOf → knows"
      (is (v/ask? kb '(knows RomanceSource RomanceTarget) 'CxSyntheticData)))

    (testing "friendOf derived from romanticPartnerOf (optimistic ontology)"
      (is (v/ask? kb '(friendOf RomanceSource RomanceTarget) 'CxSyntheticData)))

    (testing "nestingPartnerOf derives romanticPartnerOf via genl"
      (is (v/ask? kb '(romanticPartnerOf NestingSource NestingTarget) 'CxSyntheticData)))

    (testing "nestingPartnerOf derives roommateOf via genl"
      (is (v/ask? kb '(roommateOf NestingSource NestingTarget) 'CxSyntheticData)))

    (testing "siblingOf derives from chosen sibling membership"
      (is (v/ask? kb '(siblingOf ChosenSiblingOne ChosenSiblingTwo) 'CxSyntheticData)))

    (testing "siblingOf derives independently from a shared originator"
      (is (v/ask? kb '(siblingOf FoundedSiblingOne FoundedSiblingTwo) 'CxSyntheticData)))

    (testing "roommateOf derives from shared dwellsIn"
      (is (v/ask? kb '(roommateOf CoDwellerOne CoDwellerTwo) 'CxSyntheticData)))

    (testing "headmateOf derives from alters in one system"
      (is (v/ask? kb '(headmateOf HeadmateOne HeadmateTwo) 'CxSyntheticData)))

    (testing "an alter inherits its system's dwelling"
      (is (v/ask? kb '(dwellsIn DwellingAlter SystemDwelling) 'CxSyntheticData)
          "alter inherits system's dwelling"))

    (testing "relativeOf derives from founderOf → originatorOf → relativeOf"
      (is (v/ask? kb '(relativeOf CreatorOne CreatedOne) 'CxSyntheticData)))

    (testing "formerlyMarriedTo derives in CxPresent via temporal lifting"
      (is (v/ask? kb '(formerlyMarriedTo FormerSpouseOne FormerSpouseTwo) 'CxPresent)))

    (testing "exPartnerOf derives in CxPresent via temporal lifting"
      (is (v/ask? kb '(exPartnerOf FormerPartnerOne FormerPartnerTwo) 'CxPresent)))

    (testing "formerCoworkerOf derives in CxPresent via temporal lifting"
      (is (v/ask? kb '(formerCoworkerOf FormerCoworkerOne FormerCoworkerTwo) 'CxPresent)))

    (testing "knows still holds in CxPresent via extendsToFuture"
      (is (v/ask? kb '(knows FormerSpouseOne FormerSpouseTwo) 'CxPresent)))))

(deftest-both-modes starter-migration-type-safety
  (with-literal-fixtures [SyntheticConstructOne SyntheticConstructTwo
                  BiologicalParent BiologicalChild SyntheticAndroid BiologicalFriend
                  syntheticAndroidType]
    ;; apply the bridge migration on a fork (retracts person→mammal, introduces human)
    (bridge/fix-starter-ontology! kb)

    ;; declare construct type
    (v/assert kb '(unaryPredicate construct) 'CxCore)

    ;; assert test entities — use human for biological, construct for non-bio
    (v/assert kb '(construct SyntheticConstructOne) 'CxUniverse)
    (v/assert kb '(construct SyntheticConstructTwo) 'CxUniverse)
    (v/assert kb '(human BiologicalParent) 'CxUniverse)
    (v/assert kb '(human BiologicalChild) 'CxUniverse)

    (testing "1. construct does NOT derive animal or mammal"
      (is (not (v/ask? kb '(animal SyntheticConstructOne) 'CxUniverse))
          "synthetic construct should not be an animal")
      (is (not (v/ask? kb '(mammal SyntheticConstructOne) 'CxUniverse))
          "synthetic construct should not be a mammal"))

    (testing "2. construct↔construct friendOf type-checks"
      (is (v/assert kb '(friendOf SyntheticConstructOne SyntheticConstructTwo) 'CxUniverse)
          "friendOf between constructs should type-check"))

    (testing "3. construct↔construct siblingOf type-checks"
      (is (v/assert kb '(siblingOf SyntheticConstructOne SyntheticConstructTwo) 'CxUniverse)
          "siblingOf between constructs should type-check"))

    (testing "4. human↔human parentOf still type-checks"
      (is (v/assert kb '(parentOf BiologicalParent BiologicalChild) 'CxUniverse)
          "parentOf between humans should still type-check"))

    (testing "5. migration produced correct type hierarchy"
      (is (v/ask? kb '(unaryPredicate human) 'CxCore)
          "human type should exist after migration")
      (is (v/ask? kb '(genl human person) 'CxUniverse)
          "human should be genl under person")
      (is (v/ask? kb '(genl construct person) 'CxUniverse)
          "construct should be genl under person")
      (is (v/ask? kb '(genl human mammal) 'CxOrganism)
          "human should still be a mammal")
      (is (not (v/ask? kb '(genl person mammal) 'CxOrganism))
          "person should no longer be a mammal"))

    (testing "6. a synthetic non-biological person is not a mammal"
      (v/assert kb '(unaryPredicate syntheticAndroidType) 'CxCore)
      (v/assert kb '(genl syntheticAndroidType person) 'CxUniverse)
      (v/assert kb '(syntheticAndroidType SyntheticAndroid) 'CxUniverse)
      (v/assert kb '(human BiologicalFriend) 'CxUniverse)

      (is (v/ask? kb '(person SyntheticAndroid) 'CxUniverse)
          "synthetic android is a person via its declared type")
      (is (not (v/ask? kb '(mammal SyntheticAndroid) 'CxUniverse))
          "synthetic android is NOT a mammal")
      (is (not (v/ask? kb '(animal SyntheticAndroid) 'CxUniverse))
          "synthetic android is NOT an animal")

      (is (v/assert kb '(friendOf SyntheticAndroid BiologicalFriend) 'CxUniverse)
          "friendOf between android and human type-checks")
      (is (v/ask? kb '(friendOf BiologicalFriend SyntheticAndroid) 'CxUniverse)
          "friendOf symmetry holds across synthetic person types"))))

(deftest-both-modes predicate-type-hierarchy-and-meta-argisas
  (with-literal-fixtures []
    (setup-relationship-vocab! kb)

    (testing "predicateTypeByArity derives genl under predicate"
      (is (v/ask? kb '(genl unaryPredicate predicate) 'CxCore)
          "unaryPredicate genl predicate")
      (is (v/ask? kb '(genl binaryPredicate predicate) 'CxCore)
          "binaryPredicate genl predicate")
      (is (v/ask? kb '(genl ternaryPredicate predicate) 'CxCore)
          "ternaryPredicate genl predicate"))

    (testing "predicate-type meta-predicates are unary (they classify predicates)"
      (is (v/ask? kb '(arity unaryPredicate 1) 'CxCore)
          "unaryPredicate arity 1")
      (is (v/ask? kb '(arity binaryPredicate 1) 'CxCore)
          "binaryPredicate arity 1 (unary meta-predicate)")
      (is (v/ask? kb '(arity ternaryPredicate 1) 'CxCore)
          "ternaryPredicate arity 1 (unary meta-predicate)"))

    (testing "predicate types are pairwise disjoint via partition rule"
      (is (v/ask? kb '(disjoint unaryPredicate binaryPredicate) 'CxCore)
          "unaryPredicate disjoint binaryPredicate")
      (is (v/ask? kb '(disjoint binaryPredicate ternaryPredicate) 'CxCore)
          "binaryPredicate disjoint ternaryPredicate")
      (is (v/ask? kb '(disjoint unaryPredicate ternaryPredicate) 'CxCore)
          "unaryPredicate disjoint ternaryPredicate"))

    (testing "meta-predicate argIsas are set"
      (is (v/ask? kb '(argIsa formerVersionOf 1 predicate) 'CxCore)
          "formerVersionOf arg1 typed to predicate")
      (is (v/ask? kb '(argIsa formerVersionOf 2 predicate) 'CxCore)
          "formerVersionOf arg2 typed to predicate")
      (is (v/ask? kb '(argIsa extendsToFuture 1 predicate) 'CxCore)
          "extendsToFuture arg1 typed to predicate")
      (is (v/ask? kb '(argIsa notAssertible 1 predicate) 'CxCore)
          "notAssertible arg1 typed to predicate")
      (is (v/ask? kb '(argIsa symmetricBinaryPredicate 1 binaryPredicate) 'CxCore)
          "symmetricBinaryPredicate arg1 typed to binaryPredicate")
      (is (v/ask? kb '(argIsa equivalenceRelation 1 binaryPredicate) 'CxCore)
          "equivalenceRelation arg1 typed to binaryPredicate"))))

(deftest-both-modes argisa-enforcement
  (with-literal-fixtures [BiologicalParent SyntheticConstruct BiologicalChild]
    (bridge/fix-starter-ontology! kb)
    (setup-relationship-vocab! kb)
    (setup-plurality-vocab! kb)
    (v/assert kb '(disjoint construct living_thing) 'CxUniverse)

    ;; verify disjointness propagates through genl
    (testing "disjoint construct animal provable from (disjoint construct living_thing)"
      (is (v/ask? kb '(disjoint construct animal) 'CxUniverse)
          "construct disjoint with animal via living_thing genl chain"))

    ;; declare individuals with types
    (v/assert kb '(human BiologicalParent) 'CxUniverse)
    (v/assert kb '(construct SyntheticConstruct) 'CxUniverse)
    (v/assert kb '(human BiologicalChild) 'CxUniverse)

    (testing "parentOf rejects a construct in the child position"
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"rejected"
            (bridge/assert-guarded kb '(parentOf BiologicalParent SyntheticConstruct) 'CxUniverse))))

    (testing "founderOf rejects a biological person in the construct position"
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"rejected"
            (bridge/assert-guarded kb '(founderOf BiologicalParent BiologicalChild) 'CxUniverse))))

    (testing "parentOf accepts two biological people"
      (is (bridge/assert-guarded kb '(parentOf BiologicalParent BiologicalChild) 'CxUniverse)))

    (testing "founderOf accepts person × construct"
      (is (bridge/assert-guarded kb '(founderOf BiologicalParent SyntheticConstruct) 'CxUniverse)))))

(deftest-both-modes functional-slot-enforcement
  (with-literal-fixtures [alsoFormerlyMarriedTo]
    (setup-relationship-vocab! kb)

    (testing "formerVersionOf declared functional"
      (is (v/ask? kb '(functional formerVersionOf) 'CxCore)
          "formerVersionOf should be functional"))

    ;; v/check does NOT enforce functional constraints (known issue).
    ;; bridge should enforce this eventually.
    (testing "v/check does NOT catch functional violations (known gap)"
      (v/assert kb '(binaryPredicate alsoFormerlyMarriedTo) 'CxCore)
      (let [problems (v/check kb '(formerVersionOf marriedTo alsoFormerlyMarriedTo) 'CxCore)]
        (is (empty? problems)
            "v/check currently does not enforce functional — this test documents the gap")))))

;; ============================================================
;; CONSTRAINT-SENSITIVE TESTS
;; Behavior differs between :refuse (throw on disjoint clash)
;; and :arbitrate (admit and settle).
;; ============================================================

;; --- type-constraint-enforcement ---
;; Under :refuse, v/check catches disjoint clashes for unary type assertions
;; (no argIsa for construct/human/dog as type predicates, so only v/check
;; provides enforcement). Under :arbitrate, v/check returns empty and
;; assert-guarded admits the clash.

(deftest type-constraint-enforcement-refuse
  (let [kb (v/fork tu/*kb* {:constraints :refuse})]
  (with-literal-fixtures [BiologicalPerson SyntheticConstruct]
    (bridge/fix-starter-ontology! kb)
    (setup-relationship-vocab! kb)
    (setup-plurality-vocab! kb)
    (v/assert kb '(disjoint construct living_thing) 'CxUniverse)

    ;; verify disjointness propagates through genl
    (testing "disjoint construct animal provable from (disjoint construct living_thing)"
      (is (v/ask? kb '(disjoint construct animal) 'CxUniverse)
          "construct disjoint with animal via living_thing genl chain"))

    ;; declare individuals with types
    (v/assert kb '(human BiologicalPerson) 'CxUniverse)
    (v/assert kb '(construct SyntheticConstruct) 'CxUniverse)

    (testing "construct rejects a known biological person"
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"rejected"
            (bridge/assert-guarded kb '(construct BiologicalPerson) 'CxUniverse))))

    (testing "human rejects a known construct"
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"rejected"
            (bridge/assert-guarded kb '(human SyntheticConstruct) 'CxUniverse))))

    (testing "dog rejects a known construct through living_thing disjointness"
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"rejected"
            (bridge/assert-guarded kb '(dog SyntheticConstruct) 'CxUniverse))))

    (testing "disjoint symmetric asymmetric is provable"
      (is (v/ask? kb '(disjoint symmetric asymmetric) 'CxCore)))

    (testing "disjoint symmetricBinaryPredicate asymmetricBinaryPredicate via genl"
      (is (v/ask? kb '(disjoint symmetricBinaryPredicate asymmetricBinaryPredicate) 'CxCore))))))

(deftest type-constraint-enforcement-arbitrate
  (let [kb (v/fork tu/*kb* {:constraints :arbitrate})]
  (with-literal-fixtures [BiologicalPerson SyntheticConstruct]
    (bridge/fix-starter-ontology! kb)
    (setup-relationship-vocab! kb)
    (setup-plurality-vocab! kb)
    (v/assert kb '(disjoint construct living_thing) 'CxUniverse)

    ;; verify disjointness propagates through genl — same under both policies
    (testing "disjoint construct animal provable from (disjoint construct living_thing)"
      (is (v/ask? kb '(disjoint construct animal) 'CxUniverse)
          "construct disjoint with animal via living_thing genl chain"))

    ;; declare individuals with types
    (v/assert kb '(human BiologicalPerson) 'CxUniverse)
    (v/assert kb '(construct SyntheticConstruct) 'CxUniverse)

    ;; pure derivation — same under both policies
    (testing "disjoint symmetric asymmetric is provable"
      (is (v/ask? kb '(disjoint symmetric asymmetric) 'CxCore)))

    (testing "disjoint symmetricBinaryPredicate asymmetricBinaryPredicate via genl"
      (is (v/ask? kb '(disjoint symmetricBinaryPredicate asymmetricBinaryPredicate) 'CxCore)))

    ;; Under :arbitrate, type clashes are admitted and settled, not refused.
    ;; Sub-tests run sequentially on the same KB (no inner forks — vaelii
    ;; does not allow fork-of-fork). Each uses independent individuals.
    (testing "construct admits a known biological person under :arbitrate"
      (is (empty? (v/check kb '(construct BiologicalPerson) 'CxUniverse))
          "v/check returns no problems under :arbitrate")
      (is (bridge/assert-guarded kb '(construct BiologicalPerson) 'CxUniverse))
      (is (or (v/ask? kb '(construct BiologicalPerson) 'CxUniverse)
              (v/ask? kb '(human BiologicalPerson) 'CxUniverse))
          "at least one side survives arbitration"))

    (testing "human admits a known construct under :arbitrate"
      (is (empty? (v/check kb '(human SyntheticConstruct) 'CxUniverse))
          "v/check returns no problems under :arbitrate")
      (is (bridge/assert-guarded kb '(human SyntheticConstruct) 'CxUniverse))
      (is (or (v/ask? kb '(human SyntheticConstruct) 'CxUniverse)
              (v/ask? kb '(construct SyntheticConstruct) 'CxUniverse))
          "at least one side survives arbitration"))

    (testing "dog admits a known construct under :arbitrate"
      (is (empty? (v/check kb '(dog SyntheticConstruct) 'CxUniverse))
          "v/check returns no problems under :arbitrate")
      (is (bridge/assert-guarded kb '(dog SyntheticConstruct) 'CxUniverse))
      (is (or (v/ask? kb '(dog SyntheticConstruct) 'CxUniverse)
              (v/ask? kb '(construct SyntheticConstruct) 'CxUniverse))
          "at least one side survives arbitration")))))

;; --- comprehensive-ontology-scenarios ---
;; The large integration test is split: a shared setup function, a common
;; assertions function (pure derivation + bridge-enforced guards that work
;; identically under both policies), and two deftest functions for the
;; constraint-sensitive tests 11 and 12.

(defn- comprehensive-scenario-setup!
  "Common setup for comprehensive-ontology-scenarios under both constraint policies.
   Calls fix-starter-ontology! which modifies the KB (retracts person->mammal).
   Must be called on a fork to isolate mutations."
  [kb]
  (bridge/fix-starter-ontology! kb)
  (setup-relationship-vocab! kb)
  (setup-plurality-vocab! kb)
  ;; disjoint construct living_thing — safe now that fix-starter-ontology! retracted person→mammal
  (v/assert kb '(disjoint construct living_thing) 'CxUniverse)

  ;; Each group of facts is an independent invented micrograph.
  (v/assert kb '(human RomanticOne) 'CxUniverse)
  (v/assert kb '(human RomanticTwo) 'CxUniverse)
  (v/assert kb '(romanticPartnerOf RomanticOne RomanticTwo) 'CxUniverse)

  (v/assert kb '(human CreatorAgent) 'CxUniverse)
  (v/assert kb '(construct CreatedConstruct) 'CxUniverse)
  (v/assert kb '(founderOf CreatorAgent CreatedConstruct) 'CxUniverse)

  (v/assert kb '(construct TypedConstruct) 'CxUniverse)
  (v/assert kb '(human TypedHuman) 'CxUniverse)

  (v/assert kb '(construct ChosenSiblingOne) 'CxUniverse)
  (v/assert kb '(construct ChosenSiblingTwo) 'CxUniverse)
  (v/assert kb '(lacunaSibling ChosenSiblingOne) 'CxUniverse)
  (v/assert kb '(lacunaSibling ChosenSiblingTwo) 'CxUniverse)

  (v/assert kb '(human ResidentOne) 'CxUniverse)
  (v/assert kb '(dwelling ResidenceOne) 'CxUniverse)
  (v/assert kb '(dwellsIn ResidentOne ResidenceOne) 'CxUniverse))

(defn- comprehensive-scenario-common
  "Assertions that hold under both :refuse and :arbitrate constraint policies.
   Includes pure derivation queries, bridge-enforced rejections (which use
   check-arg-types and bridge guards independent of v/check), and derivation chains."
  [kb]
  ;; ============================================================
  ;; PROVABLE
  ;; ============================================================

  (testing "1. knows derives via romanticPartnerOf → friendOf → knows"
    (is (v/ask? kb '(knows RomanticOne RomanticTwo) 'CxUniverse)))

  (testing "2. relativeOf derives via founderOf → originatorOf → relativeOf"
    (is (v/ask? kb '(relativeOf CreatorAgent CreatedConstruct) 'CxUniverse)))

  (testing "3. a construct derives person via (genl construct person)"
    (is (v/ask? kb '(person CreatedConstruct) 'CxUniverse)))

  (testing "4. a human derives mammal via the starter hierarchy"
    (is (v/ask? kb '(mammal TypedHuman) 'CxUniverse)))

  (testing "5. siblingOf derives via chosen sibling membership"
    (is (v/ask? kb '(siblingOf ChosenSiblingOne ChosenSiblingTwo) 'CxUniverse)))

  (testing "6. disjoint binaryPredicate ternaryPredicate — via partition rule"
    (is (v/ask? kb '(disjoint binaryPredicate ternaryPredicate) 'CxCore)))

  (testing "7. livesIn derives via genl dwellsIn livesIn"
    (is (v/ask? kb '(livesIn ResidentOne ResidenceOne) 'CxUniverse)))

  (testing "8. friendOf derives via romanticPartnerOf → friendOf"
    (is (v/ask? kb '(friendOf RomanticOne RomanticTwo) 'CxUniverse)))

  ;; ============================================================
  ;; PROVABLY FALSE / DISPROVABLE
  ;; ============================================================

  (testing "9. mammal is false for a construct disjoint with living_thing"
    (is (not (v/ask? kb '(mammal TypedConstruct) 'CxUniverse))))

  (testing "10. headmateOf does NOT genl knows — amnesia walls"
    (is (v/ask? kb '(not (genl headmateOf knows)) 'CxUniverse)))

  ;; ============================================================
  ;; ILL-FORMED — bridge-enforced (same under both policies)
  ;; Tests 13-14 are caught by bridge/check-arg-types (argIsa violations
  ;; detected via v/ask? queries, independent of constraint policy).
  ;; Test 15 is an undeclared predicate; test 16 is notAssertible.
  ;; ============================================================

  (testing "13. parentOf rejects a construct in the child position"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"rejected"
          (bridge/assert-guarded kb '(parentOf TypedHuman TypedConstruct) 'CxUniverse))))

  (testing "14. founderOf rejects a human in the construct position"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"rejected"
          (bridge/assert-guarded kb '(founderOf TypedConstruct TypedHuman) 'CxUniverse))))

  (testing "15. broommateOf rejected — undeclared predicate"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"rejected"
          (bridge/assert-guarded kb '(broommateOf UnknownRelationOne UnknownRelationTwo) 'CxUniverse))))

  (testing "16. formerlyMarriedTo rejected — notAssertible"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"rejected"
          (bridge/assert-guarded kb '(formerlyMarriedTo DerivedFormerOne DerivedFormerTwo) 'CxUniverse))))

  ;; ============================================================
  ;; DERIVATION CHAIN TESTS (isolated fixtures)
  ;; ============================================================

  (testing "17. dwellsIn derives roommateOf + symmetric + livesIn"
    (v/assert kb '(human CoDwellerOne) 'CxUniverse)
    (v/assert kb '(human CoDwellerTwo) 'CxUniverse)
    (v/assert kb '(dwelling CoDwelling) 'CxUniverse)
    (v/assert kb '(dwellsIn CoDwellerOne CoDwelling) 'CxUniverse)
    (v/assert kb '(dwellsIn CoDwellerTwo CoDwelling) 'CxUniverse)
    (is (v/ask? kb '(roommateOf CoDwellerOne CoDwellerTwo) 'CxUniverse)
        "roommateOf derived from shared dwelling")
    (is (v/ask? kb '(roommateOf CoDwellerTwo CoDwellerOne) 'CxUniverse)
        "roommateOf symmetric")
    (is (v/ask? kb '(livesIn CoDwellerOne CoDwelling) 'CxUniverse)
        "livesIn derived via genl dwellsIn livesIn"))

  (testing "18. nestingPartnerOf derivation chain"
    (v/assert kb '(human NestingOne) 'CxUniverse)
    (v/assert kb '(human NestingTwo) 'CxUniverse)
    (v/assert kb '(romanticPartnerOf NestingOne NestingTwo) 'CxUniverse)
    (v/assert kb '(roommateOf NestingOne NestingTwo) 'CxUniverse)
    (is (v/ask? kb '(nestingPartnerOf NestingOne NestingTwo) 'CxUniverse)
        "nestingPartnerOf from romantic + roommate")
    (is (v/ask? kb '(friendOf NestingOne NestingTwo) 'CxUniverse)
        "friendOf from romanticPartnerOf")
    (is (v/ask? kb '(knows NestingOne NestingTwo) 'CxUniverse)
        "knows from friendOf"))

  (testing "19. headmateOf derivation + boundaries"
    (v/assert kb '(pluralSystem HeadmateSystem) 'CxUniverse)
    (v/assert kb '(alter HeadmateOne) 'CxUniverse)
    (v/assert kb '(alter HeadmateTwo) 'CxUniverse)
    (v/assert kb '(alterOf HeadmateOne HeadmateSystem) 'CxUniverse)
    (v/assert kb '(alterOf HeadmateTwo HeadmateSystem) 'CxUniverse)
    (is (v/ask? kb '(headmateOf HeadmateOne HeadmateTwo) 'CxUniverse)
        "headmateOf derived from shared alterOf")
    (is (v/ask? kb '(headmateOf HeadmateTwo HeadmateOne) 'CxUniverse)
        "headmateOf symmetric")
    (is (not (v/ask? kb '(headmateOf HeadmateOne HeadmateOne) 'CxUniverse))
        "headmateOf NOT reflexive — different guard")
    (is (not (v/ask? kb '(knows HeadmateOne HeadmateTwo) 'CxUniverse))
        "knows NOT derived from headmateOf alone — amnesia walls")))

(deftest comprehensive-ontology-scenarios-refuse
  (let [kb (v/fork tu/*kb* {:constraints :refuse})]
  (with-literal-fixtures [RomanticOne RomanticTwo
                  CreatorAgent CreatedConstruct TypedConstruct TypedHuman
                  ChosenSiblingOne ChosenSiblingTwo
                  ResidentOne ResidenceOne
                  UnknownRelationOne UnknownRelationTwo
                  DerivedFormerOne DerivedFormerTwo
                  CoDwellerOne CoDwellerTwo CoDwelling
                  NestingOne NestingTwo
                  HeadmateOne HeadmateTwo HeadmateSystem]
    (comprehensive-scenario-setup! kb)
    (comprehensive-scenario-common kb)

    ;; Under :refuse, type clashes throw via v/check.
    (testing "11. construct rejects a known human"
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"rejected"
            (bridge/assert-guarded kb '(construct TypedHuman) 'CxUniverse))))

    (testing "12. human rejects a known construct"
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"rejected"
            (bridge/assert-guarded kb '(human TypedConstruct) 'CxUniverse)))))))

(deftest comprehensive-ontology-scenarios-arbitrate
  (let [kb (v/fork tu/*kb* {:constraints :arbitrate})]
  (with-literal-fixtures [RomanticOne RomanticTwo
                  CreatorAgent CreatedConstruct TypedConstruct TypedHuman
                  ChosenSiblingOne ChosenSiblingTwo
                  ResidentOne ResidenceOne
                  UnknownRelationOne UnknownRelationTwo
                  DerivedFormerOne DerivedFormerTwo
                  CoDwellerOne CoDwellerTwo CoDwelling
                  NestingOne NestingTwo
                  HeadmateOne HeadmateTwo HeadmateSystem]
    (comprehensive-scenario-setup! kb)
    (comprehensive-scenario-common kb)

    ;; Under :arbitrate, type clashes are admitted and settled, not refused.
    ;; Sub-tests run sequentially on the same KB (no inner forks — vaelii
    ;; does not allow fork-of-fork). Each uses independent individuals.
    (testing "11. construct admits a known human under :arbitrate"
      (is (empty? (v/check kb '(construct TypedHuman) 'CxUniverse))
          "v/check returns no problems under :arbitrate")
      (is (bridge/assert-guarded kb '(construct TypedHuman) 'CxUniverse))
      (is (or (v/ask? kb '(construct TypedHuman) 'CxUniverse)
              (v/ask? kb '(human TypedHuman) 'CxUniverse))
          "at least one side survives arbitration"))

    (testing "12. human admits a known construct under :arbitrate"
      (is (empty? (v/check kb '(human TypedConstruct) 'CxUniverse))
          "v/check returns no problems under :arbitrate")
      (is (bridge/assert-guarded kb '(human TypedConstruct) 'CxUniverse))
      (is (or (v/ask? kb '(human TypedConstruct) 'CxUniverse)
              (v/ask? kb '(construct TypedConstruct) 'CxUniverse))
          "at least one side survives arbitration")))))


;; ============================================================
;; EPISTEMIC DISCIPLINE SPIKE 1 — Capability Ontology
;; Capabilities as predicates, not reified types.
;; "Can Nyx see?" = (agentCapable Nyx sees).
;; ============================================================

;; typeVersion as a generator requires variable-functor rule literals,
;; which vaelii rejects (:not-indexable). Until that support lands,
;; we assert one concrete bridge rule per (typeVersion X Y) declaration.
;; The generator pattern (commented below) becomes viable when vaelii
;; supports unbound-predicate rule indexing in generator consequents.
;;
;; (def ^:private type-version-generator
;;   '(set/forwardRule
;;     (implies (typeVersion ?ipred ?tpred)
;;       (set/forwardRule
;;         (implies (and (?tpred ?type ?cap) (?type ?agent))
;;           (?ipred ?agent ?cap))))))

(defn- assert-capability-ontology!
  "Assert Pace's capability ontology draft into kb.
   Returns the kb with the ontology loaded.
   All terms carry full defining assertions: genl, comment, and
   argIsa per position (explicit even if redundant — better for
   theory revision, per Pace)."
  [kb]
  ;; === agent type hierarchy ===
  (v/assert kb '(unaryPredicate agent) 'CxUniverse)
  (v/assert kb '(genl agent thing) 'CxUniverse)
  (v/assert kb '(comment agent "An entity with agency — capable of acting, perceiving, and holding capabilities.") 'CxUniverse)
  (v/assert kb '(argIsa agent 1 thing) 'CxUniverse)

  (v/assert kb '(genl person agent) 'CxUniverse)
  (v/assert kb '(comment person "An entity with social agency. Broader than human — includes constructs.") 'CxUniverse)

  ;; === agentiveBinaryPredicate metatype ===
  (v/assert kb '(unaryPredicate agentiveBinaryPredicate) 'CxUniverse)
  (v/assert kb '(genl agentiveBinaryPredicate binaryPredicate) 'CxUniverse)
  (v/assert kb '(comment agentiveBinaryPredicate "A binary predicate whose arg1 is an agent — used as the arg2 type for capability predicates.") 'CxUniverse)

  ;; === agentCapable — individual-level capability (root binary predicate) ===
  (v/assert kb '(binaryPredicate agentCapable) 'CxUniverse)
  (v/assert kb '(comment agentCapable "Asserts that an individual agent has a specific capability. (agentCapable Nyx sees) means Nyx can see.") 'CxUniverse)
  (v/assert kb '(argIsa agentCapable 1 agent) 'CxUniverse)
  (v/assert kb '(argIsa agentCapable 2 agentiveBinaryPredicate) 'CxUniverse)
  ;; capability inherits UP the predicate genl chain:
  ;; if you can seeImage, you can sees, you can perceives
  ;; (transitiveInArgInverse — renamed from argPreservingInverse in v0.6.0)
  (v/assert kb '(transitiveInArgInverse agentCapable 2 genl) 'CxUniverse)

  ;; === typeCapable — type-level capability (root binary predicate) ===
  (v/assert kb '(binaryPredicate typeCapable) 'CxUniverse)
  (v/assert kb '(comment typeCapable "Asserts that all instances of a type have a capability. (typeCapable construct perceives) means all constructs can perceive.") 'CxUniverse)
  (v/assert kb '(argIsa typeCapable 1 unaryPredicate) 'CxUniverse)
  (v/assert kb '(argIsa typeCapable 2 agentiveBinaryPredicate) 'CxUniverse)

  ;; typeVersion bridge: typeCapable → agentCapable via pair-specific generator.
  (v/assert kb
    '(set/forwardRule
      (implies
       (typeCapable ?type ?cap)
       (set/forwardRule
        (implies (?type ?agent)
                 (agentCapable ?agent ?cap)))))
    'CxUniverse)

  ;; === perception predicate hierarchy ===
  (v/assert kb '(binaryPredicate perceives) 'CxUniverse)
  (v/assert kb '(comment perceives "The most general perception predicate. Agent perceives a spatial thing.") 'CxUniverse)
  (v/assert kb '(argIsa perceives 1 agent) 'CxUniverse)
  (v/assert kb '(argIsa perceives 2 spatial_thing) 'CxUniverse)

  (v/assert kb '(binaryPredicate sees) 'CxUniverse)
  (v/assert kb '(genl sees perceives) 'CxUniverse)
  (v/assert kb '(comment sees "Visual perception. Spec of perceives.") 'CxUniverse)
  (v/assert kb '(argIsa sees 1 agent) 'CxUniverse)
  (v/assert kb '(argIsa sees 2 spatial_thing) 'CxUniverse)

  (v/assert kb '(binaryPredicate seeImage) 'CxUniverse)
  (v/assert kb '(genl seeImage sees) 'CxUniverse)
  (v/assert kb '(comment seeImage "Perceive a static image. Spec of sees.") 'CxUniverse)
  (v/assert kb '(argIsa seeImage 1 agent) 'CxUniverse)
  (v/assert kb '(argIsa seeImage 2 thing) 'CxUniverse)

  (v/assert kb '(binaryPredicate watchVideo) 'CxUniverse)
  (v/assert kb '(genl watchVideo sees) 'CxUniverse)
  (v/assert kb '(comment watchVideo "Perceive a video (temporal visual sequence). Spec of sees.") 'CxUniverse)
  (v/assert kb '(argIsa watchVideo 1 agent) 'CxUniverse)
  (v/assert kb '(argIsa watchVideo 2 thing) 'CxUniverse)

  ;; mark perception predicates as agentive
  (v/assert kb '(agentiveBinaryPredicate perceives) 'CxUniverse)
  (v/assert kb '(agentiveBinaryPredicate sees) 'CxUniverse)
  (v/assert kb '(agentiveBinaryPredicate seeImage) 'CxUniverse)
  (v/assert kb '(agentiveBinaryPredicate watchVideo) 'CxUniverse)

  ;; === construct type hierarchy ===
  (v/assert kb '(genl construct agent) 'CxUniverse)
  (v/assert kb '(comment construct "A software-substrate agent. Spec of agent, disjoint with human.") 'CxUniverse)

  (v/assert kb '(genl sightedConstruct construct) 'CxUniverse)
  (v/assert kb '(comment sightedConstruct "A construct with visual perception capabilities.") 'CxUniverse)

  (v/assert kb '(genl android sightedConstruct) 'CxUniverse)
  (v/assert kb '(comment android "A sighted construct with embodied or humanoid characteristics.") 'CxUniverse)

  kb)

;; --- Capability tests ---

(deftest-both-modes capability-direct-agent
  (assert-capability-ontology! kb)
  (testing "direct agentCapable assertion is provable"
    (v/assert kb '(construct Nyx) 'CxUniverse)
    (v/assert kb '(agentCapable Nyx seeImage) 'CxUniverse)
    (is (v/ask? kb '(agentCapable Nyx seeImage) 'CxUniverse)
        "Nyx can see images (directly asserted)")))

(deftest-both-modes capability-genl-chain
  (assert-capability-ontology! kb)
  (testing "if Nyx can see images, she can perceive (via genl chain)"
    (v/assert kb '(construct Nyx) 'CxUniverse)
    (v/assert kb '(agentCapable Nyx seeImage) 'CxUniverse)
    (is (v/ask? kb '(agentCapable Nyx sees) 'CxUniverse)
        "seeImage genl sees → agentCapable Nyx sees")
    (is (v/ask? kb '(agentCapable Nyx perceives) 'CxUniverse)
        "sees genl perceives → agentCapable Nyx perceives")))

(deftest-both-modes capability-type-to-instance
  (assert-capability-ontology! kb)
  (testing "typeCapable + type membership → agentCapable (via typeVersion generator)"
    (v/assert kb '(construct Nyx) 'CxUniverse)
    (v/assert kb '(typeCapable construct perceives) 'CxUniverse)
    (is (v/ask? kb '(agentCapable Nyx perceives) 'CxUniverse)
        "all constructs can perceive → Nyx can perceive")))

(deftest-both-modes capability-type-spec-chain
  (assert-capability-ontology! kb)
  (testing "type-level capability + genl chain + type membership"
    (v/assert kb '(android Nyx) 'CxUniverse)
    (v/assert kb '(typeCapable sightedConstruct sees) 'CxUniverse)
    (is (v/ask? kb '(agentCapable Nyx sees) 'CxUniverse)
        "sightedConstructs can see, Nyx is android (spec of sightedConstruct) → Nyx can see")
    (is (v/ask? kb '(agentCapable Nyx perceives) 'CxUniverse)
        "sees genl perceives → Nyx can also perceive")))

;; --- Defining assertions helper tests ---

(defn- assert-test-binary-parent!
  "Declare testBinaryParent as a 2-arity predicate suitable for genl from other
   binary predicates. binaryPredicate itself is a 1-arity meta-predicate in
   v0.7.0+, so genl from a 2-arity pred to binaryPredicate is rejected by arity
   descent. This shared parent has matching arity declarations."
  [kb]
  (v/assert kb '(binaryPredicate testBinaryParent) 'CxUniverse)
  (v/assert kb '(argIsa testBinaryParent 1 thing) 'CxUniverse)
  (v/assert kb '(argIsa testBinaryParent 2 thing) 'CxUniverse))

(deftest-both-modes defining-assertions-well-defined-predicate
  (testing "a fully defined binary predicate has no missing assertions"
    (assert-test-binary-parent! kb)
    (v/assert kb '(binaryPredicate wellDefined) 'CxUniverse)
    (v/assert kb '(genl wellDefined testBinaryParent) 'CxUniverse)
    (v/assert kb '(comment wellDefined "A well-defined test predicate.") 'CxUniverse)
    (v/assert kb '(argIsa wellDefined 1 thing) 'CxUniverse)
    (v/assert kb '(argIsa wellDefined 2 thing) 'CxUniverse)
    (let [result (bridge/defining-assertions kb 'wellDefined 'CxUniverse)]
      (is (= :predicate (:kind result)))
      (is (= 2 (:arity result)))
      (is (empty? (:missing result))
          "fully defined predicate should have no missing assertions"))))

(deftest-both-modes defining-assertions-missing-comment
  (testing "a predicate without a comment is flagged"
    (assert-test-binary-parent! kb)
    (v/assert kb '(binaryPredicate noComment) 'CxUniverse)
    (v/assert kb '(genl noComment testBinaryParent) 'CxUniverse)
    (v/assert kb '(argIsa noComment 1 thing) 'CxUniverse)
    (v/assert kb '(argIsa noComment 2 thing) 'CxUniverse)
    (let [missing (bridge/check-defining-assertions kb 'noComment 'CxUniverse)]
      (is (contains? missing :comment)
          "missing comment should be flagged"))))

(deftest-both-modes defining-assertions-missing-genl
  (testing "a predicate without a genl is flagged"
    (v/assert kb '(binaryPredicate noGenl) 'CxUniverse)
    (v/assert kb '(comment noGenl "Has a comment but no genl.") 'CxUniverse)
    (v/assert kb '(argIsa noGenl 1 thing) 'CxUniverse)
    (v/assert kb '(argIsa noGenl 2 thing) 'CxUniverse)
    (let [missing (bridge/check-defining-assertions kb 'noGenl 'CxUniverse)]
      (is (contains? missing :genl)
          "missing genl should be flagged"))))

(deftest-both-modes defining-assertions-missing-argisa
  (testing "a binary predicate missing arg 2 type is flagged"
    (assert-test-binary-parent! kb)
    (v/assert kb '(binaryPredicate partialArgs) 'CxUniverse)
    (v/assert kb '(genl partialArgs testBinaryParent) 'CxUniverse)
    (v/assert kb '(comment partialArgs "Only arg 1 typed.") 'CxUniverse)
    (v/assert kb '(argIsa partialArgs 1 thing) 'CxUniverse)
    ;; no argIsa for position 2
    (let [result (bridge/defining-assertions kb 'partialArgs 'CxUniverse)]
      (is (contains? (:missing result) :argIsa-2)
          "missing argIsa for position 2 should be flagged")
      (is (contains? (:present result) :argIsa-1)
          "present argIsa for position 1 should be recorded"))))

(deftest-both-modes defining-assertions-collection-type
  (testing "a non-predicate collection checks genl and comment only"
    (v/assert kb '(genl widget thing) 'CxUniverse)
    (v/assert kb '(comment widget "A test widget.") 'CxUniverse)
    (let [result (bridge/defining-assertions kb 'widget 'CxUniverse)]
      (is (= :collection (:kind result)))
      (is (nil? (:arity result)))
      (is (empty? (:missing result))
          "collection with genl + comment is fully defined"))))

(deftest-both-modes defining-assertions-convenience-predicate
  (testing "assert-well-defined? returns true for complete term"
    (v/assert kb '(genl gadget thing) 'CxUniverse)
    (v/assert kb '(comment gadget "A test gadget.") 'CxUniverse)
    (is (bridge/assert-well-defined? kb 'gadget 'CxUniverse))))

(deftest-both-modes defining-assertions-audit-capability-ontology
  (assert-capability-ontology! kb)
  (testing "agentCapable has all defining assertions"
    (let [result (bridge/defining-assertions kb 'agentCapable 'CxUniverse)]
      (is (= :predicate (:kind result)))
      (is (= 2 (:arity result)))
      (is (contains? (:present result) :argIsa-1)
          "agentCapable arg 1 (agent) should be present")
      (is (contains? (:present result) :argIsa-2)
          "agentCapable arg 2 (agentiveBinaryPredicate) should be present"))))

(deftest-both-modes perception-argisa-rejects-intangible
  (assert-capability-ontology! kb)
  (testing "sees rejects intangible arg2 via spatial_thing constraint"
    ;; TheVeryConceptOfApplebees is intangible — not a spatial_thing
    (v/assert kb '(intangible TheVeryConceptOfApplebees) 'CxUniverse)
    ;; this should be ill-formed: sees arg2 requires spatial_thing,
    ;; and an intangible thing is disjoint with spatial_thing
    (let [problems (bridge/check-guarded kb
                     '(sees Nyx TheVeryConceptOfApplebees)
                     'CxUniverse)]
      (is (seq problems)
          "sees should reject an intangible arg2 — spatial_thing required"))))

;; --- Provenance timestamp tests ---

(deftest-both-modes provenance-assert-timestamp-override
  (testing "binding *clock* overrides the :created timestamp on assert"
    (let [pinned-time 1000000000000]
      (binding [v/*clock* (constantly pinned-time)]
        (let [h (v/assert kb '(dog Tweety) 'CxTest)]
          (is (= pinned-time (:created (v/provenance kb h)))
              "assert should use the bound *clock* value"))))))

(deftest-both-modes provenance-custom-metadata
  (testing "extra provenance fields travel through assert opts"
    (let [pinned-time 1723500000000
          observed-at 1723499000000]
      (binding [v/*clock* (constantly pinned-time)]
        (let [h (v/assert kb '(dog Tweety) 'CxTest
                           {:provenance {:observedAt observed-at
                                         :source "boot-stretch"}})]
          (let [prov (v/provenance kb h)]
            (is (= pinned-time (:created prov))
                ":created comes from *clock*")
            (is (= observed-at (:observedAt prov))
                ":observedAt travels through :provenance opts")
            (is (= "boot-stretch" (:source prov))
                "arbitrary fields survive in provenance")))))))

(deftest-both-modes provenance-first-writer-wins
  (testing "re-asserting the same sentex keeps original :created timestamp"
    (let [early 1000000000000
          late  2000000000000]
      (binding [v/*clock* (constantly early)]
        (v/assert kb '(dog Tweety) 'CxTest))
      (binding [v/*clock* (constantly late)]
        (v/assert kb '(dog Tweety) 'CxTest))
      (let [h (v/handle-of kb '(dog Tweety) 'CxTest)
            prov (v/provenance kb h)]
        (is (= early (:created prov))
            "first-writer-wins: original timestamp preserved on re-assert")))))

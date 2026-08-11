;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.ontology-test
  "The shipped ontology as a *modelling* claim, where `starter-test` reads it as a schema
  that loads and reasons.

  What is pinned here is the shape of the mini-ontology rather than any one inference:
  which names are types and which are properties, that every type is placed under the
  root, that a capability is related to a kind rather than spelled as a predicate of its
  own, and how a claim about a kind reaches the kinds beneath it and stops where a nearer
  claim contradicts it.  Those are decisions somebody made, and every one of them is
  invisible to a test that only asks whether the KB answers a question.

  The genl-level exception is the centre of it.  A rule states its exception with
  `exceptWhen` (docs/exceptions.md); an *inherited* claim has no rule to except, and is
  stopped instead by a more specific claim — which works only for a default, never for a
  monotonic one, and both halves of that are tested because the asymmetry is the design."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.starter :as starter]
            [vaelii.test-util :as tu]
            [vaelii.world :as world]))

(use-fixtures :once (tu/loaded (fn [kb] (-> kb starter/load-into world/load-into))))
(use-fixtures :each (tu/neutral))

(def ^:private B 'BiologyContext)
(def ^:private N 'NaturalWorldContext)

;; ---- capabilities are related to a kind, not spelled as predicates -------

(tu/deftest-kb a-capability-is-a-noun-related-to-a-kind
  ;; `flies` as a one-place predicate says the same thing, and says it in a shape that
  ;; cannot be generalized: every further ability needs a further predicate, and nothing
  ;; relates them.  As a capability it is a term, so the abilities form a hierarchy.
  (testing "the capability names a kind of its own, under capability"
    (is (v/genl? kb 'flying 'capability))
    (is (v/genl? kb 'travelling 'capability))
    (is (v/genl? kb 'flying 'travelling)))
  (testing "and no one-place flight predicate survives beside it"
    (is (empty? (v/sentexes-matching kb '(arity flies ?n) '?ctx)))
    (is (empty? (v/sentexes-matching kb '(arity canTravel ?n) '?ctx)))))

(tu/deftest-kb what-a-kind-can-do-reaches-the-kinds-beneath-it
  ;; One sentence is stored.  Everything else here is the taxonomy being read.
  (testing "the stated claim"
    (is (v/ask? kb '(hasCapability bird flying) B)))
  (testing "and the kinds nobody wrote anything about"
    (is (v/ask? kb '(hasCapability eagle flying) B))
    (is (v/ask? kb '(hasCapability sparrow flying) B)))
  (testing "inherited rather than stored — one sentex carries all of it"
    (is (empty? (v/sentexes-matching kb '(hasCapability eagle flying) '?ctx))))
  (testing "and it climbs the capability hierarchy: what flies travels"
    (is (v/ask? kb '(hasCapability bird travelling) B))
    (is (v/ask? kb '(hasCapability eagle travelling) B))))

(tu/deftest-kb a-nearer-claim-stops-an-inherited-default-at-itself
  ;; The genl-level counterpart of `exceptWhen`.  There is no rule to block here — the
  ;; reach is the taxonomy's — so what stops it is a claim about the nearer kind.
  (testing "the excepted kind"
    (is (not (v/ask? kb '(hasCapability penguin flying) B))))
  (testing "its siblings are untouched, which is what makes this an exception"
    (is (v/ask? kb '(hasCapability eagle flying) B))
    (is (v/ask? kb '(hasCapability crow flying) B)))
  (testing "and the general claim survives being excepted"
    (is (v/ask? kb '(hasCapability bird flying) B))))

(tu/deftest-kb the-exception-is-a-claim-and-not-merely-a-silence
  ;; "Penguins do not fly" is something the KB says, not something it fails to say.  An
  ;; application can query it and argue from it; an absence supports no argument.
  (testing "at the kind"
    (is (seq (v/sentexes-matching kb '(not (hasCapability penguin flying)) '?ctx))))
  (testing "and at the member, by its own rule"
    (is (seq (v/sentexes-matching kb '(not (hasCapability Tweety flying)) N)))))

(tu/deftest-kb a-claim-about-a-kind-does-not-reach-its-members-on-its-own
  ;; The bridge is a rule, written once and deliberately, because "every bird flies" and
  ;; "this bird flies" differ by a quantifier the KB will not guess (typeToInstancePred).
  (testing "the member's flight is derived, and it is a record"
    (is (v/ask? kb '(hasCapability Sam flying) N))
    (is (seq (v/sentexes-matching kb '(hasCapability Sam flying) N))))
  (testing "the consequence rests on it and is a record too, so the cascade is visible"
    (is (seq (v/sentexes-matching kb '(hasCapability Sam travelling) N))))
  (testing "and the flightless member gets neither"
    (is (not (v/ask? kb '(hasCapability Tweety flying) N)))
    (is (empty? (v/sentexes-matching kb '(hasCapability Tweety travelling) N)))))

;; ---- the exception mechanism itself, apart from birds --------------------

(tu/deftest-kb an-inherited-default-is-undercut-and-an-inherited-monotonic-one-is-not
  ;; `argPreserving`'s contract in one test, both halves.  A default yields to a nearer
  ;; claim; a monotonic claim does not, because yielding would make a stated certainty
  ;; depend on what else got said, and the strength is exactly the author saying it must
  ;; not.  Two independent hierarchies so neither answer can come from the other.
  (tu/with-terms [carriesLoad pack_animal mule_kind hauler_kind cart_kind]
    (v/assert kb (list 'binaryPredicate carriesLoad) 'UniverseContext)
    (v/assert kb (list 'argPreserving carriesLoad 1 'genl) 'UniverseContext)
    (v/assert kb (list 'genl pack_animal 'animal) 'UniverseContext)
    (v/assert kb (list 'genl mule_kind pack_animal) 'UniverseContext)
    (v/assert kb (list 'genl hauler_kind 'animal) 'UniverseContext)
    (v/assert kb (list 'genl cart_kind hauler_kind) 'UniverseContext)
    (testing "a default reaches the subkind"
      (v/assert kb (list carriesLoad pack_animal 'Bone1) 'UniverseContext)
      (is (v/ask? kb (list carriesLoad mule_kind 'Bone1) 'UniverseContext)))
    (testing "and a nearer claim stops it there"
      (v/assert kb (list 'not (list carriesLoad mule_kind 'Bone1)) 'UniverseContext)
      (is (not (v/ask? kb (list carriesLoad mule_kind 'Bone1) 'UniverseContext)))
      (is (v/ask? kb (list carriesLoad pack_animal 'Bone1) 'UniverseContext)))
    (testing "a monotonic claim reaches the subkind the same way"
      (v/assert kb (list carriesLoad hauler_kind 'Bone1) 'UniverseContext {:strength :monotonic})
      (is (v/ask? kb (list carriesLoad cart_kind 'Bone1) 'UniverseContext)))
    (testing "and a nearer default does NOT displace it — the general claim still stands"
      (v/assert kb (list 'not (list carriesLoad cart_kind 'Bone1)) 'UniverseContext)
      (is (v/ask? kb (list carriesLoad hauler_kind 'Bone1) 'UniverseContext)
          "the monotonic claim is not undercut, which is inherit/undercut?'s contract"))
    (testing "the disagreement is a dilemma, and asking the subkind answers nothing"
      ;; Both claims survive `undercut?` — the monotonic one because it is known-true,
      ;; the negative one because nothing is more specific than it — so `verdict` sees
      ;; both polarities and returns `:ambiguous`, which `ask?` renders as false.  Not
      ;; the same as the negative winning: the general claim above is still believed.
      (is (not (v/ask? kb (list carriesLoad cart_kind 'Bone1) 'UniverseContext))))
    (testing "and the dilemma is not reported anywhere a caller would find it"
      ;; `inherit`'s own docstring calls a contrary specific claim against a monotonic
      ;; one "a contradiction to report rather than a refinement to defer to".  Nothing
      ;; is reported: the pair reaches neither list, because an inherited claim is not a
      ;; stored sentex and the clash machinery pairs handles.  Pinned as it stands so the
      ;; gap is visible rather than discovered again from a wrong answer.
      (is (empty? (filter #(= (:sentence %) (list carriesLoad cart_kind 'Bone1))
                          (map :sentence (v/conflicts kb)))))
      (is (empty? (v/contradictions kb))))))

;; ---- what is a type, and what is only a property ------------------------

(tu/deftest-kb a-type-is-a-noun-and-a-property-is-not-a-type
  ;; The naming rules make `alive` and `mortal` legal unary predicates, and nothing in
  ;; them says whether a name belongs in the genl hierarchy.  That is a modelling
  ;; decision: a type is a kind of thing and wants a noun, while a property is something
  ;; a thing *is*, and putting one in the hierarchy would make "mortal" a kind that
  ;; living things are a kind OF.  Were one wanted as a type it would be spelled for it —
  ;; `mortal_being`, not `mortal`.
  (testing "the properties the biology theory concludes are outside the hierarchy"
    (doseq [p '[alive dead awake asleep mortal warmBlooded breathesAir]]
      (is (empty? (v/sentexes-matching kb (list 'genl p '?super) '?ctx))
          (str p " is a property, not a type — it must carry no genl edge"))
      (is (seq (v/sentexes-matching kb (list 'arity p 1) '?ctx))
          (str p " is still a one-place predicate"))))
  (testing "while the kinds they are said of are types, and reach the root"
    (doseq [t '[animal bird penguin dog person physical_object capability flying]]
      (is (v/genl? kb t 'thing) (str t " must reach thing")))))

(tu/deftest-kb every-shipped-type-is-placed-under-the-root
  ;; An unplaced type is invisible to every closure the engine reads, so it is a type in
  ;; spelling only.  `islands` is the taxonomy's own count of them.
  (let [q (v/kb-quality kb)]
    (is (zero? (:islands (:taxonomy q)))
        "a type with no path to thing answers nothing and is a type in spelling only")
    (is (= (:edged (:taxonomy q)) (:rooted (:taxonomy q)))
        "every name with a genl edge reaches the root")))

(tu/deftest-kb the-types-added-for-argument-constraints-are-placed-where-they-are-used
  (testing "the two calculi types the argument declarations name"
    (is (v/genl? kb 'physical_object 'spatial_thing))
    (is (v/genl? kb 'time_point 'temporal_thing)))
  (testing "and an animal reaches spatial_thing, so a spatial relation admits one"
    (is (v/genl? kb 'dog 'spatial_thing))))

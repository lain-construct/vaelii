;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.geography-test
  "The geography tracer: CxNow and CxGeographyNow, spatiallyPartitionedByType (a region
  partitioned by a type's instances), the open neighbour relation bordersOn and its
  country spec countryBordersOn, whereabouts in CxTimeFn time contexts, the polity
  that governs a country's territory, the sole leader of an organization, and a head of
  state who acts for the polity from exile.

  Every question is answered three ways and each test names the one it expects: true
  (the sentence is proved), false (its negation is proved) and unknown (neither is).
  False is a proven negation, so a test expecting false fails on unknown and a test
  expecting unknown fails on a manufactured negative.

  The geography facts are a tracer subset of North America, stated in CxGeographyNow per
  test.  Two states and the District stand in for the instances of the classifier whose
  instances partition the fifty states and DC.  A human's whereabouts are stated in a
  (CxTimeFn CxGeographyNow (DatetimeFn …)) context.  CxTime declares that a time context
  sees its base, so each one sees CxGeographyNow with no genlCx edge stated, and orders
  each month below its year and each day below its month, so a sibling month sees the
  geography and not the whereabouts."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.space :as space]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded #(doto %
                                  (tu/load-starter!)
                                  (v/add-prover (space/spatial-prover)))))
(use-fixtures :each (tu/neutral))

(def ^:private GEO 'CxGeographyNow)

(defn- verdict
  "`:true` when `s` is proved in `ctx`, `:false` when its negation is, `:unknown` when
  neither is, and `:both` when the two are proved together."
  [kb s ctx]
  (let [t (boolean (v/ask? kb s ctx))
        f (boolean (v/ask? kb (list 'not s) ctx))]
    (cond (and t f) :both, t :true, f :false, :else :unknown)))

;; Each reader answers a boolean, so a failing `is` prints the question and not the KB.
(defn- sees? [kb c1 c2] (boolean (v/sees? kb c1 c2)))
(defn- genl? [kb sub super ctx] (boolean (v/genl? kb sub super ctx)))

(defn- assert-all! [kb ctx sentences]
  (doseq [s sentences] (v/assert kb s ctx)))

(defn- under!
  "Place each of `children` directly below `parent`."
  [kb parent & children]
  (doseq [c children] (v/assert kb (list 'genlCx c parent) 'CxUniverse)))

;; ---- time contexts ---------------------------------------------------------------

(defn- at
  "The time context of the ISO interval `iso`, read against CxGeographyNow."
  [iso]
  (list 'CxTimeFn GEO (list 'DatetimeFn iso)))

(defn- state!
  "Assert `s` in the time context of `iso` and return the context's `cx/` constant."
  [kb s iso]
  (:context (v/sentex kb (v/assert kb s (at iso)))))

;; Tracer subset of the United States: two states and the District are instances of the
;; classifier partitioning the fifty-states-and-DC region, and a territory is another
;; part of UnitedStates outside it.
(def ^:private us-facts
  '[(genl us_state_or_dc geographic_region)
    (partOfRegion UnitedStates50AndDC UnitedStates)
    (spatiallyPartitionedByType UnitedStates50AndDC us_state_or_dc)
    (us_state_or_dc WashingtonState)
    (us_state_or_dc California)
    (us_state_or_dc DistrictOfColumbia)
    (partOfRegion PuertoRico UnitedStates)
    (regionDiscreteFrom PuertoRico UnitedStates50AndDC)])

(def ^:private country-facts
  '[(country Canada)
    (country UnitedStates)
    (country Mexico)
    (countryBordersOn Canada UnitedStates)
    (countryBordersOn UnitedStates Mexico)])

(def ^:private city-facts
  '[(partOfRegion Tacoma WashingtonState)
    (partOfRegion Seattle WashingtonState)
    (regionDiscreteFrom Tacoma Seattle)])

;; ---- the contexts --------------------------------------------------------------

(tu/deftest-kb geography-sits-below-now-and-now-below-the-real-world
  (is (sees? kb GEO 'CxNow))
  (is (sees? kb 'CxNow 'CxRealWorld))
  (is (sees? kb GEO 'CxSpace))
  (testing "both are opt-in: CxWell and the upper ontology see neither"
    (doseq [c ['CxWell 'CxUniverse 'CxRealWorld]]
      (is (not (sees? kb c 'CxNow)) (str c " does not see CxNow"))
      (is (not (sees? kb c GEO)) (str c " does not see CxGeographyNow")))))

;; ---- spatiallyPartitionedByType -------------------------------------------------

(tu/deftest-kb a-classifier-partitioning-a-region-places-and-separates-its-instances
  (tu/with-terms [Whole tile_kind PartA PartB PartC Outsider Square CxTiles]
    (under! kb GEO CxTiles)
    (assert-all! kb CxTiles
                 [(list 'genl tile_kind 'spatiotemporal)
                  (list tile_kind PartA)
                  (list tile_kind PartB)
                  (list 'spatiallyPartitionedByType Whole tile_kind)
                  (list 'partOfRegion Square Whole)
                  (list 'regionDiscreteFrom Square PartA)
                  (list 'regionDiscreteFrom Square PartB)])
    (testing "an instance stated after the partition is placed as one stated before it"
      (v/assert kb (list tile_kind PartC) CxTiles))
    (testing "every instance is part of the whole"
      (doseq [p [PartA PartB PartC]]
        (is (= :true (verdict kb (list 'partOfRegion p Whole) CxTiles)) (str p))))
    (testing "two different instances are discrete, in either order"
      (doseq [[a b] [[PartA PartB] [PartB PartA] [PartA PartC] [PartC PartB]]]
        (is (= :true (verdict kb (list 'regionDiscreteFrom a b) CxTiles)) (str a " " b))))
    (testing "a region that is no instance is neither placed nor separated"
      (is (= :unknown (verdict kb (list 'partOfRegion Outsider Whole) CxTiles)))
      (is (= :unknown (verdict kb (list 'regionDiscreteFrom Outsider PartA) CxTiles))))
    (testing "no rule draws the coverage half, so a square discrete from every instance
              but one is not placed in the remaining one"
      (is (= :unknown (verdict kb (list 'partOfRegion Square PartC) CxTiles))))
    (testing "a context that does not see the partition places nothing"
      (is (= :unknown (verdict kb (list 'partOfRegion PartA Whole) GEO))))))

(tu/deftest-kb the-coverage-half-names-the-issue-it-waits-on
  (let [notes (map (comp #(nth % 2) :sentence)
                   (v/sentexes-matching kb '(implementationNote spatiallyPartitionedByType ?n) GEO))]
    (is (some #(re-find #"issues/171" %) notes)))
  (is (= :true (verdict kb '(termsRelated partitionedByType spatiallyPartitionedByType) GEO))))

(tu/deftest-kb the-district-is-discrete-from-each-state-of-the-partition
  (tu/with-terms [Straddler TerritorySquare]
    (assert-all! kb GEO us-facts)
    (assert-all! kb GEO
                 [(list 'partOfRegion Straddler 'UnitedStates50AndDC)
                  (list 'not (list 'partOfRegion Straddler 'WashingtonState))
                  (list 'not (list 'partOfRegion Straddler 'California))
                  (list 'partOfRegion TerritorySquare 'PuertoRico)])
    (testing "each instance is in the fifty-and-DC union and so in UnitedStates"
      (doseq [p '[WashingtonState California DistrictOfColumbia]]
        (is (= :true (verdict kb (list 'partOfRegion p 'UnitedStates50AndDC) GEO)))
        (is (= :true (verdict kb (list 'partOfRegion p 'UnitedStates) GEO)))))
    (testing "the District is discrete from each state"
      (is (= :true (verdict kb '(regionDiscreteFrom DistrictOfColumbia WashingtonState) GEO)))
      (is (= :true (verdict kb '(regionDiscreteFrom California DistrictOfColumbia) GEO)))
      (is (= :false (verdict kb '(partOfRegion DistrictOfColumbia California) GEO))))
    (testing "a straddler that is only not inside each state is not placed in the District"
      (is (= :unknown (verdict kb (list 'partOfRegion Straddler 'DistrictOfColumbia) GEO))))
    (testing "a square in a territory outside the fifty-and-DC union is not in the District"
      (is (= :false (verdict kb (list 'partOfRegion TerritorySquare 'DistrictOfColumbia) GEO)))
      (is (= :true (verdict kb (list 'partOfRegion TerritorySquare 'UnitedStates) GEO))))))

;; ---- whereabouts in time contexts -------------------------------------------------

(tu/deftest-kb ottoline-in-canada-in-october-is-not-in-the-united-states-and-unknown-in-november
  (let [_   (state! kb '(human Ottoline) "2026")
        oct (state! kb '(partOfRegion Ottoline Canada) "2026-10")
        nov (state! kb '(human Ottoline) "2026-11")]
    (assert-all! kb GEO country-facts)
    (testing "in October"
      (is (= :true (verdict kb '(partOfRegion Ottoline Canada) (at "2026-10"))))
      (is (= :false (verdict kb '(partOfRegion Ottoline UnitedStates) (at "2026-10")))))
    (testing "in November nothing places her"
      (is (= :unknown (verdict kb '(partOfRegion Ottoline Canada) (at "2026-11"))))
      (is (= :unknown (verdict kb '(partOfRegion Ottoline UnitedStates) (at "2026-11")))))
    (testing "both months see the geography, and neither sees the other"
      (is (sees? kb oct GEO))
      (is (sees? kb nov GEO))
      (is (not (sees? kb nov oct)))
      (is (not (sees? kb oct nov))))))

(tu/deftest-kb ottoline-in-washington-in-october-is-not-in-california-and-unknown-in-november
  (state! kb '(human Ottoline) "2026")
  (assert-all! kb GEO us-facts)
  (state! kb '(partOfRegion Ottoline WashingtonState) "2026-10")
  (state! kb '(human Ottoline) "2026-11")
  (is (= :false (verdict kb '(partOfRegion Ottoline California) (at "2026-10"))))
  (is (= :true (verdict kb '(partOfRegion Ottoline UnitedStates) (at "2026-10"))))
  (is (= :unknown (verdict kb '(partOfRegion Ottoline California) (at "2026-11"))))
  (is (= :unknown (verdict kb '(partOfRegion Ottoline WashingtonState) (at "2026-11")))))

(tu/deftest-kb ottoline-in-tacoma-in-october-is-not-in-seattle-and-unknown-in-november
  (state! kb '(human Ottoline) "2026")
  (assert-all! kb GEO us-facts)
  (assert-all! kb GEO city-facts)
  (state! kb '(partOfRegion Ottoline Tacoma) "2026-10")
  (state! kb '(human Ottoline) "2026-11")
  (is (= :false (verdict kb '(partOfRegion Ottoline Seattle) (at "2026-10"))))
  (is (= :true (verdict kb '(partOfRegion Ottoline WashingtonState) (at "2026-10"))))
  (is (= :false (verdict kb '(partOfRegion Ottoline California) (at "2026-10"))))
  (is (= :unknown (verdict kb '(partOfRegion Ottoline Seattle) (at "2026-11"))))
  (is (= :unknown (verdict kb '(partOfRegion Ottoline Tacoma) (at "2026-11")))))

(tu/deftest-kb whereabouts-stated-for-a-month-hold-on-each-of-its-days
  (state! kb '(human Ottoline) "2026")
  (assert-all! kb GEO country-facts)
  (let [oct    (state! kb '(partOfRegion Ottoline Canada) "2026-10")
        day    (state! kb '(human Ottoline) "2026-10-12")
        nov-2  (state! kb '(human Ottoline) "2026-11-02")]
    (is (= :true (verdict kb '(partOfRegion Ottoline Canada) (at "2026-10-12"))))
    (testing "the day sees its month, through the subintervalOf ordering"
      (is (sees? kb day oct))
      (is (not (sees? kb oct day))))
    (testing "a fact stated at the month is visible from a day it was never stated in"
      (tu/with-terms [Brannoc]
        (state! kb (list 'partOfRegion Brannoc 'Mexico) "2026-10")
        (is (= :true (verdict kb (list 'partOfRegion Brannoc 'Mexico) (at "2026-10-12"))))
        (is (= :false (verdict kb (list 'partOfRegion Brannoc 'UnitedStates) (at "2026-10-12"))))
        (is (= :unknown (verdict kb (list 'partOfRegion Brannoc 'Mexico) (at "2026-11-02"))))))
    (testing "a fact stated at a day is not visible from its month"
      (tu/with-terms [Brannoc]
        (state! kb (list 'partOfRegion Brannoc 'Canada) "2026-11-02")
        (is (= :unknown (verdict kb (list 'partOfRegion Brannoc 'Canada) (at "2026-11"))))
        (is (sees? kb nov-2 GEO))))))

;; CxTime's (contextArgGenlCx CxTimeFn 1) places each time context below its base, so the
;; geography reaches a day no edge was stated for and a time context of another base does
;; not reach it.
(tu/deftest-kb a-time-context-sees-the-geography-with-no-edge-stated
  (tu/with-terms [CxElsewhere]
    (under! kb 'CxUniverse CxElsewhere)
    (assert-all! kb GEO country-facts)
    (let [day   (state! kb '(human Ottoline) "2026-10-12")
          other (:context (v/sentex kb (v/assert kb '(human Ottoline)
                                                 (list 'CxTimeFn CxElsewhere
                                                       '(DatetimeFn "2026-10-12")))))
          edge  (v/handle-of kb (list 'genlCx day GEO) 'CxUniverse)]
      (is (some? edge) "the day is placed below the geography")
      (is (not (v/premise? kb edge)) "by an edge nobody stated")
      (is (sees? kb day GEO))
      (is (= :true (verdict kb '(country Canada) (at "2026-10-12"))))
      (is (sees? kb other CxElsewhere))
      (is (not (sees? kb other GEO)) "a time context of another base does not see the geography"))))

;; ---- borders and their completeness ---------------------------------------------

(tu/deftest-kb country-borders-on-is-a-spec-of-borders-on
  (is (genl? kb 'countryBordersOn 'bordersOn GEO))
  (is (genl? kb 'countryBordersOn 'externallyConnected GEO)))

(tu/deftest-kb country-borders-are-closed-only-under-the-audit-grant
  (tu/with-terms [CxBorderAudit]
    (under! kb GEO CxBorderAudit)
    (assert-all! kb GEO country-facts)
    (assert-all! kb GEO us-facts)
    (assert-all! kb GEO city-facts)
    (v/assert kb '(closedExtentForArg countryBordersOn 1 Canada) CxBorderAudit)
    (testing "a stated countryBordersOn reads as bordersOn through the genl edge"
      (is (= :true (verdict kb '(countryBordersOn Canada UnitedStates) GEO)))
      (is (= :true (verdict kb '(bordersOn Canada UnitedStates) GEO))))
    (testing "without the grant an unlisted pair is unknown"
      (is (= :unknown (verdict kb '(countryBordersOn Canada Mexico) GEO))))
    (testing "under the grant the listed pair holds and the unlisted pair is false"
      (is (= :true (verdict kb '(countryBordersOn Canada UnitedStates) CxBorderAudit)))
      (is (= :false (verdict kb '(countryBordersOn Canada Mexico) CxBorderAudit))))
    (testing "the grant closes no other position"
      (is (= :unknown (verdict kb '(countryBordersOn Mexico Canada) CxBorderAudit))))
    (testing "an unlisted city-level contact under open bordersOn stays unknown"
      (is (= :unknown (verdict kb '(bordersOn Seattle Canada) CxBorderAudit)))
      (is (= :unknown (verdict kb '(bordersOn Canada Seattle) CxBorderAudit))))))

(tu/deftest-kb a-closed-spec-leaves-the-open-relations-above-it-open
  (tu/with-terms [CxBorderAudit]
    (under! kb GEO CxBorderAudit)
    (assert-all! kb GEO country-facts)
    (v/assert kb '(closedExtentForArg countryBordersOn 1 Canada) CxBorderAudit)
    (is (= :false (verdict kb '(countryBordersOn Canada Mexico) CxBorderAudit)))
    (is (= :unknown (verdict kb '(bordersOn Canada Mexico) CxBorderAudit)))
    (is (= :unknown (verdict kb '(externallyConnected Canada Mexico) CxBorderAudit)))))

;; ---- polities and the territory they govern -------------------------------------
;; A country is the region; a polity is the body that governs it and acts, signing
;; treaties and levying taxes.  A polity is an organization and so an agent, aspatial; a
;; country is spatiotemporal; so the two are disjoint and neither is the other.

(tu/deftest-kb a-polity-is-an-organization-and-so-an-agent-and-no-country
  (is (genl? kb 'polity 'organization GEO))
  (is (genl? kb 'polity 'agent GEO))
  (is (not (genl? kb 'country 'organization GEO)) "a country stays a region")
  (is (boolean (v/disjoint? kb 'polity 'country GEO))
      "an organization is aspatial and a country spatiotemporal")
  (is (not (sees? kb 'CxUniverse GEO)) "opt-in, as the rest of the geography is"))

(tu/deftest-kb a-country-is-a-geographic-region
  (doseq [up '[geographic_region region spatial intangible spatiotemporal]]
    (is (genl? kb 'country up GEO) (str "country genl " up)))
  (is (= #{'geographic_region} (set (v/direct-genls kb 'country GEO)))
      "geographic_region is country's one parent")
  (is (genl? kb 'geographic_region 'spatiotemporal GEO))
  (is (not (genl? kb 'region 'spatiotemporal GEO))
      "a region of a mathematical space is in no time"))

(tu/deftest-kb territory-of-relates-a-polity-to-the-region-it-governs
  (is (= :true (verdict kb '(binary_predicate territoryOf) GEO)))
  (is (= :true (verdict kb '(arg territoryOf 1 polity) GEO)))
  (is (= :true (verdict kb '(arg territoryOf 2 spatial) GEO)))
  (tu/with-terms [Ardenmark ArdenmarkRealm]
    (assert-all! kb GEO [(list 'country Ardenmark)
                         (list 'polity ArdenmarkRealm)
                         (list 'territoryOf ArdenmarkRealm Ardenmark)])
    (is (= [] (v/check kb (list 'territoryOf ArdenmarkRealm Ardenmark) GEO))
        "a polity governs a country with no conviction")
    (is (= :true (verdict kb (list 'agent ArdenmarkRealm) GEO)))))

;; ---- the sole leader of an organization -------------------------------------------
;; (functionalInArg soleLeaderOf 1): one organization has at most one sole leader where
;; one context reads both, and one agent may lead several.  The leader is read per
;; context, so a succession stated in two time contexts that do not see each other is no
;; collision.

(defn- clashes-naming
  "The contradictions whose nogood holds the handle of any of `sentences` in `ctx`."
  [kb ctx sentences]
  (let [hs (set (keep #(v/handle-of kb % ctx) sentences))]
    (filter #(some hs (:nogood %)) (v/contradictions kb))))

(tu/deftest-kb sole-leader-of-is-declared-functional-in-its-leader
  (is (= :true (verdict kb '(binary_predicate soleLeaderOf) GEO)))
  (is (= :true (verdict kb '(arg soleLeaderOf 1 agent) GEO)))
  (is (= :true (verdict kb '(arg soleLeaderOf 2 organization) GEO)))
  (is (= :true (verdict kb '(functionalInArg soleLeaderOf 1) GEO)))
  (is (= :true (verdict kb '(functionalInArg soleLeaderOf 1) 'CxUniverse))
      "declared in CxSociety, so every context reads it"))

(tu/deftest-kb two-sole-leaders-of-one-polity-in-one-context-collide
  (tu/with-terms [Ardenmark Brannoc Ottoline Guild CxCourt]
    (under! kb GEO CxCourt)
    (let [a (list 'soleLeaderOf Brannoc Ardenmark)
          b (list 'soleLeaderOf Ottoline Ardenmark)]
      (assert-all! kb CxCourt [(list 'polity Ardenmark) (list 'organization Guild)
                               (list 'human Brannoc) (list 'human Ottoline)
                               a (list 'soleLeaderOf Brannoc Guild)])
      (testing "one agent may lead two organizations"
        (is (empty? (clashes-naming kb CxCourt [a (list 'soleLeaderOf Brannoc Guild)]))))
      (v/assert kb b CxCourt)
      (testing "two leaders of one organization are a nogood, not a merge"
        (let [hs #{(v/handle-of kb a CxCourt) (v/handle-of kb b CxCourt)}]
          (is (some #(= hs (set (:nogood %))) (v/contradictions kb))))
        (is (= :unknown (verdict kb (list 'equals Brannoc Ottoline) CxCourt))
            "neither fact is monotonic, so no equality is concluded")))))

(defn- in-year
  [iso]
  (list 'CxTimeFn GEO (list 'DatetimeFn iso)))

(tu/deftest-kb a-succession-stated-in-two-years-is-no-collision
  (tu/with-terms [Ardenmark Brannoc Ottoline]
    (v/assert kb (list 'polity Ardenmark) GEO)
    (let [old (list 'soleLeaderOf Brannoc Ardenmark)
          new (list 'soleLeaderOf Ottoline Ardenmark)]
      (state! kb old "2025")
      (state! kb new "2026")
      (is (= :true (verdict kb old (in-year "2025"))))
      (is (= :true (verdict kb new (in-year "2026"))))
      (is (= :unknown (verdict kb new (in-year "2025"))))
      (is (= :unknown (verdict kb old (in-year "2026"))))
      (is (empty? (concat (clashes-naming kb (in-year "2025") [old])
                          (clashes-naming kb (in-year "2026") [new])))
          "sibling years see neither each other's leader nor a collision"))))

(tu/deftest-kb the-king-is-dead-long-live-the-king
  ;; Two neighbouring days with a different sole leader each.  A day sees its month and
  ;; not its sibling, so each day reads its own leader and nothing about the other's, and
  ;; the month, which sees neither day, reads no leader at all.
  (tu/with-terms [Ardenmark Brannoc Ottoline]
    (v/assert kb (list 'polity Ardenmark) GEO)
    (let [old  (list 'soleLeaderOf Brannoc Ardenmark)
          new  (list 'soleLeaderOf Ottoline Ardenmark)
          d11  (state! kb old "2026-10-11")
          d12  (state! kb new "2026-10-12")
          oct  (state! kb (list 'human Brannoc) "2026-10")]
      (testing "each day answers its own leader"
        (is (= :true (verdict kb old (at "2026-10-11"))))
        (is (= :true (verdict kb new (at "2026-10-12")))))
      (testing "and the other day's leader is unknown, not false"
        (is (= :unknown (verdict kb new (at "2026-10-11"))))
        (is (= :unknown (verdict kb old (at "2026-10-12")))))
      (testing "a day sees its month and the month sees neither day"
        (is (sees? kb d11 oct))
        (is (sees? kb d12 oct))
        (is (not (sees? kb oct d11)))
        (is (not (sees? kb oct d12)))
        (is (not (sees? kb d11 d12)))
        (is (= :unknown (verdict kb old (at "2026-10"))))
        (is (= :unknown (verdict kb new (at "2026-10")))))
      (is (empty? (concat (clashes-naming kb (at "2026-10-11") [old])
                          (clashes-naming kb (at "2026-10-12") [new])))
          "no collision anywhere, the month included"))))

;; ---- a head of state in exile ------------------------------------------------------
;; Brannoc leads the polity of Ardenmark from Valdria, a region discrete from Ardenmark,
;; and signs a treaty there.  The signing is stated as two performings, one by Brannoc
;; and one by the polity: each is an agent, so each can intentionally initiate it.

(tu/deftest-kb brannoc-signs-a-treaty-for-ardenmark-from-exile
  (tu/with-terms [Ardenmark ArdenmarkRealm Valdria Brannoc TreatyOfCinders
                  Cairnstone Rockfall Scree Landslide CxExile]
    (under! kb GEO CxExile)
    (assert-all! kb CxExile
                 [(list 'country Ardenmark)
                  (list 'polity ArdenmarkRealm)
                  (list 'territoryOf ArdenmarkRealm Ardenmark)
                  (list 'regionDiscreteFrom Valdria Ardenmark)
                  (list 'human Brannoc)
                  (list 'soleLeaderOf Brannoc ArdenmarkRealm)
                  (list 'partOfRegion Brannoc Valdria)
                  (list 'event TreatyOfCinders)
                  (list 'performedBy TreatyOfCinders Brannoc)
                  (list 'performedBy TreatyOfCinders ArdenmarkRealm)])
    (testing "the head of state is not in the territory: Valdria is discrete from it"
      (is (= :false (verdict kb (list 'partOfRegion Brannoc Ardenmark) CxExile))))
    (testing "the treaty is performed by Brannoc and by the polity"
      (is (= :true (verdict kb (list 'performedBy TreatyOfCinders Brannoc) CxExile)))
      (is (= :true (verdict kb (list 'performedBy TreatyOfCinders ArdenmarkRealm) CxExile)))
      (is (= :true (verdict kb (list 'doneBy TreatyOfCinders ArdenmarkRealm) CxExile))))
    (testing "the polity is an agent"
      (is (= :true (verdict kb (list 'agent ArdenmarkRealm) CxExile))))
    (testing "the region is not concluded an agent, nor concluded not one"
      ;; A country is spatiotemporal and intangible, and nothing separates either from
      ;; causal or agent: a polity is disjoint from a country, but agent is not.  So the
      ;; KB leaves the question open rather than proving Ardenmark no agent.
      (is (= :unknown (verdict kb (list 'agent Ardenmark) CxExile))))
    (testing "no collision among the facts"
      (is (empty? (v/contradictions kb))))
    (testing "a rock can do an event, and a rock held to be no agent cannot perform one"
      (assert-all! kb CxExile [(list 'formation Cairnstone) (list 'formation Scree)
                               (list 'event Rockfall) (list 'event Landslide)
                               (list 'doneBy Rockfall Cairnstone)])
      (is (= :true (verdict kb (list 'doneBy Rockfall Cairnstone) CxExile)))
      (is (empty? (v/contradictions kb)) "doneBy is accepted")
      (v/assert kb (list 'not (list 'agent Scree)) CxExile)
      (v/assert kb (list 'performedBy Landslide Scree) CxExile)
      (is (seq (clashes-naming kb CxExile [(list 'not (list 'agent Scree))]))
          "performedBy's declaration concludes an agent the negation refutes"))))

;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.common-sense-qualitative-test
  "Common sense about space, time and distance — the half of the sweep that reasons
  over a *network* rather than over a cast, which is why it sits beside
  `common-sense-test` instead of inside it.

  Everything here is the same shape: state two or three relations somebody would say
  out loud, then ask for one nobody stated.  A cup in a box in a room is in the room; a
  room is not in the box the cup is in; breakfast before lunch before dinner is before
  dinner; two things each very close to a third are not far apart.  The engine gets
  there by composing base relations through an algebra's table and tightening the
  network to a fixpoint, and the point of writing them this way is that the answers are
  checkable by anybody, table or no table.  The sign arithmetic at the end is the same
  shape without a table: a tub fills while the tap beats the drain.

  All ten reasoners are registered on the fixture KB.  A network is a property of the
  stored facts either way — `possible-relations` and `qualitative-network` read it
  whether or not a prover is registered — but `ask?` is what a caller actually writes,
  and that needs the calculus in the registry."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.starter :as starter]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded (fn [kb]
                                 (starter/load-into kb)
                                 (v/add-reasoner kb :rcc8 :allen :point :cardinal
                                                 :relative :distance :duration
                                                 :metric-time :sign :calendar))))
(use-fixtures :each (tu/neutral))

(def ^:private C 'CxUniverse)

(defn- state!
  "Assert each sentence into the one context this namespace reasons in.  A network is
  read from a context's own ancestor set, so keeping every fact in one place is what makes the
  composition visible to the tightening."
  [kb & sentences]
  (doseq [s sentences] (v/assert kb s C)))

;; ---- space: what is inside what -----------------------------------------

(tu/deftest-kb a-cup-in-a-box-in-a-room-is-in-the-room
  ;; RCC-8's NTPP composed with itself is NTPP, and nothing else — so the containment
  ;; is not merely possible, it is the only relation left standing between the cup and
  ;; the room.  The derived `partOfRegion` is the weaker claim that follows from it.
  (tu/with-terms [Cup Box Room Garden]
    (state! kb (list 'nonTangentialProperPart Cup Box)
            (list 'nonTangentialProperPart Box Room)
            (list 'spatiallyDisconnected Room Garden))
    (testing "the cup is strictly inside the room, and that is the only possibility left"
      (is (= #{:ntpp} (v/possible-relations kb :rcc8 C Cup Room)))
      (is (v/ask? kb (list 'nonTangentialProperPart Cup Room) C))
      (is (v/ask? kb (list 'partOfRegion Cup Room) C)))
    (testing "and the containment does not run backwards"
      (is (not (v/ask? kb (list 'nonTangentialProperPart Room Cup) C)))
      (is (v/ask? kb (list 'nonTangentialProperPartInverse Room Cup) C)))
    (testing "what the room is cut off from, the cup inside it is cut off from too"
      (is (= #{:dc} (v/possible-relations kb :rcc8 C Cup Garden)))
      (is (v/ask? kb (list 'spatiallyDisconnected Cup Garden) C)))
    (testing "nothing said so far is impossible"
      (is (:consistent? (v/qualitative-network kb :rcc8 C))))))

(tu/deftest-kb one-arrangement-of-a-consistent-map-can-be-written-down
  ;; A network says what is possible; a scenario picks one arrangement that satisfies
  ;; all of it at once.  Extraction is deterministic — every tie breaks on content —
  ;; so the same map yields the same arrangement however the facts arrived.
  (tu/with-terms [Cup Box Room]
    (state! kb (list 'nonTangentialProperPart Cup Box)
            (list 'nonTangentialProperPart Box Room))
    (let [scenario (v/qualitative-scenario kb :rcc8 C)]
      (testing "every pair gets exactly one base relation"
        (is (= :ntpp (scenario [Cup Room])))
        (is (= :ntppi (scenario [Room Cup])))
        (is (every? keyword? (vals scenario))))
      (testing "and asking again answers the same way"
        (is (= scenario (v/qualitative-scenario kb :rcc8 C)))))))

(tu/deftest-kb a-map-that-cannot-be-drawn-says-so-rather-than-answering
  ;; The other half of a calculus: refutation.  Three intervals each before the next in
  ;; a ring is not a hard error at assert time — every fact is fine on its own — it is
  ;; a network with no solution, and a KB that answered questions from it would be
  ;; making things up.
  (tu/with-terms [CxRing X Y Z]
    (v/assert kb (list 'genlCx CxRing 'CxUniverse) 'CxUniverse)
    (doseq [s [(list 'before X Y) (list 'before Y Z) (list 'before Z X)]]
      (v/assert kb s CxRing))
    (is (not (:consistent? (v/qualitative-network kb :allen CxRing))))
    (is (nil? (v/qualitative-scenario kb :allen CxRing))
        "there is no arrangement, so none is offered")))

;; ---- time: what happened before what ------------------------------------

(tu/deftest-kb breakfast-before-lunch-before-dinner-is-before-dinner
  ;; Allen's `before` composed with itself is `before`.  `meets` composed with itself
  ;; is `before` too, and that pair is the distinction the algebra is for: two meals
  ;; that touch and two meals with a gap are different facts with the same consequence
  ;; three hops out.
  (tu/with-terms [Breakfast Lunch Dinner]
    (state! kb (list 'before Breakfast Lunch) (list 'before Lunch Dinner))
    (testing "the order nobody stated"
      (is (= #{:before} (v/possible-relations kb :allen C Breakfast Dinner)))
      (is (v/ask? kb (list 'before Breakfast Dinner) C)))
    (testing "and the one that is refuted, not merely unproven"
      (is (not (v/ask? kb (list 'after Breakfast Dinner) C)))
      (is (not (v/ask? kb (list 'overlaps Breakfast Dinner) C))))
    (testing "the derived relations that follow from it"
      (is (v/ask? kb (list 'precedes Breakfast Dinner) C))
      (is (v/ask? kb (list 'temporallyDisjoint Breakfast Dinner) C))
      (is (not (v/ask? kb (list 'sharesTimeWith Breakfast Dinner) C))))))

(tu/deftest-kb two-things-that-touch-end-to-end-still-do-not-overlap
  (tu/with-terms [Morning Noon Evening]
    (state! kb (list 'meets Morning Noon) (list 'meets Noon Evening))
    (testing "meeting twice leaves a gap — the middle interval"
      (is (= #{:before} (v/possible-relations kb :allen C Morning Evening))))
    (testing "and neither pair shares any time"
      (is (v/ask? kb (list 'temporallyDisjoint Morning Noon) C))
      (is (v/ask? kb (list 'temporallyDisjoint Morning Evening) C)))))

(tu/deftest-kb one-moment-before-another-before-a-third
  ;; The point algebra is three relations over instants rather than thirteen over
  ;; intervals, and it is spelled apart from Allen's on purpose: `before` is about
  ;; stretches of time, `instantBefore` about moments.
  (tu/with-terms [Dawn Noon Dusk]
    (state! kb (list 'instantBefore Dawn Noon) (list 'instantBefore Noon Dusk))
    (is (= #{:before} (v/possible-relations kb :point C Dawn Dusk)))
    (is (v/ask? kb (list 'instantBefore Dawn Dusk) C))
    (testing "the ≤ that follows, and the = that is refuted"
      (is (v/ask? kb (list 'instantNotAfter Dawn Dusk) C))
      (is (not (v/ask? kb (list 'instantEqual Dawn Dusk) C))))))

;; ---- direction: which way is it ------------------------------------------

(tu/deftest-kb north-of-something-east-of-something-is-northeast-of-it
  ;; Cardinal direction constrains two axes independently, so composing a pure north
  ;; with a pure east pins both at once — the strongest thing a single direction fact
  ;; can say, out of two that each said half of it.
  (tu/with-terms [Village Farm Mill]
    (state! kb (list 'northOf Farm Village) (list 'eastOf Mill Farm))
    (is (= #{:ne} (v/possible-relations kb :cardinal C Mill Village)))
    (is (v/ask? kb (list 'northeastOf Mill Village) C))
    (testing "and the weaker single-axis reading follows from it"
      (is (v/ask? kb (list 'northwardOf Mill Village) C))
      (is (v/ask? kb (list 'eastwardOf Mill Village) C)))
    (testing "the converse is the mirror, not the same claim"
      (is (v/ask? kb (list 'southwestOf Village Mill) C))
      (is (not (v/ask? kb (list 'northeastOf Village Mill) C))))))

(tu/deftest-kb left-of-a-thing-left-of-a-thing-is-still-to-the-left
  ;; Relative direction reads from a viewpoint, and here the viewpoint is the context —
  ;; which is why two contexts can hold opposite left-of claims about one pair without
  ;; either being wrong.  Within one frame it composes like any algebra.
  (tu/with-terms [Chair Table Lamp]
    (state! kb (list 'leftOf Chair Table) (list 'leftOf Table Lamp))
    (is (= #{:left} (v/possible-relations kb :relative C Chair Lamp)))
    (is (v/ask? kb (list 'leftwardOf Chair Lamp) C))
    (is (v/ask? kb (list 'rightOf Lamp Chair) C))))

;; ---- distance: how far is it ---------------------------------------------

(tu/deftest-kb two-things-very-close-to-a-third-are-not-far-apart
  ;; Qualitative distance composes by the triangle inequality over class bounds, so
  ;; the answer is a *range* of classes rather than one: two very-close hops leave the
  ;; ends anywhere from co-located to close.  That the composition does not collapse to
  ;; one class is the honest answer, and the derived `withinNearDistanceOf` is what a
  ;; caller usually wants from it.
  (tu/with-terms [Nest Branch Trunk]
    (state! kb (list 'veryCloseTo Nest Branch) (list 'veryCloseTo Branch Trunk))
    (is (= #{:co :very-close :close} (v/possible-relations kb :distance C Nest Trunk)))
    (testing "so the disjunction that covers all three answers"
      (is (v/ask? kb (list 'withinNearDistanceOf Nest Trunk) C)))
    (testing "and no single class is entailed"
      (is (not (v/ask? kb (list 'veryCloseTo Nest Trunk) C)))
      (is (not (v/ask? kb (list 'closeTo Nest Trunk) C))))
    (testing "while what is ruled out is ruled out"
      (is (not (v/ask? kb (list 'farFrom Nest Trunk) C)))
      (is (not (v/ask? kb (list 'beyondFarDistanceFrom Nest Trunk) C))))))

;; ---- duration and metric time: how long, and how far apart ---------------

(tu/deftest-kb half-an-hour-and-an-hour-are-ninety-minutes
  ;; The quantitative half of interval reasoning, over the shipped unit table: a total
  ;; is summed in the dimension's base unit and rendered there, so two lengths written
  ;; in different units add without anybody converting them first.
  (tu/with-terms [Breakfast Lunch]
    (state! kb (list 'length Breakfast '(QuantityFn 30 Minute))
            (list 'length Lunch '(QuantityFn 1 Hour)))
    (testing "the sum, in seconds because Second is the base unit of Duration"
      (is (= '(QuantityFn 5400 Second)
             (get (tu/sole-answer (v/ask kb (list 'totalDuration (list 'list Breakfast Lunch) '?d) C))
                  '?d))))
    (testing "and a ground total checks in whatever unit it is written"
      (is (v/ask? kb (list 'totalDuration (list 'list Breakfast Lunch)
                           '(QuantityFn 90 Minute)) C)))))

(tu/deftest-kb two-meals-that-cannot-overlap-overlap-for-no-time-at-all
  ;; Where the qualitative and the quantitative meet: the Allen relation says the two
  ;; share no time, so the overlap is exactly zero rather than an interval nobody can
  ;; narrow — computed from the relation, not from the lengths.
  (tu/with-terms [Breakfast Lunch]
    (state! kb (list 'before Breakfast Lunch)
            (list 'length Breakfast '(QuantityFn 30 Minute))
            (list 'length Lunch '(QuantityFn 1 Hour)))
    (is (= '(QuantityFn 0 Second)
           (get (tu/sole-answer (v/ask kb (list 'overlapDuration Breakfast Lunch '?d) C)) '?d)))))

(tu/deftest-kb six-hours-then-six-hours-is-twelve-hours
  ;; Metric time over the same instants: bounds on a gap, closed by all-pairs shortest
  ;; paths.  Nobody wrote the dawn-to-dusk gap, and the KB answers it as an exact
  ;; measure because both legs were exact.
  (tu/with-terms [Dawn Noon Dusk]
    (state! kb (list 'temporalDistance Dawn Noon '(QuantityFn 6 Hour))
            (list 'temporalDistance Noon Dusk '(QuantityFn 6 Hour)))
    (testing "the composed gap, bound as a measure"
      (is (= '(QuantityFn 43200 Second)
             (get (tu/sole-answer (v/ask kb (list 'temporalDistance Dawn Dusk '?d) C)) '?d))))
    (testing "and checked against the way a person would write it"
      (is (v/ask? kb (list 'temporalDistance Dawn Dusk '(QuantityFn 12 Hour)) C))
      (is (not (v/ask? kb (list 'temporalDistance Dawn Dusk '(QuantityFn 11 Hour)) C))))))

;; ---- the calendar: what a date already says ------------------------------

(tu/deftest-kb march-is-inside-the-millennium-and-february-runs-into-it
  ;; Nobody states anything at all here.  A year, a month and a day carry their own
  ;; extent in their fields, so where they sit relative to one another is arithmetic —
  ;; and the moments they lie between are computed the same way, half-open, so the end
  ;; of one is the start of the next.
  (testing "a month is inside its year, and the first and last share an end with it"
    (is (v/ask? kb '(during (MonthFn 2000 3) (YearFn 2000)) C))
    (is (v/ask? kb '(starts (MonthFn 2000 1) (YearFn 2000)) C))
    (is (v/ask? kb '(finishes (MonthFn 2000 12) (YearFn 2000)) C))
    (is (v/ask? kb '(subintervalOf (DayFn 2000 3 15) (YearFn 2000)) C)))
  (testing "consecutive terms touch, so they meet — before wants a gap, and there is none"
    (is (v/ask? kb '(meets (MonthFn 2000 2) (MonthFn 2000 3)) C))
    (is (v/ask? kb '(precedes (YearFn 1999) (YearFn 2000)) C))
    (is (not (v/ask? kb '(before (YearFn 1999) (YearFn 2000)) C)))
    (is (v/ask? kb '(before (YearFn 1999) (YearFn 2001)) C)))
  (testing "and the moment the year turns has one name, whichever side you ask from"
    (is (= (get (tu/sole-answer (v/ask kb '(endOf (YearFn 1999) ?i) C)) '?i)
           (get (tu/sole-answer (v/ask kb '(startOf (YearFn 2000) ?i) C)) '?i)
           '(InstantFn 2000 1 1 0 0 0)))
    (is (v/ask? kb '(instantBefore (InstantFn 2000 1 1 0 0 0)
                                   (InstantFn 2000 3 1 0 0 0)) C))))

;; ---- signs: which way a quantity is going -------------------------------

(tu/deftest-kb the-tub-fills-while-the-tap-runs-faster-than-the-drain
  ;; No numbers anywhere.  Two flows with a sign apiece, a sum, and the one comparison
  ;; that decides which of the two wins — which is how anybody would say it, and the
  ;; only thing about a tub a person actually knows.
  (tu/with-terms [Tap Drain NetFlow WaterLevel]
    (state! kb (list 'signOf Tap 'SignPositive)
            (list 'signOf Drain 'SignNegative)
            (list 'qualitativeSum Tap Drain NetFlow)
            (list 'derivativeOf NetFlow WaterLevel))
    (testing "without the comparison the net flow could go either way, and the KB
              declines all three answers rather than picking one"
      (is (empty? (v/ask kb (list 'signOf NetFlow '?s) C)))
      (is (empty? (v/ask kb (list 'trendOf WaterLevel '?s) C))))
    (testing "the tap runs faster than the drain, so the tub fills"
      (state! kb (list 'greaterInMagnitudeThan Tap Drain))
      (is (v/ask? kb (list 'signOf NetFlow 'SignPositive) C))
      (is (v/ask? kb (list 'trendOf WaterLevel 'SignPositive) C)))))

(tu/deftest-kb a-cooling-bodys-temperature-falls
  ;; One edge and one sign: a rate known negative makes the quantity it is the rate of
  ;; fall, and the KB will also say outright that it is not rising — the three values
  ;; being exhaustive, ruling two out proves the third.
  (tu/with-terms [HeatLoss BodyTemperature]
    (state! kb (list 'derivativeOf HeatLoss BodyTemperature)
            (list 'signOf HeatLoss 'SignNegative))
    (is (v/ask? kb (list 'trendOf BodyTemperature 'SignNegative) C))
    (is (v/ask? kb (list 'not (list 'trendOf BodyTemperature 'SignPositive)) C))))

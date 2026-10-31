;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.quantity-test
  "The measure-evaluating quantity prover (`vaelii.impl.provers/QuantityProver`): measure
  comparisons — `sameQuantity`, `quantityLessThan`, `quantityGreaterThan`,
  `quantityLessThanOrEqual`, `quantityGreaterThanOrEqual` — that normalize a measure
  `(QuantityFn N Unit)` / `(QuantityIntervalFn Lo Hi Unit)` against the KB's
  `dimensionOf` / `conversionFactor` table and compare.  Check-only over ground
  measures; a dimension mismatch is never comparable and never throws."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.host.core-context :as core-context]
            [vaelii.impl.nat-read :as nat-read]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.types.prover :as prover-types]
            [vaelii.test-util :as tu]))

;; one KB per namespace: the upper layer, whose measure.txt declares QuantityFn /
;; QuantityIntervalFn unreifiable and documents the comparison and table predicates.
(use-fixtures :once (tu/loaded tu/load-core!))
(use-fixtures :each (tu/neutral))

(def ^:private C 'CxUniverse)

;; ---- same unit -----------------------------------------------------------

(tu/deftest-kb same-unit-comparisons-need-no-table
  (testing "a measure's own unit is its dimension, so same-unit compares directly"
    (is (v/ask? kb '(quantityLessThan (QuantityFn 5 Meter) (QuantityFn 7 Meter)) C))
    (is (not (v/ask? kb '(quantityLessThan (QuantityFn 7 Meter) (QuantityFn 5 Meter)) C))
        "the reverse fails")
    (is (v/ask? kb '(quantityGreaterThan (QuantityFn 7 Meter) (QuantityFn 5 Meter)) C))
    (is (v/ask? kb '(sameQuantity (QuantityFn 5 Meter) (QuantityFn 5 Meter)) C))
    (is (v/ask? kb '(quantityLessThanOrEqual (QuantityFn 5 Meter) (QuantityFn 5 Meter)) C))
    (is (v/ask? kb '(quantityGreaterThanOrEqual (QuantityFn 5 Meter) (QuantityFn 5 Meter)) C))))

;; ---- cross-unit conversion ----------------------------------------------

(defn- load-mass-table [kb]
  (v/assert kb '(dimensionOf Gram Mass)               C)
  (v/assert kb '(dimensionOf Kilogram Mass)           C)
  (v/assert kb '(conversionFactor Gram Kilogram 0.001) C)
  (v/assert kb '(conversionFactor Kilogram Kilogram 1) C))   ; Kilogram is its own base

(tu/deftest-kb cross-unit-normalizes-to-the-base
  (load-mass-table kb)
  (testing "5 kg = 5000 g once both are normalized to kilograms"
    (is (v/ask? kb '(sameQuantity (QuantityFn 5 Kilogram) (QuantityFn 5000 Gram)) C))
    (is (v/ask? kb '(sameQuantity (QuantityFn 5000 Gram) (QuantityFn 5 Kilogram)) C)
        "symmetric in the two directions"))
  (testing "3 kg > 2000 g, 500 g < 1 kg"
    (is (v/ask? kb '(quantityGreaterThan (QuantityFn 3 Kilogram) (QuantityFn 2000 Gram)) C))
    (is (v/ask? kb '(quantityLessThan (QuantityFn 500 Gram) (QuantityFn 1 Kilogram)) C))
    (is (not (v/ask? kb '(sameQuantity (QuantityFn 5 Kilogram) (QuantityFn 4000 Gram)) C)))))

;; ---- dimension mismatch --------------------------------------------------

(tu/deftest-kb a-dimension-mismatch-is-never-comparable
  (v/assert kb '(dimensionOf Kilogram Mass)   C)
  (v/assert kb '(dimensionOf Meter Length)    C)
  (testing "mass vs length is neither equal nor ordered — and never throws"
    (doseq [pred '[sameQuantity quantityLessThan quantityGreaterThan
                   quantityLessThanOrEqual quantityGreaterThanOrEqual]]
      (is (not (v/ask? kb (list pred '(QuantityFn 5 Kilogram) '(QuantityFn 5 Meter)) C))
          (str pred " must fail across dimensions"))
      (is (not (v/ask? kb (list pred '(QuantityFn 5 Meter) '(QuantityFn 5 Kilogram)) C))))))

;; ---- intervals -----------------------------------------------------------

(tu/deftest-kb interval-comparisons-use-the-necessary-reading
  (v/assert kb '(dimensionOf Meter Length) C)
  (testing "a definite (necessary) order: it must hold of every point of each interval"
    (is (v/ask? kb '(quantityLessThan (QuantityIntervalFn 1 2 Meter) (QuantityFn 5 Meter)) C)
        "all of [1,2] is strictly below 5")
    (is (v/ask? kb '(quantityGreaterThan (QuantityFn 5 Meter) (QuantityIntervalFn 1 2 Meter)) C))
    (is (not (v/ask? kb '(quantityLessThan (QuantityIntervalFn 1 4 Meter)
                                           (QuantityIntervalFn 3 6 Meter)) C))
        "overlapping intervals are not necessarily ordered"))
  (testing "the boundary distinguishes strict < from <="
    (is (not (v/ask? kb '(quantityLessThan (QuantityIntervalFn 1 2 Meter) (QuantityFn 2 Meter)) C))
        "hi=2 is not strictly below 2")
    (is (v/ask? kb '(quantityLessThanOrEqual (QuantityIntervalFn 1 2 Meter) (QuantityFn 2 Meter)) C)
        "but it is at most 2"))
  (testing "an interval equals only the identical interval"
    (is (v/ask? kb '(sameQuantity (QuantityIntervalFn 1 2 Meter) (QuantityIntervalFn 1 2 Meter)) C))
    (is (not (v/ask? kb '(sameQuantity (QuantityFn 2 Meter) (QuantityIntervalFn 1 2 Meter)) C)))))

;; ---- rule antecedent -----------------------------------------------------

(tu/deftest-kb a-quantity-comparison-in-a-rule-antecedent-derives
  (tu/with-terms [heavy Boulder Pebble]
    (v/assert kb '(dimensionOf Kilogram Mass) C)
    ;; the comparison is a deferred antecedent, placed after (mass ?o ?q) binds ?q
    (v/assert-rule kb [(list 'mass '?o '?q)
                       (list 'quantityGreaterThan '?q '(QuantityFn 100 Kilogram))]
                   (list heavy '?o) C {:direction :forward})
    (v/assert kb (list 'mass Boulder '(QuantityFn 150 Kilogram)) C)
    (v/assert kb (list 'mass Pebble  '(QuantityFn 50 Kilogram))  C)
    (testing "the rule fires only for the object over the threshold"
      (is (v/ask? kb (list heavy Boulder) C) "150 kg > 100 kg ⇒ heavy")
      (is (not (v/ask? kb (list heavy Pebble) C)) "50 kg is not > 100 kg"))))

;; ---- structural pass-through (01's check) --------------------------------

(tu/deftest-kb a-stored-measure-keeps-its-compound-and-is-never-minted
  (tu/with-terms [Obj]
    (let [m '(QuantityFn 5 Kilogram)
          h (v/assert kb (list 'mass Obj m) C)]
      (testing "the structural NAT is stored structurally, not reified to a constant"
        (is (= (list 'mass Obj m) (:sentence (v/sentex kb h))))
        (is (nil? (nat-read/dedup-constant kb m)) "no constant was minted for it"))
      (testing "it round-trips through query unchanged"
        (is (seq (v/sentexes-matching kb (list 'mass Obj m) '?ctx)))))))

;; ---- float policy: an epsilon tolerance ----------------------------------

(tu/deftest-kb quantity-equality-is-an-epsilon-tolerance
  (testing "a gap within the tolerance counts as the same quantity"
    (binding [provers/*quantity-tolerance* 0.001]
      (is (v/ask? kb '(sameQuantity (QuantityFn 1.0 Meter) (QuantityFn 1.0005 Meter)) C))))
  (testing "a gap beyond the tolerance does not"
    (binding [provers/*quantity-tolerance* 1e-9]
      (is (not (v/ask? kb '(sameQuantity (QuantityFn 1.0 Meter) (QuantityFn 1.0005 Meter)) C)))))
  (testing "the default tolerance absorbs cross-unit floating-point rounding"
    (v/assert kb '(dimensionOf MilliMeter Length)               C)
    (v/assert kb '(dimensionOf Meter Length)                    C)
    (v/assert kb '(conversionFactor MilliMeter Meter 0.001)     C)
    (is (v/ask? kb '(sameQuantity (QuantityFn 1000 MilliMeter) (QuantityFn 1 Meter)) C)
        "1000 × 0.001 rounds to 1.0 within 1e-9")))

(tu/deftest-kb the-rounding-grid-is-the-bound-tolerances
  ;; The grid a computed magnitude is snapped to and the slack the comparisons allow are
  ;; one policy.  Rebinding the tolerance without moving the grid leaves two magnitudes
  ;; that compare equal rendering as two different figures — an answer that is `=` to
  ;; itself under the comparison and not under `=`.
  (testing "under a coarse tolerance, two magnitudes inside it compare equal"
    (binding [provers/*quantity-tolerance* 1e-3]
      (is (v/ask? kb '(sameQuantity (QuantityFn 2.0 Meter) (QuantityFn 2.0005 Meter)) C)
          "5e-4 apart is inside a 1e-3 tolerance")
      (testing "and the grid is that tolerance's — three decimal places, not nine"
        (is (= 2.001 (provers/round-magnitude 2.0005)))
        (is (= 2 (provers/round-magnitude 2.0004))
            "noise below the bound tolerance is snapped away rather than rendered"))))
  (testing "the shipped tolerance keeps the nine places the float noise needs"
    (binding [provers/*quantity-tolerance* 1e-9]
      (is (= 2.0004 (provers/round-magnitude 2.0004)) "nothing at 1e-4 is noise at 1e-9")
      (is (= 9000 (provers/round-magnitude 9000.0000000000004))
          "float noise below the grid is snapped away, and a whole number comes back long"))))

;; ---- a table the KB disagrees with itself about --------------------------
;; Every match of a table read carries the same bindings when one declaration is merely
;; restated, and different ones when the KB has declared a unit twice over.  Reading the
;; first match would answer whichever the index yields — a handle order — so a second
;; declaration is declined rather than adjudicated, and the answer is the same in either
;; load order.

(defn- factor-of
  "How `unit` normalizes, as `[dimension magnitude base-unit]` for one of it."
  [kb unit]
  (let [[dim lo _] (provers/normalize-quantity kb (list 'QuantityFn 1 unit) C)]
    [dim lo (provers/base-unit-of kb unit C)]))

(tu/deftest-kb one-declaration-restated-is-still-one-declaration
  (tu/with-terms [CxInner]
    (v/assert kb (list 'genlCx CxInner C) C)
    (v/assert kb '(dimensionOf Gram Mass) C)
    (v/assert kb '(conversionFactor Gram Kilogram 0.001) C)
    (v/assert kb '(conversionFactor Gram Kilogram 0.001) CxInner)
    (testing "restating a factor in a context of the ancestor set is not a disagreement — the
              matches carry the same bindings and collapse to one"
      (is (= '[Mass 0.001 Kilogram] (factor-of kb 'Gram)))
      (is (= '[Mass 0.001 Kilogram]
             (let [[dim lo _] (provers/normalize-quantity kb '(QuantityFn 1 Gram) CxInner)]
               [dim lo (provers/base-unit-of kb 'Gram CxInner)]))))))

(tu/deftest-kb two-conversion-factors-for-one-unit-are-no-conversion-factor
  (v/assert kb '(dimensionOf Gram Mass) C)
  (v/assert kb '(conversionFactor Gram Kilogram 0.001) C)
  (v/assert kb '(conversionFactor Gram Kilogram 0.002) C)
  (testing "the KB cannot say how heavy a gram is, so it says nothing: the unit is its own
            base and converts by 1, whichever of the two was written first"
    (is (= '[Mass 1 Gram] (factor-of kb 'Gram))))
  (testing "which makes it comparable with itself and with nothing else — a wrong number
            is what taking either declaration would have produced"
    (is (v/ask? kb '(sameQuantity (QuantityFn 5 Gram) (QuantityFn 5 Gram)) C))
    (is (not (v/ask? kb '(sameQuantity (QuantityFn 5000 Gram) (QuantityFn 5 Kilogram)) C)))))

(tu/deftest-kb a-unit-with-a-dimension-and-no-factor-compares-with-no-unit-of-another-base
  ;; The unit is its own base at factor 1, so its magnitudes are not in the dimension's
  ;; base unit, and a comparison or a sum with a metre has no answer.  A factor row naming
  ;; the unit itself states the same reading.
  (tu/with-terms [Foot spanOf Trail]
    (v/assert kb (list 'dimensionOf Foot 'Length) C)
    (let [foot (list 'QuantityFn 1 Foot)]
      (doseq [pred '[sameQuantity quantityLessThan quantityGreaterThan
                     quantityLessThanOrEqual quantityGreaterThanOrEqual]]
        (is (not (v/ask? kb (list pred foot '(QuantityFn 1 Meter)) C)) (str pred)))
      (is (v/ask? kb (list 'sameQuantity foot foot) C) "the unit compares with itself")
      (v/assert kb (list spanOf Trail foot) C)
      (v/assert kb (list spanOf Trail '(QuantityFn 1 Meter)) C)
      (is (empty? (v/ask kb (list 'agg/sum '?n '?v (list spanOf Trail '?v)) C))
          "a sum over a foot and a metre has no answer")
      (v/assert kb (list 'conversionFactor Foot Foot 1) C)
      (is (not (v/ask? kb (list 'sameQuantity foot '(QuantityFn 1 Meter)) C)))
      (is (empty? (v/ask kb (list 'agg/max '?n '?v (list spanOf Trail '?v)) C))
          "nor a maximum, with the unit's own factor row stated"))))

(tu/deftest-kb a-base-and-a-factor-are-one-reading
  (v/assert kb '(dimensionOf Gram Mass) C)
  (v/assert kb '(conversionFactor Gram Kilogram 0.001) C)
  (v/assert kb '(conversionFactor Gram Milligram 1000) C)
  (testing "two declarations naming different bases are declined together — a base taken
            from one and a factor from the other would convert into a unit nothing said it
            converts to"
    (is (= '[Mass 1 Gram] (factor-of kb 'Gram)))))

(tu/deftest-kb two-dimensions-for-one-unit-are-no-dimension
  (v/assert kb '(dimensionOf Gram Mass) C)
  (v/assert kb '(dimensionOf Gram Length) C)
  (testing "the unit falls back to being its own dimension, so it compares with itself
            rather than with whichever dimension is indexed first"
    (is (= 'Gram (first (factor-of kb 'Gram))))
    (is (not (v/ask? kb '(sameQuantity (QuantityFn 1 Gram) (QuantityFn 1 Kilogram)) C)))))

(tu/deftest-kb the-table-answers-the-same-in-either-load-order
  ;; the invariant under all four above: same knowledge, two orders, one answer
  (v/assert kb '(dimensionOf Gram Mass) C)
  (v/assert kb '(conversionFactor Gram Kilogram 0.001) C)
  (v/assert kb '(conversionFactor Gram Kilogram 0.002) C)
  (let [forward (factor-of kb 'Gram)]
    (tu/with-neutral-kb [other #(doto (tu/isolated-fresh)
                                  (tu/load-core!))]
      (v/assert other '(conversionFactor Gram Kilogram 0.002) C)
      (v/assert other '(conversionFactor Gram Kilogram 0.001) C)
      (v/assert other '(dimensionOf Gram Mass) C)
      (is (= forward
             (let [[dim lo _] (provers/normalize-quantity other '(QuantityFn 1 Gram) C)]
               [dim lo (provers/base-unit-of other 'Gram C)]))))))

(tu/deftest-kb an-aggregate-over-two-bases-has-no-answer-in-either-arrival-order
  ;; Two units of one dimension declaring **different bases** — a KB that has broken the
  ;; direct-to-base contract, so their magnitudes are in incomparable scales, and a sum
  ;; over the two has no answer, as a comparison between them has none.
  (let [table! (fn [k]
                 (v/assert k '(dimensionOf Furlong Distance) C)
                 (v/assert k '(dimensionOf Chain Distance) C)
                 (v/assert k '(conversionFactor Furlong Rod 40) C)
                 (v/assert k '(conversionFactor Chain Link 4) C))
        goal   '(agg/sum ?n ?v (spanOf Trail ?v))]
    (table! kb)
    (v/assert kb '(spanOf Trail (QuantityFn 1 Furlong)) C)
    (v/assert kb '(spanOf Trail (QuantityFn 2 Chain)) C)
    (tu/with-neutral-kb [other #(doto (tu/isolated-fresh)
                                  (tu/load-core!))]
      (table! other)
      (v/assert other '(spanOf Trail (QuantityFn 2 Chain)) C)
      (v/assert other '(spanOf Trail (QuantityFn 1 Furlong)) C)
      (is (= [[] []] [(v/ask kb goal C) (v/ask other goal C)]))
      (is (not (v/ask? kb '(sameQuantity (QuantityFn 1 Furlong) (QuantityFn 10 Chain)) C))))))

;; ---- a functional measure slot -------------------------------------------

(defn- try-second-weight
  "`:stored`, or the refusal's `[:type :violation]`, for `try-assert` of a second weight."
  [kb s]
  (try (v/try-assert kb s C) :stored
       (catch clojure.lang.ExceptionInfo e ((juxt :type :violation) (ex-data e)))))

(tu/deftest-kb a-functional-measure-slot-holds-one-magnitude-in-any-unit
  ;; weightOf is functional (measure.txt), and its second filler agrees with 20 kg
  ;; exactly when the two can denote one magnitude
  (doseq [[m agrees?] '[[(QuantityFn 20000 Gram)                true]
                        [(QuantityIntervalFn 18 22 Kilogram)    true]
                        [(QuantityIntervalFn 18000 22000 Gram)  true]
                        [(QuantityIntervalFn 20 25 Kilogram)    true]
                        [(QuantityFn 30 Kilogram)               false]
                        [(QuantityIntervalFn 21 25 Kilogram)    false]
                        [(QuantityFn 20 Meter)                  false]]]
    (tu/with-terms [Muffet Rex]
      (v/assert kb (list 'weightOf Muffet '(QuantityFn 20 Kilogram)) C)
      (v/assert kb (list 'weightOf Rex '(QuantityFn 20 Kilogram)) C)
      (is (= (if agrees? :stored [:definitional-clash :functional])
             (try-second-weight kb (list 'weightOf Muffet m)))
          (str "try-assert " m))
      (is (= (not agrees?) (tu/stored-in-clash? kb (list 'weightOf Rex m) C))
          (str "assert " m)))))

(tu/deftest-kb a-unit-row-arriving-or-leaving-moves-a-functional-measure-clash
  (tu/with-terms [Muffet Pound]
    (let [kg     (list 'weightOf Muffet '(QuantityFn 1 Kilogram))
          lb     (list 'weightOf Muffet (list 'QuantityFn 2 Pound))
          factor (list 'conversionFactor Pound 'Kilogram 0.5)
          clash? (fn [] (boolean (some #(contains? (:nogood %) (v/handle-of kb lb C))
                                       (concat (v/contradictions kb) (v/conflicts kb)))))]
      (v/assert kb kg C)
      (v/assert kb lb C)
      (is (clash?) "a unit the table does not declare is its own dimension")
      (v/assert kb (list 'dimensionOf Pound 'Mass) C)
      (v/assert kb factor C)
      (is (not (clash?)) "two pounds at half a kilogram each is one kilogram")
      (is (and (v/ask? kb kg C) (v/ask? kb lb C)))
      (v/retract! kb (v/handle-of kb factor C))
      (is (clash?) "the factor retracted, the pound compares with no kilogram"))))

(tu/deftest-kb a-conclusion-drawn-through-a-shipped-unit-row-keeps-its-strength
  ;; the firing names the Gram and Kilogram rows among its antecedents
  (tu/with-terms [heavy Boulder]
    (v/assert-rule kb [(list 'mass '?o '?q)
                       (list 'quantityGreaterThan '?q '(QuantityFn 100 Gram))]
                   (list heavy '?o) C {:direction :forward :strength :monotonic})
    (v/assert kb (list 'mass Boulder '(QuantityFn 1 Kilogram)) C {:strength :monotonic})
    (is (= :monotonic (v/defeat-class kb (v/handle-of kb (list heavy Boulder) C))))))

;; ---- check-only: an open goal is refused, not enumerated -----------------

(tu/deftest-kb an-open-measure-goal-is-refused
  (let [applicable? #(prover-types/applicable? (provers/->QuantityProver) kb % C)]
    (testing "both arguments ground measures ⇒ claimed"
      (is (applicable? '(sameQuantity (QuantityFn 5 Kilogram) (QuantityFn 5 Kilogram)))))
    (testing "a variable, a bare number, or a non-measure compound ⇒ refused"
      (is (not (applicable? '(sameQuantity ?x (QuantityFn 5 Kilogram)))))
      (is (not (applicable? '(sameQuantity (QuantityFn ?n Kilogram) (QuantityFn 5 Kilogram)))))
      (is (not (applicable? '(sameQuantity 5 (QuantityFn 5 Kilogram)))))
      (is (not (applicable? '(sameQuantity (Frobnicate 5) (QuantityFn 5 Kilogram))))))
    (testing "the quantity prover never appears in the plan for an open measure goal"
      (is (not (contains? (set (map :prover (v/query-plan kb '(sameQuantity ?x (QuantityFn 5 Kilogram)) C)))
                          "QuantityProver"))))))

;; ---- ontology: the vocabulary is declared and documented -----------------

(tu/deftest-kb the-measure-vocabulary-is-documented
  (doseq [term '[QuantityFn QuantityIntervalFn dimensionOf conversionFactor
                 sameQuantity quantityLessThan quantityGreaterThan
                 quantityLessThanOrEqual quantityGreaterThanOrEqual]]
    (is (= 1 (count (core-context/comment-of kb term))) (str "comment for " term))
    (is (string? (first (core-context/comment-of kb term)))))
  (testing "the measure functions are declared unreifiable"
    (is (v/has-prop? kb :unreifiable 'QuantityFn))
    (is (v/has-prop? kb :unreifiable 'QuantityIntervalFn))))

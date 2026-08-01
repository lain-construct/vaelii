(ns vaelii.stp-test
  "The metric temporal layer (`vaelii.impl.stp`): bounds on the gap between two instants,
  closed by all-pairs shortest paths, and the bridge that lets those bounds narrow what
  Allen's algebra leaves open.

  Two halves.  The first tests the **algorithm alone** — no KB, no context, no belief — and
  derives the thirteen endpoint signatures a second time, from numeric interval layouts, so
  the transcribed table and the definitions can only agree by both being right.  The second
  tests the prover over a KB, where the measures, the unit table and belief all come into
  it."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.core-context :as core-context]
            [vaelii.impl.duration :as dur]
            [vaelii.impl.interval :as iv]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.seed :as seed]
            [vaelii.impl.stp :as stp]
            [vaelii.test-util :as tu])
  (:import [vaelii.impl.stp TemporalDistanceProver]))

;; A fresh KB per test: the CoreContext grammar, MeasureContext (the measure NAUTs and the
;; unit table the magnitudes normalize through), TimeContext (temporalDistance, startOf,
;; endOf and the interval relations), and the prover registered — it is opt-in, so
;; registering it is what turns stored constraints into a closure.
(use-fixtures :each (tu/neutral-fresh
                     #(doto (tu/fresh)
                        (core-context/load-into)
                        (seed/load-context 'MeasureContext "upper")
                        (seed/load-context 'TimeContext "upper")
                        (v/add-prover (stp/stp-prover)))))

(def ^:private C 'UniverseContext)

(defn- load-time-units
  "Three units of one dimension, all converting direct to Second — the direct-to-base
  contract the normalization assumes."
  [kb]
  (v/assert kb '(dimensionOf Second Duration)   C)
  (v/assert kb '(dimensionOf Minute Duration)   C)
  (v/assert kb '(dimensionOf Hour Duration)     C)
  (v/assert kb '(conversionFactor Second Second 1)  C)
  (v/assert kb '(conversionFactor Minute Second 60) C)
  (v/assert kb '(conversionFactor Hour Second 3600) C))

(defn- bound [kb goal] (get (first (v/ask kb goal C)) '?d))

;; ---- the algorithm, without a KB ----------------------------------------

(deftest a-chain-of-gaps-composes-by-addition
  (let [net (-> {} (stp/narrow 'A 'B 10 20) (stp/narrow 'B 'C 5 5))
        pc  (stp/close net (stp/nodes net))]
    (testing "10-to-20 then exactly 5 is 15-to-25, which nobody wrote down"
      (is (= [15 25] (stp/constraint pc 'A 'C))))
    (testing "and the converse bound is the same interval reflected"
      (is (= [-25 -15] (stp/constraint pc 'C 'A))))
    (testing "a stated bound no path improves on survives unchanged"
      (is (= [10 20] (stp/constraint pc 'A 'B))))
    (testing "the diagonal is no gap at all"
      (is (= [0 0] (stp/constraint pc 'A 'A))))
    (testing "and an instant the network never mentions is unbounded against everything"
      (is (= stp/unbounded (stp/constraint pc 'A 'Z))))))

(deftest a-second-route-tightens-the-first
  ;; A to B is stated loosely and pinned exactly by the way round through C
  (let [net (-> {} (stp/narrow 'A 'B 10 20) (stp/narrow 'A 'C 5 5) (stp/narrow 'C 'B 8 8))
        pc  (stp/close net (stp/nodes net))]
    (is (= [13 13] (stp/constraint pc 'A 'B)))
    (testing "which is contained in what was stated — a closure only ever narrows"
      (let [[lo hi] (stp/constraint pc 'A 'B)]
        (is (and (>= lo 10) (<= hi 20)))))))

(deftest intersection-is-order-independent
  (is (= (-> {} (stp/narrow 'A 'B 0 10) (stp/narrow 'A 'B 5 20))
         (-> {} (stp/narrow 'A 'B 5 20) (stp/narrow 'A 'B 0 10))))
  (is (= [5 10] (get (-> {} (stp/narrow 'A 'B 0 10) (stp/narrow 'A 'B 5 20)) '[A B]))))

(deftest a-negative-cycle-is-the-contradiction
  (testing "three gaps that cannot all be closed: A to B and B to C are each 1, and A to C
            is claimed to be 1 as well"
    (let [net (-> {} (stp/narrow 'A 'B 1 1) (stp/narrow 'B 'C 1 1) (stp/narrow 'A 'C 1 1))]
      (is (= :inconsistent (stp/close net (stp/nodes net))))))
  (testing "bounds that cross are refused as written, whatever else is present"
    (is (= :inconsistent (stp/close (assoc {} '[A B] [10 5]) '#{A B})))
    (is (= '#{[A B]} (stp/unsatisfiable-pairs (assoc {} '[A B] [10 5])))))
  (testing "a non-zero gap from an instant to itself is refused the same way — no path ever
            visits the diagonal, so nothing else would report it"
    (is (= :inconsistent (stp/close (assoc {} '[A A] [5 5]) '#{A})))
    (is (= [0 0] (stp/constraint (assoc {} '[A A] [5 5]) 'A 'A))))
  (testing "and a consistent cycle is not one — the three gaps add to nothing"
    (let [net (-> {} (stp/narrow 'A 'B 1 1) (stp/narrow 'B 'C 1 1) (stp/narrow 'A 'C 2 2))]
      (is (not= :inconsistent (stp/close net (stp/nodes net)))))))

(deftest a-bound-reads-back-as-an-ordering
  (is (= #{:before} (stp/point-possibilities [1 5])))
  (is (= #{:after} (stp/point-possibilities [-5 -1])))
  (is (= #{:equal} (stp/point-possibilities [0 0])))
  (is (= #{:before :equal} (stp/point-possibilities [0 5])))
  (is (= #{:equal :after} (stp/point-possibilities [-5 0])))
  (is (= #{:before :equal :after} (stp/point-possibilities [-5 5])))
  (is (= #{:before :equal :after} (stp/point-possibilities stp/unbounded))
      "a bound is a closed interval, so at least one ordering always survives"))

;; ---- the endpoint signatures, derived from numeric layouts ---------------

(def ^:private by-endpoints
  "Each Allen base relation as the inequalities over four endpoints that define it, an
  interval being `[start end]` with `start < end`.  The independent second statement of what
  `endpoint-signature` transcribes."
  {:before        (fn [_as ae bs _be] (< ae bs))
   :meets         (fn [_as ae bs _be] (= ae bs))
   :overlaps      (fn [as ae bs be] (and (< as bs) (< bs ae) (< ae be)))
   :finished-by   (fn [as ae bs be] (and (< as bs) (= ae be)))
   :contains      (fn [as ae bs be] (and (< as bs) (> ae be)))
   :starts        (fn [as ae bs be] (and (= as bs) (< ae be)))
   :equal         (fn [as ae bs be] (and (= as bs) (= ae be)))
   :started-by    (fn [as ae bs be] (and (= as bs) (> ae be)))
   :during        (fn [as ae bs be] (and (> as bs) (< ae be)))
   :finishes      (fn [as ae bs be] (and (> as bs) (= ae be)))
   :overlapped-by (fn [as ae bs be] (and (> as bs) (< as be) (> ae be)))
   :met-by        (fn [as _ae _bs be] (= as be))
   :after         (fn [as _ae _bs be] (> as be))})

(def ^:private layouts
  "Every proper interval over the six points 0..5 — enough to realize any layout of two."
  (vec (for [s (range 6) e (range 6) :when (< s e)] [s e])))

(defn- relation-of [[as ae] [bs be]]
  (first (keep (fn [[rel pred]] (when (pred as ae bs be) rel)) by-endpoints)))

(defn- ordering [a b] (cond (< a b) :before (= a b) :equal :else :after))

(defn- signature-of [[as ae] [bs be]]
  {[:start :start] (ordering as bs) [:start :end] (ordering as be)
   [:end :start]   (ordering ae bs) [:end :end]   (ordering ae be)})

(deftest the-endpoint-signatures-match-the-relation-definitions
  ;; The guard on the bridge.  A mistyped signature is not a crash and not an empty answer —
  ;; it is a metric network quietly narrowing an interval relation to the wrong thing.
  (let [derived (reduce (fn [m [a b]]
                          (update m (relation-of a b) (fnil conj #{}) (signature-of a b)))
                        {} (for [a layouts b layouts] [a b]))]
    (testing "each relation forces exactly one set of four orderings"
      (doseq [[rel sigs] derived]
        (is (= 1 (count sigs)) (str rel " forces " (count sigs) " different signatures"))))
    (testing "and that is the one transcribed"
      (is (= iv/all-relations (set (keys derived))))
      (is (= iv/all-relations (set (keys stp/endpoint-signature))))
      (doseq [[rel sigs] derived]
        (is (= (first sigs) (stp/endpoint-signature rel)) (str rel))))
    (testing "the thirteen signatures are distinct, which is what makes reading them a
              decision rather than a filter that could pass two"
      (is (= 13 (count (set (vals stp/endpoint-signature))))))))

(deftest the-narrowing-reads-a-relation-off-the-gaps
  (testing "A lasts 2, B lasts 3, and B starts 1 after A ends — that is before, and only"
    (let [net (-> {} (stp/narrow 'As 'Ae 2 2) (stp/narrow 'Bs 'Be 3 3)
                  (stp/narrow 'Ae 'Bs 1 1))
          pc  (stp/close net (stp/nodes net))]
      (is (= #{:before} (stp/relations-from-endpoints pc '[As Ae] '[Bs Be])))
      (is (= #{:after} (stp/relations-from-endpoints pc '[Bs Be] '[As Ae])))))
  (testing "B starting somewhere between 1 and 5 after A starts leaves three relations,
            because where A's end falls against B's start is exactly what is open"
    (let [net (-> {} (stp/narrow 'As 'Ae 2 2) (stp/narrow 'Bs 'Be 3 3)
                  (stp/narrow 'As 'Bs 1 5))
          pc  (stp/close net (stp/nodes net))]
      (is (= #{:before :meets :overlaps} (stp/relations-from-endpoints pc '[As Ae] '[Bs Be])))))
  (testing "a network saying nothing narrows nothing"
    (is (= iv/all-relations (stp/relations-from-endpoints {} '[As Ae] '[Bs Be])))))

(deftest the-overlap-window-is-the-later-start-to-the-earlier-end
  (testing "A runs 0 to 10, B runs 4 to 20 — six shared"
    (let [net (-> {} (stp/narrow 'As 'Ae 10 10) (stp/narrow 'As 'Bs 4 4)
                  (stp/narrow 'Bs 'Be 16 16))
          pc  (stp/close net (stp/nodes net))]
      (is (= [6 6] (stp/overlap-bounds-from-endpoints pc '[As Ae] '[Bs Be])))
      (is (= [6 6] (stp/overlap-bounds-from-endpoints pc '[Bs Be] '[As Ae]))
          "the overlap is symmetric")))
  (testing "intervals apart share nothing, and the clamp is what says so"
    (let [net (-> {} (stp/narrow 'As 'Ae 2 2) (stp/narrow 'Bs 'Be 3 3)
                  (stp/narrow 'Ae 'Bs 1 1))
          pc  (stp/close net (stp/nodes net))]
      (is (= [0 0] (stp/overlap-bounds-from-endpoints pc '[As Ae] '[Bs Be])))))
  (testing "a network that pins nothing bounds nothing"
    (let [[lo hi] (stp/overlap-bounds-from-endpoints {} '[As Ae] '[Bs Be])]
      (is (= 0 lo))
      (is (not (Double/isFinite (double hi)))))))

;; ---- the prover over a KB ------------------------------------------------

(tu/deftest-kb a-derived-gap-is-bound-in-the-base-unit
  (load-time-units kb)
  (tu/with-terms [P Q R]
    (v/assert kb (list 'temporalDistance P Q '(QuantityFn 30 Minute)) C)
    (v/assert kb (list 'temporalDistance Q R '(QuantityFn 1 Hour)) C)
    (testing "half an hour then an hour is 5400 seconds, though nobody said so"
      (is (= '(QuantityFn 5400 Second) (bound kb (list 'temporalDistance P R '?d)))))
    (testing "the units compose through the table, so a mixture is no obstacle"
      (is (v/ask? kb (list 'temporalDistance P R '(QuantityFn 1.5 Hour)) C))
      (is (v/ask? kb (list 'temporalDistance P R '(QuantityFn 90 Minute)) C)))
    (testing "and the gap read backwards is the same one negated"
      (is (= '(QuantityFn -5400 Second) (bound kb (list 'temporalDistance R P '?d)))))
    (testing "an instant against itself is no gap at all"
      (is (= '(QuantityFn 0 Second) (bound kb (list 'temporalDistance P P '?d)))))))

(tu/deftest-kb a-bounded-constraint-stays-bounded
  (load-time-units kb)
  (tu/with-terms [P Q R]
    (v/assert kb (list 'temporalDistance P Q '(QuantityIntervalFn 10 20 Minute)) C)
    (v/assert kb (list 'temporalDistance Q R '(QuantityFn 5 Minute)) C)
    (testing "the bounds add separately, and the render reports what is not known"
      (is (= '(QuantityIntervalFn 900 1500 Second)
             (bound kb (list 'temporalDistance P R '?d)))))
    (testing "so no point measure is claimed"
      (is (not (v/ask? kb (list 'temporalDistance P R '(QuantityFn 900 Second)) C)))
      (is (not (v/ask? kb (list 'temporalDistance P R '(QuantityFn 1500 Second)) C))))))

(tu/deftest-kb the-derived-bound-is-the-tightest-one-entailed
  (load-time-units kb)
  (tu/with-terms [P Q R]
    ;; P to Q is stated loosely and pinned exactly by the way round through R
    (v/assert kb (list 'temporalDistance P Q '(QuantityIntervalFn 10 20 Minute)) C)
    (v/assert kb (list 'temporalDistance P R '(QuantityFn 5 Minute)) C)
    (v/assert kb (list 'temporalDistance R Q '(QuantityFn 8 Minute)) C)
    (testing "the two routes intersect to the exact figure"
      (is (= '(QuantityFn 780 Second) (bound kb (list 'temporalDistance P Q '?d)))))
    (testing "and it is contained in the bound that was stated, which therefore still checks
              — a stated bound is a weaker claim, so the derived one entails it"
      (is (v/ask? kb (list 'temporalDistance P Q '(QuantityIntervalFn 10 20 Minute)) C))
      (is (v/ask? kb (list 'temporalDistance P Q '(QuantityIntervalFn 0 60 Minute)) C)))
    (testing "while anything tighter than the derived bound is not entailed"
      (is (not (v/ask? kb (list 'temporalDistance P Q '(QuantityIntervalFn 14 20 Minute)) C)))
      (is (not (v/ask? kb (list 'temporalDistance P Q '(QuantityFn 700 Second)) C))))))

(tu/deftest-kb a-gap-nothing-reaches-has-no-measure
  (load-time-units kb)
  (tu/with-terms [P Q R S]
    (v/assert kb (list 'temporalDistance P Q '(QuantityFn 5 Minute)) C)
    (testing "R sits in no constraint, so its gap to P is unbounded — a real answer, but
              not one any measure can be written for"
      (is (empty? (v/ask kb (list 'temporalDistance P R '?d) C)))
      (is (= [[(quote Duration) (quote Second)] ##-Inf ##Inf] (stp/separation kb C 'P R))))
    (testing "and a half-bounded gap is the same: knowledge, but not a measure"
      (v/assert kb (list 'temporalDistance R S '(QuantityIntervalFn 5 5 Minute)) C)
      (is (empty? (v/ask kb (list 'temporalDistance P S '?d) C))))))

(tu/deftest-kb an-inconsistent-network-answers-nothing-and-is-reported
  (load-time-units kb)
  (v/clear-violations! kb)
  (tu/with-terms [P Q R]
    ;; P to Q is an hour and Q to R is an hour, so P to R cannot also be an hour
    (v/assert kb (list 'temporalDistance P Q '(QuantityFn 1 Hour)) C)
    (v/assert kb (list 'temporalDistance Q R '(QuantityFn 1 Hour)) C)
    (v/assert kb (list 'temporalDistance P R '(QuantityFn 1 Hour)) C)
    (testing "no assignment of times satisfies all three, and the closure proves it"
      (is (stp/inconsistent? kb C))
      (is (nil? (stp/separation kb C P R))))
    (testing "and an unsatisfiable theory is not mined for a number — not even for the pair
              that was stated outright"
      (is (empty? (v/ask kb (list 'temporalDistance P Q '?d) C)))
      (is (not (v/ask? kb (list 'temporalDistance P Q '(QuantityFn 1 Hour)) C))))
    (testing "the clash is a property of the set, so it is reported rather than thrown"
      (let [entry (first (filter #(= :metric-temporal-inconsistency (:violation %))
                                 (v/violations kb)))]
        (is (some? entry))
        (is (= C (:context entry)))
        (is (= '#{P Q R} (set (map #(get {P 'P, Q 'Q, R 'R} %) (:nodes (:detail entry))))))
        (is (seq (:cycle (:detail entry))) "and it names the instants on the cycle")))
    (testing "retracting one of the three gives the others their answers back"
      (v/retract! kb (v/handle-of kb (list 'temporalDistance P R '(QuantityFn 1 Hour)) C))
      (is (not (stp/inconsistent? kb C)))
      (is (= '(QuantityFn 7200 Second) (bound kb (list 'temporalDistance P R '?d)))))))

(tu/deftest-kb constraints-of-two-dimensions-are-refused-rather-than-mixed
  (load-time-units kb)
  (v/assert kb '(dimensionOf Metre Length) C)
  (tu/with-terms [P Q R]
    (v/assert kb (list 'temporalDistance P Q '(QuantityFn 5 Minute)) C)
    (v/assert kb (list 'temporalDistance Q R '(QuantityFn 5 Metre)) C)
    (testing "minutes and metres do not add up, so the network is not built at all"
      (is (nil? (stp/problem kb C)))
      (is (empty? (v/ask kb (list 'temporalDistance P R '?d) C)))
      (is (empty? (v/ask kb (list 'temporalDistance P Q '?d) C))))))

(tu/deftest-kb a-refusal-that-silences-the-whole-layer-is-reported
  (load-time-units kb)
  (v/assert kb '(dimensionOf Metre Length) C)
  (v/clear-violations! kb)
  (tu/with-terms [P Q R]
    (v/assert kb (list 'temporalDistance P Q '(QuantityFn 5 Minute)) C)
    (v/assert kb (list 'temporalDistance Q R '(QuantityFn 5 Metre)) C)
    (testing "one mis-spelt unit takes every metric goal in the context with it, the gap
              stated outright included — so the refusal is content the engine dropped and
              goes where the engine says what it dropped"
      (is (empty? (v/ask kb (list 'temporalDistance P Q '?d) C)))
      (let [entry (first (filter #(= :metric-temporal-mixed-dimensions (:violation %))
                                 (v/violations kb)))]
        (is (some? entry))
        (is (= C (:context entry)))
        (is (= '[Duration Length] (:dimensions (:detail entry))))
        (is (= '[Metre Second] (:units (:detail entry)))
            "and names the base units the two dimensions would have been summed in")))
    (testing "a query loop says it once, not once per goal"
      (v/ask kb (list 'temporalDistance P R '?d) C)
      (v/ask kb (list 'temporalDistance Q R '?d) C)
      (is (= 1 (count (filter #(= :metric-temporal-mixed-dimensions (:violation %))
                              (v/violations kb))))))))

(tu/deftest-kb the-constraints-are-read-under-belief-and-visibility
  (load-time-units kb)
  (tu/with-terms [P Q R InnerContext]
    (v/assert kb (list 'genlContext InnerContext C) C)
    (v/assert kb (list 'temporalDistance P Q '(QuantityFn 1 Hour)) C)
    (v/assert kb (list 'temporalDistance Q R '(QuantityFn 1 Hour)) InnerContext)
    (testing "the inner context sees both, so it composes the chain"
      (is (= '(QuantityFn 7200 Second)
             (get (first (v/ask kb (list 'temporalDistance P R '?d) InnerContext)) '?d))))
    (testing "the outer sees only its own, so it composes nothing"
      (is (empty? (v/ask kb (list 'temporalDistance P R '?d) C))))
    (testing "retracting a link breaks the chain — the network is read, not cached"
      (v/retract! kb (v/handle-of kb (list 'temporalDistance Q R '(QuantityFn 1 Hour))
                                  InnerContext))
      (is (empty? (v/ask kb (list 'temporalDistance P R '?d) InnerContext))))))

;; ---- one gap, written two ways -------------------------------------------
;; A magnitude reaches the network multiplied by a stored conversion factor, so two
;; spellings of one figure arrive a last bit apart.  Every comparison the metric layer
;; makes is therefore read to `provers/*quantity-tolerance*` — the epsilon the measure
;; comparisons and the duration arithmetic are held to — and each stated magnitude is
;; snapped to that grid on the way in, exactly as a stored `length` is.  What that buys is
;; below; the guard that it did not buy it by tolerating everything is beneath them.

(tu/deftest-kb the-same-gap-written-in-two-units-is-one-constraint
  (load-time-units kb)
  (v/clear-violations! kb)
  (tu/with-terms [P Q]
    (v/assert kb (list 'temporalDistance P Q '(QuantityFn 66 Minute)) C)
    (v/assert kb (list 'temporalDistance P Q '(QuantityFn 1.1 Hour)) C)
    (testing "the KB's own measure comparison calls the two the same quantity"
      (is (v/ask? kb '(sameQuantity (QuantityFn 66 Minute) (QuantityFn 1.1 Hour)) C)))
    (testing "so the metric layer must too: 1.1 hours normalizes to 3960.0000000000005
              seconds and 66 minutes to 3960, and intersected exactly the two would cross —
              one true thing said twice, read as a gap at once too long and too short"
      (is (not (stp/inconsistent? kb C)))
      (is (= '(QuantityFn 3960 Second) (bound kb (list 'temporalDistance P Q '?d)))))
    (testing "and nothing is filed against a KB that stated no contradiction"
      (is (empty? (v/violations kb))))))

(tu/deftest-kb a-cycle-a-conversion-opens-is-not-a-contradiction
  (load-time-units kb)
  (v/clear-violations! kb)
  (tu/with-terms [P Q R]
    ;; three facts, no pair stated twice, and they agree: 66 minutes then one more is 67
    (v/assert kb (list 'temporalDistance P Q '(QuantityFn 1.1 Hour)) C)
    (v/assert kb (list 'temporalDistance Q R '(QuantityFn 1 Minute)) C)
    (v/assert kb (list 'temporalDistance P R '(QuantityFn 67 Minute)) C)
    (testing "the cycle closes at −5e-13, which is the conversion and not the knowledge"
      (is (not (stp/inconsistent? kb C)))
      (is (= '(QuantityFn 4020 Second) (bound kb (list 'temporalDistance P R '?d))))
      (is (empty? (v/violations kb))))))

(tu/deftest-kb noise-a-chain-accumulates-does-not-close-a-cycle
  (load-time-units kb)
  (v/clear-violations! kb)
  (let [ts (mapv (fn [_] (tu/tmp-ind "T")) (range 11))]
    (doseq [i (range 10)]
      (v/assert kb (list 'temporalDistance (ts i) (ts (inc i)) '(QuantityFn 0.1 Second)) C))
    (v/assert kb (list 'temporalDistance (ts 0) (ts 10) '(QuantityFn 1 Second)) C)
    (testing "each hop is snapped on the way in and each is exact, but ten tenths of a
              second sum to 0.9999999999999999 — against the stated second that is a cycle
              of −1.1e-16, which no snapping at the boundary could have caught"
      (is (not (stp/inconsistent? kb C))))
    (testing "and the crossed sliver the closure leaves still renders as the figure"
      (is (= '(QuantityFn 1 Second)
             (bound kb (list 'temporalDistance (ts 0) (ts 10) '?d)))))))

(tu/deftest-kb a-disagreement-wider-than-the-epsilon-is-still-a-contradiction
  (load-time-units kb)
  (v/clear-violations! kb)
  (tu/with-terms [P Q]
    (v/assert kb (list 'temporalDistance P Q '(QuantityFn 3960 Second)) C)
    (v/assert kb (list 'temporalDistance P Q '(QuantityFn 3960.000001 Second)) C)
    (testing "a microsecond is a thousand epsilons, so these are two claims and not two
              spellings — the band is what a conversion can lose, not a licence"
      (is (stp/inconsistent? kb C))
      (is (seq (filter #(= :metric-temporal-inconsistency (:violation %))
                       (v/violations kb)))))))

(tu/deftest-kb the-metric-layer-and-the-duration-arithmetic-read-one-pair-of-facts-alike
  (v/add-prover kb (dur/duration-prover))
  (load-time-units kb)
  (tu/with-terms [A P Q]
    (v/assert kb (list 'length A '(QuantityFn 66 Minute)) C)
    (v/assert kb (list 'length A '(QuantityFn 1.1 Hour)) C)
    (v/assert kb (list 'temporalDistance P Q '(QuantityFn 66 Minute)) C)
    (v/assert kb (list 'temporalDistance P Q '(QuantityFn 1.1 Hour)) C)
    (testing "one interval's length written twice, and one gap written twice, in the same
              two units — a separation and a duration are written the same way, so the two
              subsystems have to read the pair the same way"
      (is (= '(QuantityFn 3960 Second)
             (get (first (v/ask kb (list 'totalDuration (list 'list A) '?d) C)) '?d)))
      (is (= '(QuantityFn 3960 Second) (bound kb (list 'temporalDistance P Q '?d)))))))

;; ---- who is told the network cannot be satisfied --------------------------
;; The closure is memoized on the network *value* and so is shared — two contexts seeing
;; the same constraints, or two KBs holding them, close it once between them.  A ledger
;; entry is a claim about a KB and a context, so it cannot ride on that pass.

(tu/deftest-kb every-context-that-cannot-satisfy-the-constraints-is-told-so
  (load-time-units kb)
  (v/clear-violations! kb)
  (tu/with-terms [P Q R InnerContext]
    (v/assert kb (list 'genlContext InnerContext C) C)
    (v/assert kb (list 'temporalDistance P Q '(QuantityFn 1 Hour)) C)
    (v/assert kb (list 'temporalDistance Q R '(QuantityFn 1 Hour)) C)
    (v/assert kb (list 'temporalDistance P R '(QuantityFn 1 Hour)) C)
    (testing "the inner context sees exactly the outer's constraints and nothing else, so
              the two reach one network and close it once between them"
      (is (stp/inconsistent? kb InnerContext))
      (is (stp/inconsistent? kb C)))
    (let [es (filter #(= :metric-temporal-inconsistency (:violation %)) (v/violations kb))]
      (testing "and each is named — what a reader needs is where its own query stopped
                being answered, not which context happened to ask first"
        (is (= #{InnerContext C} (set (map :context es)))))
      (testing "once each, since a query loop over one belief state reports once"
        (is (= 2 (count es)))))))

(tu/deftest-kb a-second-kb-holding-the-same-constraints-is-told-so-too
  (load-time-units kb)
  (v/clear-violations! kb)
  (tu/with-terms [P Q R]
    (let [facts [(list 'temporalDistance P Q '(QuantityFn 1 Hour))
                 (list 'temporalDistance Q R '(QuantityFn 1 Hour))
                 (list 'temporalDistance P R '(QuantityFn 1 Hour))]
          other (doto (tu/isolated-fresh)
                  (core-context/load-into)
                  (seed/load-context 'MeasureContext "upper")
                  (seed/load-context 'TimeContext "upper")
                  (v/add-prover (stp/stp-prover)))]
      (try
        (load-time-units other)
        (doseq [s facts] (v/assert kb s C) (v/assert other s C))
        (testing "the two KBs reach the very same network, so whichever asks first runs the
                  closure and the other reads its answer"
          (is (stp/inconsistent? kb C))
          (is (stp/inconsistent? other C)))
        (testing "both are told: a KB answering nothing with an empty ledger has no way to
                  learn that another KB's pass is the reason"
          (is (= 1 (count (filter #(= :metric-temporal-inconsistency (:violation %))
                                  (v/violations kb)))))
          (is (= 1 (count (filter #(= :metric-temporal-inconsistency (:violation %))
                                  (v/violations other))))))
        (finally (tu/clear-kb! other))))))

;; ---- the bridge to the interval algebra ----------------------------------

(defn- bridge-interval
  "Give interval `i` the two bounding instants `s` and `e`."
  [kb i s e]
  (v/assert kb (list 'startOf i s) C)
  (v/assert kb (list 'endOf i e) C))

(tu/deftest-kb the-metric-network-narrows-the-allen-possibilities
  (load-time-units kb)
  (tu/with-terms [A B As Ae Bs Be]
    (bridge-interval kb A As Ae)
    (bridge-interval kb B Bs Be)
    (v/assert kb (list 'temporalDistance As Ae '(QuantityFn 2 Hour)) C)
    (v/assert kb (list 'temporalDistance Bs Be '(QuantityFn 3 Hour)) C)
    (v/assert kb (list 'temporalDistance Ae Bs '(QuantityFn 1 Hour)) C)
    (testing "B begins an hour after A ends, so A is before B and can be nothing else"
      (let [narrowed (stp/allen-narrowing kb C)]
        (is (= #{:before} (get narrowed [A B])))
        (is (= #{:after} (get narrowed [B A])) "and the pair reads the same backwards")))
    (testing "the narrowing is a value to intersect, not a mutation — no interval fact has
              appeared and the stored network is untouched"
      (is (empty? (v/sentexes-matching kb (list 'before A B) C)))
      (is (= iv/all-relations (iv/possible-allen-relations kb C A B))))))

(tu/deftest-kb a-loose-metric-network-narrows-without-pinning
  (load-time-units kb)
  (tu/with-terms [A B As Ae Bs Be]
    (bridge-interval kb A As Ae)
    (bridge-interval kb B Bs Be)
    (v/assert kb (list 'temporalDistance As Ae '(QuantityFn 2 Hour)) C)
    (v/assert kb (list 'temporalDistance Bs Be '(QuantityFn 3 Hour)) C)
    (v/assert kb (list 'temporalDistance As Bs '(QuantityIntervalFn 1 5 Hour)) C)
    (testing "B starts somewhere between one and five hours after A does, which leaves open
              exactly where A's end falls against B's start"
      (is (= #{:before :meets :overlaps} (get (stp/allen-narrowing kb C) [A B]))))))

(tu/deftest-kb the-bridge-needs-both-endpoints-and-a-satisfiable-network
  (load-time-units kb)
  (tu/with-terms [A B As Ae Bs]
    (testing "with no metric constraints there is nothing to read"
      (is (nil? (stp/allen-narrowing kb C))))
    (bridge-interval kb A As Ae)
    (v/assert kb (list 'startOf B Bs) C)                  ; no endOf
    (v/assert kb (list 'temporalDistance As Ae '(QuantityFn 2 Hour)) C)
    (testing "an interval missing one of its bounding instants is not read"
      (is (nil? (get (stp/endpoints-of kb B C) 0)))
      (is (nil? (stp/allen-narrowing kb C))))
    (testing "and neither is an interval whose start is stated of two different instants"
      (tu/with-terms [Bs2]
        (v/assert kb (list 'startOf B Bs2) C)
        (is (nil? (stp/endpoints-of kb B C)))))))

;; ---- registration --------------------------------------------------------

(tu/deftest-kb the-prover-ships-opt-in
  (is (not-any? #(instance? TemporalDistanceProver %) provers/default-provers)
      "nothing metric is in the default registry, so a KB pays for the closure only once
       it asks for it"))

(tu/deftest-kb without-the-prover-the-constraints-are-inert
  (load-time-units kb)
  (tu/with-terms [P Q R]
    (v/assert kb (list 'temporalDistance P Q '(QuantityFn 1 Hour)) C)
    (v/assert kb (list 'temporalDistance Q R '(QuantityFn 1 Hour)) C)
    (testing "a stated constraint is retrievable as an ordinary fact"
      (is (seq (provers/solve-goal-with kb provers/default-provers
                                        (list 'temporalDistance P Q '?d) C))))
    (testing "but nothing in the default registry composes two of them"
      (is (empty? (provers/solve-goal-with kb provers/default-provers
                                           (list 'temporalDistance P R '?d) C))))
    (testing "the registered prover on the very same facts does"
      (is (= '(QuantityFn 7200 Second) (bound kb (list 'temporalDistance P R '?d)))))))

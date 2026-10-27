;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.cardinality-solve-test
  "`asp/atMost` / `asp/atLeast`, their weighted `…Sum` forms and the soft twins, which
  `solve-context` grounds to one solver cardinality entry per group (docs/solving.md,
  \"`atMost` / `atLeast`\").  The
  solving tests are guarded on `asp?`; the wrapper, record and refusal tests run without a
  backend."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.walk :as walk]
            [vaelii.core :as v]
            [vaelii.impl.asp.solver :as solver]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.rules :as rules]
            [vaelii.test-util :as tu]))

(def ^:private asp? (solver/available?))

(defn- sentex-of [kb h] (p/get-sentex (:records kb) h))

;; ---- 1. the surface normalizes to a constraint rule carrying the bound ----

(deftest a-cardinality-rule-is-a-marked-constraint-rule
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [build]
      (let [most  (v/assert kb (list 'asp/atMost 2 '?c (list build '?c 'transport)) 'CxUniverse)
            least (v/assert kb (list 'asp/atLeast 1 '?c (list build '?c 'transport)) 'CxUniverse)
            soft  (v/assert kb (list 'asp/softAtMost 2 '?c (list build '?c 'transport)) 'CxUniverse)]
        (testing "it stores as a constraint rule — hard by default, soft for the soft twin"
          (is (= :hard (rules/constraint-of (sentex-of kb most))))
          (is (= :hard (rules/constraint-of (sentex-of kb least))))
          (is (= :soft (rules/constraint-of (sentex-of kb soft)))))
        (testing "cardinality-of reads the operator and the bound back off the marker"
          (is (= {:op :at-most :k 2 :counted (:counted (rules/cardinality-of (sentex-of kb most)))}
                 (rules/cardinality-of (sentex-of kb most))))
          (is (= :at-most (:op (rules/cardinality-of (sentex-of kb most)))))
          (is (= 2 (:k (rules/cardinality-of (sentex-of kb most)))))
          (is (= :at-least (:op (rules/cardinality-of (sentex-of kb least)))))
          (is (= 1 (:k (rules/cardinality-of (sentex-of kb least))))))
        (testing "k and op are part of identity: atMost 2, atMost 3, atLeast 1 are distinct"
          (let [three (v/assert kb (list 'asp/atMost 3 '?c (list build '?c 'transport)) 'CxUniverse)]
            (is (not= most three))
            (is (not= most least))
            (is (not= most soft))))
        (testing "a cardinality rule chains for nobody, like any constraint rule"
          (is (not (rules/forward-sentex? (sentex-of kb most))))
          (is (not (rules/backward-sentex? (sentex-of kb most)))))
        (testing "re-asserting the same bound is idempotent"
          (is (= most (v/assert kb (list 'asp/atMost 2 '?c (list build '?c 'transport)) 'CxUniverse))))))))

(deftest a-malformed-cardinality-bound-is-refused
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [build]
      (testing "the count must be a non-negative integer"
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/assert kb (list 'asp/atMost '?n '?c (list build '?c 'transport)) 'CxUniverse)))
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/assert kb (list 'asp/atMost -1 '?c (list build '?c 'transport)) 'CxUniverse))))
      (testing "the counted slot must be a variable"
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/assert kb (list 'asp/atMost 2 'Ada (list build 'Ada 'transport)) 'CxUniverse))))
      (testing "the counted variable must appear in the pattern"
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/assert kb (list 'asp/atMost 2 '?x (list build '?c 'transport)) 'CxUniverse)))))))

(deftest the-authored-surface-survives-a-round-trip
  ;; The rule stores as `(set/hardConstraint (implies …))`, but `rewrap-sentex` restores the
  ;; authored `asp/atMost` form for export/display rather than leaking the internal one.
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [build]
      (let [h  (v/assert kb (list 'asp/atMost 2 '?c (list build '?c 'transport)) 'CxUniverse)
            sx (sentex-of kb h)
            surface (rules/rewrap-sentex (v/sentence-of sx) sx)]
        (is (= 'asp/atMost (first surface)) "the surface wrapper comes back, not set/hardConstraint")
        (is (= 2 (second surface)) "and the bound")
        (let [soft (v/assert kb (list 'asp/softAtMost 2 '?c (list build '?c 'transport)) 'CxUniverse)
              ssx  (sentex-of kb soft)]
          (is (= 'asp/softAtMost
                 (first (rules/rewrap-sentex (v/sentence-of ssx) ssx)))))))))

;; ---- 2. end to end: the bound prunes the models --------------------------

(defn- install-build!
  "A build allocation over `cities`: each city builds transport or army (a choice),
  exactly one (`functional` + a hard at-least-one), and army costs 1 so the solver
  prefers transport up to whatever cap is asserted."
  [kb ctx build cities]
  (doseq [v '[transport army]]
    (v/assert kb (list 'set/assumptionRule (list 'implies (list 'cand '?c) (list build '?c v)))
              ctx))
  (v/assert kb (list 'functional build) ctx {:strength :monotonic})
  (v/assert kb (list 'set/hardConstraint
                     (list 'implies (list 'and (list 'not (list build '?c 'transport))
                                          (list 'not (list build '?c 'army)))
                           (list 'nobuild '?c)))
            ctx {:strength :monotonic})
  (v/assert kb (list 'set/softConstraint (list 'implies (list build '?c 'army) (list 'wasted '?c)))
            ctx {:strength :monotonic})
  (doseq [c cities] (v/assert kb (list 'cand c) ctx {:strength :monotonic})))

(defn- builds-of [labeling build kind]
  (for [s (:true labeling) :when (and (= build (first s)) (= kind (nth s 2)))] (nth s 1)))

(deftest at-most-caps-the-transports
  ;; Five cities, at most two transports.  The soft army cost drives every uncapped city
  ;; to army, so the optimum fills the cap: exactly two transports, three armies, and
  ;; every city builds exactly one.
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [build]
        (install-build! kb 'CxCap build '[C1 C2 C3 C4 C5])
        (v/assert kb (list 'asp/atMost 2 '?c (list build '?c 'transport)) 'CxCap {:strength :monotonic})
        (let [r        (v/assert kb (list 'do/label 'CxCap 'CxCapPlan :one) 'CxCap)
              labeling (first (:labelings r))
              trans    (set (builds-of labeling build 'transport))
              army     (set (builds-of labeling build 'army))]
          (testing "the cap binds: exactly two transports"
            (is (= 2 (count trans))))
          (testing "every city builds exactly one thing"
            (is (= 5 (+ (count trans) (count army))))
            (is (empty? (clojure.set/intersection trans army))))
          (testing "base belief is untouched"
            (is (zero? (count (v/contradictions kb))))))))))

(deftest cardinality-grounds-where-subset-nogoods-cannot
  ;; thirty cities, a hard at-most-10 and at-least-10: a hand-written at-most alone is
  ;; `C(30, 11)` ≈ 54M subset nogoods, and each bound here is one weight-body constraint
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [build]
        ;; a soft-free program, so `:sat` has nothing to optimize
        (doseq [v '[transport army]]
          (v/assert kb (list 'set/assumptionRule (list 'implies (list 'cand '?c) (list build '?c v)))
                    'CxBig))
        (v/assert kb (list 'functional build) 'CxBig {:strength :monotonic})
        (v/assert kb (list 'set/hardConstraint
                           (list 'implies (list 'and (list 'not (list build '?c 'transport))
                                                (list 'not (list build '?c 'army)))
                                 (list 'nobuild '?c)))
                  'CxBig {:strength :monotonic})
        (doseq [c (mapv #(symbol (str "B" %)) (range 30))]
          (v/assert kb (list 'cand c) 'CxBig {:strength :monotonic}))
        (v/assert kb (list 'asp/atMost 10 '?c (list build '?c 'transport)) 'CxBig {:strength :monotonic})
        (v/assert kb (list 'asp/atLeast 10 '?c (list build '?c 'transport)) 'CxBig {:strength :monotonic})
        (let [r        (v/assert kb (list 'do/label 'CxBig 'CxBigPlan :sat) 'CxBig)
              labeling (first (:labelings r))]
          (is (= 10 (count (builds-of labeling build 'transport)))
              "both bounds bind: exactly ten transports")
          (is (= 30 (+ (count (builds-of labeling build 'transport))
                       (count (builds-of labeling build 'army))))
              "and every city still builds exactly one"))))))

(deftest at-least-forces-a-minimum
  ;; Deploying costs 1, so the solver would deploy nobody — but at-least-two forces two.
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [deploy]
        (v/assert kb (list 'set/assumptionRule (list 'implies (list 'unit '?u) (list deploy '?u)))
                  'CxAtl)
        (v/assert kb (list 'set/softConstraint (list 'implies (list deploy '?u) (list 'costd '?u)))
                  'CxAtl {:strength :monotonic})
        (v/assert kb (list 'asp/atLeast 2 '?u (list deploy '?u)) 'CxAtl {:strength :monotonic})
        (doseq [u '[U1 U2 U3 U4]] (v/assert kb (list 'unit u) 'CxAtl {:strength :monotonic}))
        (let [r        (v/assert kb (list 'do/label 'CxAtl 'CxAtlPlan :one) 'CxAtl)
              labeling (first (:labelings r))
              deployed (for [s (:true labeling) :when (= deploy (first s))] (nth s 1))]
          (is (= 2 (count deployed)) "the floor binds: exactly two deploy despite the cost"))))))

(deftest at-most-groups-by-the-uncounted-variable
  ;; Ferry: each transport gathers at most one army — a bound PER transport, grouped by
  ;; `?t`.  Three armies, two transports, cap one each: two get ferried, one does not, and
  ;; no transport holds two.
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [ferry]
        (doseq [a '[A1 A2 A3], t '[T1 T2]]
          (v/assert kb (list 'ferryCand a t) 'CxFer {:strength :monotonic}))
        (v/assert kb (list 'set/assumptionRule (list 'implies (list 'ferryCand '?a '?t) (list ferry '?a '?t)))
                  'CxFer)
        (v/assert kb (list 'functional ferry) 'CxFer {:strength :monotonic})   ; each army ≤1 transport
        ;; each transport gathers ≤1 army — the grouped bound
        (v/assert kb (list 'asp/atMost 1 '?a (list ferry '?a '?t)) 'CxFer {:strength :monotonic})
        ;; an unferried army costs, so the solver fills the two slots
        (v/assert kb (list 'set/softConstraint
                           (list 'implies (list 'and (list 'not (list ferry '?a 'T1))
                                                (list 'not (list ferry '?a 'T2)))
                                 (list 'unferried '?a)))
                  'CxFer {:strength :monotonic})
        (let [r        (v/assert kb (list 'do/label 'CxFer 'CxFerPlan :one) 'CxFer)
              labeling (first (:labelings r))
              ferried  (for [s (:true labeling) :when (= ferry (first s))] [(nth s 1) (nth s 2)])
              per-t    (frequencies (map second ferried))]
          (testing "two of the three armies are ferried"
            (is (= 2 (count ferried))))
          (testing "and no transport gathers more than one — the per-group cap"
            (is (every? #(<= % 1) (vals per-t)))))))))

;; ---- 3. check predicts a malformed bound without throwing -----------------

(deftest check-reports-a-malformed-cardinality-rather-than-throwing
  ;; `check` returns the problem `assert` throws, so a batch caller flags one line
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [build]
      (doseq [bad [(list 'asp/atMost -1 '?c (list build '?c 'transport))
                   (list 'asp/atMost '?n '?c (list build '?c 'transport))
                   (list 'asp/atMost 2 'Ada (list build 'Ada 'transport))
                   (list 'asp/atMost 2 '?x (list build '?c 'transport))]]
        (let [problems (v/check kb bad 'CxUniverse)]
          (is (seq problems) (str "check returns a problem for " (pr-str bad)))
          (is (= :not-well-formed (:type (first problems)))
              (str "and it is the :not-well-formed refusal for " (pr-str bad))))))))

;; ---- 4. the soft twins are tradeable, not forced --------------------------

(deftest soft-atmost-is-tradeable-hard-atmost-is-not
  ;; The soft twin emits a minimized violation atom (`aspif/weight-rule` + `minimize`),
  ;; not an integrity constraint — so the bound is TRADED when compliance costs more,
  ;; where the hard bound forces it.  Four cities, cap one transport; army costs 1 each
  ;; (soft), so the hard cap yields one transport plus three armies (cost 3), while
  ;; breaching the soft cap is one violation (cost 1) < three armies — so the soft cap
  ;; builds all four transports.
  (when asp?
    (letfn [(transports-under [cap-wrapper]
              (tu/with-cleared-kb [kb tu/fresh]
                (tu/with-terms [build]
                  (install-build! kb 'CxSoft build '[C1 C2 C3 C4])
                  (v/assert kb (list cap-wrapper 1 '?c (list build '?c 'transport)) 'CxSoft {:strength :monotonic})
                  (let [r   (v/assert kb (list 'do/label 'CxSoft 'CxSoftPlan :one) 'CxSoft)
                        lab (first (:labelings r))]
                    (count (builds-of lab build 'transport))))))]
      (testing "a hard atMost forces the cap: exactly one transport"
        (is (= 1 (transports-under 'asp/atMost))))
      (testing "a soft atMost is one tradeable violation, breached when compliance costs more"
        (is (= 4 (transports-under 'asp/softAtMost)))))))

(deftest soft-atleast-is-tradeable
  ;; The soft at-least twin emits the same minimized violation over the default-negated
  ;; members.  Four units, deploying costs 1 (soft): the hard floor of two forces two
  ;; deploys (cost 2), while breaching the soft floor is one violation (cost 1) < two
  ;; deploys — so the soft floor deploys nobody.
  (when asp?
    (letfn [(deployed-under [floor-wrapper]
              (tu/with-cleared-kb [kb tu/fresh]
                (tu/with-terms [deploy]
                  (v/assert kb (list 'set/assumptionRule (list 'implies (list 'unit '?u) (list deploy '?u)))
                            'CxSAtl)
                  (v/assert kb (list 'set/softConstraint (list 'implies (list deploy '?u) (list 'costd '?u)))
                            'CxSAtl {:strength :monotonic})
                  (v/assert kb (list floor-wrapper 2 '?u (list deploy '?u)) 'CxSAtl {:strength :monotonic})
                  (doseq [u '[U1 U2 U3 U4]] (v/assert kb (list 'unit u) 'CxSAtl {:strength :monotonic}))
                  (let [r   (v/assert kb (list 'do/label 'CxSAtl 'CxSAtlPlan :one) 'CxSAtl)
                        lab (first (:labelings r))]
                    (count (for [s (:true lab) :when (= deploy (first s))] s))))))]
      (testing "a hard atLeast forces the floor: exactly two deploy"
        (is (= 2 (deployed-under 'asp/atLeast))))
      (testing "a soft atLeast is one tradeable violation, breached when the floor costs more"
        (is (= 0 (deployed-under 'asp/softAtLeast)))))))

;; ---- 5. a global at-least over an empty choice is infeasible, not dropped --

(deftest a-global-atleast-over-an-empty-choice-is-infeasible
  ;; a second, satisfiable choice keeps the program non-empty, so the zero labelings
  ;; come from the floor
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [deploy]
        (v/assert kb '(set/assumptionRule (implies (thing ?x) (other ?x))) 'CxEmp)
        (v/assert kb '(thing W) 'CxEmp {:strength :monotonic})
        (v/assert kb (list 'set/assumptionRule (list 'implies (list 'unit '?u) (list deploy '?u)))
                  'CxEmp)
        (v/assert kb (list 'asp/atLeast 2 '?u (list deploy '?u)) 'CxEmp {:strength :monotonic})
        ;; NO unit facts, so deploy grounds to zero choice heads
        (let [r (v/assert kb (list 'do/label 'CxEmp 'CxEmpPlan :sat) 'CxEmp)]
          (is (empty? (:labelings r))
              "the global floor over an empty choice is infeasible, not silently dropped"))))))

;; ---- 6. an interrupted optimisation hands back its best model ------------

(deftest interrupted-optimisation-hands-back-its-best-model
  ;; A cap over 30 interchangeable cities has C(30, 10) equal-cost optima: the solver finds
  ;; one in milliseconds, but proving it optimal takes more search than the default solve
  ;; limit, so the `:one` solve stops at that limit WITH a model in hand.  That model
  ;; satisfies every hard constraint (each city builds one thing, at most ten transports),
  ;; so the solve returns it, marked `:best-effort? true`, instead of discarding it and
  ;; reporting no answer.
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [build]
        (install-build! kb 'CxBestEffort build (mapv #(symbol (str "C" %)) (range 30)))
        (v/assert kb (list 'asp/atMost 10 '?c (list build '?c 'transport))
                  'CxBestEffort {:strength :monotonic})
        (let [r     (v/assert kb (list 'do/label 'CxBestEffort 'CxBestEffortPlan :one) 'CxBestEffort)
              lab   (first (:labelings r))
              trans (set (builds-of lab build 'transport))
              army  (set (builds-of lab build 'army))]
          (testing "the solve is marked best-effort — a model found, optimality unproven"
            (is (true? (:best-effort? r))))
          (testing "and it hands back a valid labeling, not an empty fallback"
            (is (= 30 (+ (count trans) (count army))) "every city still builds exactly one")
            (is (<= (count trans) 10) "the hard cap still binds")
            (is (empty? (clojure.set/intersection trans army)))))))))

;; ---- 7. a weighted bound: each head counts the weight a fact gives it ----

(defn- refusal-type [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))

(deftest a-weighted-bound-is-a-marked-constraint-rule
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [load]
      (let [body (list 'and (list load '?c) (list 'tons '?c '?w))
            h    (v/assert kb (list 'asp/atMostSum 9 '?w '?c body) 'CxUniverse)
            sx   (sentex-of kb h)]
        (testing "it stores as a hard constraint rule whose marker carries the bound and both variables"
          (is (= :hard (rules/constraint-of sx)))
          (is (= [:at-most 9] ((juxt :op :k) (rules/cardinality-of sx))))
          (is (every? some? ((juxt :weight :counted) (rules/cardinality-of sx)))))
        (testing "the authored surface comes back"
          (is (= ['asp/atMostSum 9] (take 2 (rules/rewrap-sentex (v/sentence-of sx) sx)))))
        (testing "the soft twin stores soft, and is a distinct rule"
          (let [soft (v/assert kb (list 'asp/softAtMostSum 9 '?w '?c body) 'CxUniverse)]
            (is (= :soft (rules/constraint-of (sentex-of kb soft))))
            (is (not= h soft))))))))

(deftest a-malformed-weighted-bound-is-refused-and-check-reports-it
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [load]
      (let [body (list 'and (list load '?c) (list 'tons '?c '?w))]
        (doseq [bad [(list 'asp/atMostSum 9 'W '?c body)
                     (list 'asp/atMostSum 9 '?c '?c body)
                     (list 'asp/atMostSum 9 '?x '?c body)
                     (list 'asp/atMostSum 9 '?c body)
                     (list 'asp/atMostSum -1 '?w '?c body)]]
          (testing (pr-str bad)
            (is (= :not-well-formed (refusal-type #(v/assert kb bad 'CxUniverse))))
            (is (= :not-well-formed (:type (first (v/check kb bad 'CxUniverse)))))))))))

(defn- install-cargo!
  "Cargo over `ctx`: each item in `tons` loads or not (a choice), and an item left behind
  costs 1, so the optimum loads as many items as the asserted bound admits."
  [kb ctx load tons]
  (v/assert kb (list 'set/assumptionRule (list 'implies (list 'cargo '?c) (list load '?c))) ctx)
  (v/assert kb (list 'set/softConstraint
                     (list 'implies (list 'and (list 'cargo '?c) (list 'not (list load '?c)))
                           (list 'left_behind '?c)))
            ctx {:strength :monotonic})
  (doseq [[c w] tons]
    (v/assert kb (list 'cargo c) ctx {:strength :monotonic})
    (v/assert kb (list 'tons c w) ctx {:strength :monotonic})))

(defn- loaded [labeling load]
  (set (for [s (:true labeling) :when (= load (first s))] (second s))))

(defn- label-one [kb ctx]
  (first (:labelings (v/assert kb (list 'do/label ctx (symbol (str ctx "Plan")) :one) ctx))))

(deftest at-most-sum-caps-the-total-weight
  ;; Items of 5, 4, 3 and 2 tons under a 9-ton cap: three items fit (4 + 3 + 2), where a
  ;; headcount cap of 9 would load all four (14 tons).
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [load]
        (install-cargo! kb 'CxHold load '{I1 5 I2 4 I3 3 I4 2})
        (v/assert kb (list 'asp/atMostSum 9 '?w '?c (list 'and (list load '?c) (list 'tons '?c '?w)))
                  'CxHold {:strength :monotonic})
        (is (= '#{I2 I3 I4} (loaded (label-one kb 'CxHold) load)))))))

(deftest at-most-sum-groups-by-the-uncounted-variables
  ;; Two 5-ton trucks and items of 4, 3, 2 and 1 tons, each on at most one truck: the cap is
  ;; one weight body per truck, so every item rides (4 + 1, 3 + 2) and no truck passes 5.
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [onto]
        (doseq [c '[I1 I2 I3 I4]] (v/assert kb (list 'cargo c) 'CxTrucks {:strength :monotonic}))
        (doseq [[c w] '{I1 4 I2 3 I3 2 I4 1}] (v/assert kb (list 'tons c w) 'CxTrucks {:strength :monotonic}))
        (doseq [t '[T1 T2]] (v/assert kb (list 'truck t) 'CxTrucks {:strength :monotonic}))
        (v/assert kb (list 'set/assumptionRule
                           (list 'implies (list 'and (list 'cargo '?c) (list 'truck '?t)) (list onto '?c '?t)))
                  'CxTrucks)
        (v/assert kb (list 'functional onto) 'CxTrucks {:strength :monotonic})
        (v/assert kb (list 'set/softConstraint
                           (list 'implies (list 'and (list 'cargo '?c)
                                                (list 'not (list onto '?c 'T1))
                                                (list 'not (list onto '?c 'T2)))
                                 (list 'left_behind '?c)))
                  'CxTrucks {:strength :monotonic})
        (v/assert kb (list 'asp/atMostSum 5 '?w '?c (list 'and (list onto '?c '?t) (list 'tons '?c '?w)))
                  'CxTrucks {:strength :monotonic})
        (let [lab   (label-one kb 'CxTrucks)
              tons  '{I1 4 I2 3 I3 2 I4 1}
              rides (for [s (:true lab) :when (= onto (first s))] [(nth s 1) (nth s 2)])
              per-t (reduce (fn [m [c t]] (update m t (fnil + 0) (tons c))) {} rides)]
          (is (= '#{I1 I2 I3 I4} (set (map first rides))) "every item rides")
          (is (every? #(<= % 5) (vals per-t)) "and no truck carries over 5 tons"))))))

(deftest at-least-sum-forces-a-minimum-total
  ;; Deploying costs 1 per unit, and units have strength 3, 2, 2 and 1: a floor of strength 4
  ;; deploys two units reaching it, where a headcount floor of 4 would deploy all four.
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [deploy]
        (v/assert kb (list 'set/assumptionRule (list 'implies (list 'unit '?u) (list deploy '?u))) 'CxForce)
        (v/assert kb (list 'set/softConstraint (list 'implies (list deploy '?u) (list 'costd '?u)))
                  'CxForce {:strength :monotonic})
        (let [power '{U1 3 U2 2 U3 2 U4 1}]
          (doseq [[u w] power]
            (v/assert kb (list 'unit u) 'CxForce {:strength :monotonic})
            (v/assert kb (list 'power u w) 'CxForce {:strength :monotonic}))
          (v/assert kb (list 'asp/atLeastSum 4 '?w '?u (list 'and (list deploy '?u) (list 'power '?u '?w)))
                    'CxForce {:strength :monotonic})
          (let [out (loaded (label-one kb 'CxForce) deploy)]
            (is (= 2 (count out)))
            (is (<= 4 (reduce + (map power out))))))))))

(deftest soft-at-most-sum-is-tradeable
  ;; Under a 5-ton cap, items of 5, 4, 3 and 2 tons leave two behind at best (cost 2), and
  ;; breaching the soft cap costs 1, so the soft cap loads all four.
  (when asp?
    (letfn [(loaded-under [wrapper]
              (tu/with-cleared-kb [kb tu/fresh]
                (tu/with-terms [load]
                  (install-cargo! kb 'CxSoftHold load '{I1 5 I2 4 I3 3 I4 2})
                  (v/assert kb (list wrapper 5 '?w '?c (list 'and (list load '?c) (list 'tons '?c '?w)))
                            'CxSoftHold {:strength :monotonic})
                  (count (loaded (label-one kb 'CxSoftHold) load)))))]
      (is (= 2 (loaded-under 'asp/atMostSum)))
      (is (= 4 (loaded-under 'asp/softAtMostSum))))))

(deftest a-weighted-bound-refuses-what-the-solver-cannot-encode
  ;; A weight is data, so the solve that grounds it refuses a negative or non-integer one,
  ;; and a body over two choice literals, which has no single head to weigh.
  (when asp?
    (doseq [[label tons bound]
            [["a negative weight" '{I1 -2 I2 3} '(and (LOAD ?c) (tons ?c ?w))]
             ["a non-integer weight" '{I1 2.5 I2 3} '(and (LOAD ?c) (tons ?c ?w))]
             ["two choice literals" '{I1 2 I2 3} '(and (LOAD ?c) (LOAD ?d) (tons ?c ?w) (tons ?d ?x))]]]
      (testing label
        (tu/with-cleared-kb [kb tu/fresh]
          (tu/with-terms [load]
            (install-cargo! kb 'CxBad load tons)
            (v/assert kb (list 'asp/atMostSum 4 '?w '?c (walk/postwalk-replace {'LOAD load} bound))
                      'CxBad {:strength :monotonic})
            (is (= :not-well-formed (refusal-type #(label-one kb 'CxBad))))))))))

;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.cardinality-solve-test
  "Native cardinality bounds on a choice predicate: `(asp/atMost k ?v pattern)` and
  `(asp/atLeast k ?v pattern)` (and the soft twins), which `solve-context` grounds to ONE
  solver cardinality atom per group rather than the `C(n, k+1)` subset nogoods a
  hand-written encoding needs (docs/solving.md).

  The surface mirrors `agg/count`'s projection: `?v` is the counted variable, the
  pattern's other variables are the group, so `(asp/atMost 6 ?c (build ?c transport))` is
  one global bound and `(asp/atMost cap ?a (ferry ?a ?t))` is one bound per `?t`.

  End-to-end tests need an ASP backend and are guarded on `asp?`; the wrapper/record and
  refusal unit tests are not."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.asp.solver :as solver]
            [vaelii.impl.config :as config]
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
  ;; The rule stores as `(set/hardConstraint (implies …))`, but `rewrap` restores the
  ;; authored `asp/atMost` form for export/display rather than leaking the internal one.
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [build]
      (let [h  (v/assert kb (list 'asp/atMost 2 '?c (list build '?c 'transport)) 'CxUniverse)
            sx (sentex-of kb h)
            surface (rules/rewrap (:sentence sx) (:direction sx) (:defeasible sx)
                                  (:assumption sx) (:constraint sx))]
        (is (= 'asp/atMost (first surface)) "the surface wrapper comes back, not set/hardConstraint")
        (is (= 2 (second surface)) "and the bound")
        (let [soft (v/assert kb (list 'asp/softAtMost 2 '?c (list build '?c 'transport)) 'CxUniverse)
              ssx  (sentex-of kb soft)]
          (is (= 'asp/softAtMost
                 (first (rules/rewrap (:sentence ssx) (:direction ssx) (:defeasible ssx)
                                      (:assumption ssx) (:constraint ssx))))))))))

;; ---- 2. end to end: the bound prunes the models --------------------------

(defn- install-build!
  "A build allocation over `cities`: each city builds transport or army (a choice),
  exactly one (`functional` + a hard at-least-one), and army costs 1 so the solver
  prefers transport up to whatever cap is asserted."
  [kb ctx build cities]
  (doseq [v '[transport army]]
    (v/assert kb (list 'set/assumptionRule (list 'implies (list 'cand '?c) (list build '?c v)))
              ctx {:direction :forward}))
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
  ;; Thirty cities, exactly ten transports (a hard at-most-10 AND at-least-10).  The
  ;; at-most bound alone is `C(30, 11)` ≈ 54M subset nogoods under a hand-written encoding
  ;; — the heap-death the app clamps its inputs to avoid.  Each native bound grounds to
  ;; ONE weight-body constraint, so the whole program grounds instantly, and a plain
  ;; `:sat` solve (no optimization to prove) finds a model at once.  Both bounds bind:
  ;; exactly ten transports, and every city still builds one thing.
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [build]
        ;; a soft-free program, so `:sat` is plain satisfaction with nothing to optimize —
        ;; the point is that GROUNDING stays linear, not that a symmetric optimum is cheap
        (doseq [v '[transport army]]
          (v/assert kb (list 'set/assumptionRule (list 'implies (list 'cand '?c) (list build '?c v)))
                    'CxBig {:direction :forward}))
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
                  'CxAtl {:direction :forward})
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
                  'CxFer {:direction :forward})
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
  ;; `assert` throws on a malformed bound; `check` must PREDICT that as a returned
  ;; problem, not throw out of itself.  A batch critic — the web save preview, the RPC
  ;; `:check` op — feeds `check` lines and reports a problem per line, so a throw would
  ;; abort the whole batch instead of flagging the one bad line.
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
                            'CxSAtl {:direction :forward})
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
  ;; A GLOBAL `asp/atLeast` whose choice predicate grounds to no head (an empty global
  ;; group) is infeasible — the floor cannot vanish because nothing was a candidate,
  ;; where a single candidate under `atLeast 2` would already be infeasible.  A
  ;; co-resident, independently satisfiable choice keeps the program non-empty, so the
  ;; zero labelings come from the floor and not from an empty program.
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [deploy]
        (v/assert kb '(set/assumptionRule (implies (thing ?x) (other ?x))) 'CxEmp {:direction :forward})
        (v/assert kb '(thing W) 'CxEmp {:strength :monotonic})
        (v/assert kb (list 'set/assumptionRule (list 'implies (list 'unit '?u) (list deploy '?u)))
                  'CxEmp {:direction :forward})
        (v/assert kb (list 'asp/atLeast 2 '?u (list deploy '?u)) 'CxEmp {:strength :monotonic})
        ;; NO unit facts, so deploy grounds to zero choice heads
        (let [r (v/assert kb (list 'do/label 'CxEmp 'CxEmpPlan :sat) 'CxEmp)]
          (is (empty? (:labelings r))
              "the global floor over an empty choice is infeasible, not silently dropped"))))))

;; ---- 6. an interrupted optimisation hands back its best model ------------

(deftest interrupted-optimisation-hands-back-its-best-model
  ;; A cap over 30 interchangeable cities has C(30, 10) equal-cost optima: clingo finds one
  ;; in milliseconds but proves it optimal slowly, so under a short budget the `:one` solve
  ;; is cancelled WITH a model in hand. That model satisfies every hard constraint (each
  ;; city builds one thing, at most ten transports), so the solve now returns it, marked
  ;; `:best-effort? true`, instead of discarding it and reporting no answer. Gated on a
  ;; short VAELII_ASP_TIME_LIMIT — the 60 s default would let the proof run for a minute —
  ;; so run it deliberately, e.g. `VAELII_ASP_TIME_LIMIT=5 lein with-profile +with-clingo
  ;; test vaelii.cardinality-solve-test`.
  (when (and asp? (<= 1 (config/asp-time-limit) 15))
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

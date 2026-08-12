;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.solve-context-test
  "assumptionRules and persistent, inert solve/labeling contexts
  (`vaelii.impl.asp.solve-context`, the `do/label` and `do/classify` imperatives).

  The feature's whole claim is that a solve becomes a **persisted, inert artifact** that
  leaves the always-true base KB untouched, so the tests pin exactly that:

    * an `assumptionRule` never forward-chains — its head is a choice, not a truth;
    * an inert fact is stored and inspectable but never IN, so it forms no nogood and
      moves no belief — which is what lets many labelings coexist;
    * `do/label` materializes one labeling context per optimal answer set, base belief
      unchanged; `do/classify` gathers brave/cautious over them.

  Enumeration needs an ASP backend, so the `do/label`/`do/classify` end-to-end tests are
  guarded on `asp?`; the assumptionRule and inert-fact unit tests are not — those are the
  representation, independent of any solver."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.asp.solver :as solver]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.rules :as rules]
            [vaelii.test-util :as tu]))

(def ^:private asp? (solver/available?))

(defn- sentex-of [kb h] (p/get-sentex (:records kb) h))

;; ---- 1. assumptionRule: a choice rule, inference-inert ------------------

(deftest an-assumption-rule-is-distinct-from-its-bare-twin
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [candidate color]
      (let [bare (v/assert kb (list 'implies (list candidate '?c) (list color '?c 'red)) 'CxUniverse)
            asm  (v/assert kb (list 'set/assumptionRule
                                    (list 'implies (list candidate '?c) (list color '?c 'red)))
                           'CxUniverse)]
        (testing "the wrapper is part of identity, so they are two sentexes"
          (is (not= bare asm)))
        (testing "assumption? reads the record, true only for the wrapped one"
          (is (rules/assumption? (sentex-of kb asm)))
          (is (not (rules/assumption? (sentex-of kb bare)))))
        (testing "and re-asserting the same assumptionRule is idempotent"
          (is (= asm (v/assert kb (list 'set/assumptionRule
                                        (list 'implies (list candidate '?c) (list color '?c 'red)))
                               'CxUniverse))))))))

(deftest an-assumption-rule-does-not-forward-chain
  ;; The defining behaviour: a choice head is not a derived truth. The bare rule fires
  ;; on the same fact; the assumptionRule stays dormant until a solve grounds it.
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [candidate color Item]
      (v/assert kb (list 'implies (list candidate '?c) (list color '?c 'red)) 'CxUniverse)
      (v/assert kb (list 'set/assumptionRule (list 'implies (list candidate '?c) (list color '?c 'blue)))
                'CxUniverse)
      (v/assert kb (list candidate Item) 'CxUniverse)
      (is (seq (v/sentexes-matching kb (list color Item 'red) 'CxUniverse)) "bare rule fired")
      (is (empty? (v/sentexes-matching kb (list color Item 'blue) 'CxUniverse)) "assumptionRule did not"))))

;; ---- 2. inert facts: stored, inspectable, never believed ----------------

(deftest an-inert-fact-is-stored-but-never-believed
  ;; inert facts are not premises, so the retract-based neutral teardown cannot clean
  ;; them — a store-mutating test clears instead (like the persistence tests)
  (tu/with-cleared-kb [kb tu/fresh]
    (tu/with-terms [p Tom CxBox]
      (let [h (v/assert-inert kb (list p Tom) 'CxBox)]
        (testing "stored and inspectable"
          (is (some? (sentex-of kb h)))
          (is (some #(= (:id %) h) (v/sentexes-in-context kb 'CxBox))))
        (testing "but not a premise, so not believed"
          (is (not (v/in? kb h)))
          (is (empty? (v/sentexes-matching kb (list p Tom) 'CxBox))))
        (testing "and retract! tears it down directly, though it was never a TMS datum"
          (is (= {:removed-sentexes 1 :removed-justifications 0} (v/retract! kb h)))
          (is (nil? (sentex-of kb h)))
          (is (empty? (v/sentexes-in-context kb 'CxBox)))
          (is (empty? (v/find-sentexes kb Tom))))))))

(deftest an-inert-negation-forms-no-nogood
  ;; The property that makes labelings coexist: an inert `(not X)` in a context that
  ;; sees a believed `X` is invisible to the belief-filtered nogood scan.
  (tu/with-cleared-kb [kb tu/fresh]
    (tu/with-terms [p Tom CxBox]
      (v/assert kb (list p Tom) 'CxUniverse)                              ; believed
      (v/assert kb (list 'genlCx 'CxBox 'CxUniverse) 'CxUniverse {:strength :monotonic})
      (v/assert-inert kb (list 'not (list p Tom)) 'CxBox)                 ; inert opposite
      (testing "no contradiction, and the believed side stands"
        (is (zero? (count (v/contradictions kb))))
        (is (seq (v/sentexes-matching kb (list p Tom) 'CxUniverse)))))))

;; ---- 3. do/label: one inert labeling per optimal answer set -------------

(defn- color-choices
  "The user's worked example: pick at most one color for an individual."
  [kb]
  (let [candidate (tu/tmp-pred) color (tu/tmp-pred) item (tu/tmp-ind)]
    (v/assert kb (list 'set/assumptionRule (list 'implies (list candidate '?c) (list color '?c 'red)))
              'CxUniverse)
    (v/assert kb (list 'set/assumptionRule (list 'implies (list candidate '?c) (list color '?c 'blue)))
              'CxUniverse)
    (v/assert kb (list 'functional color) 'CxUniverse)
    (v/assert kb (list candidate item) 'CxUniverse)
    {:color color :item item}))

(deftest label-materializes-one-inert-context-per-answer-set
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (let [{:keys [color item]} (color-choices kb)
            r (v/assert kb (list 'do/label 'CxUniverse (tu/tmp-ctx "Plan")) 'CxUniverse)]
        (testing "two optima: red-world and blue-world"
          (is (= 2 (:count r)))
          (let [worlds (set (map (fn [l] (set (map #(nth % 2) (:true l)))) (:labelings r)))]
            (is (= #{#{'red} #{'blue}} worlds))))
        (testing "each labeling is a total, consistent assignment"
          (doseq [l (:labelings r)]
            (is (= 1 (count (:true l))))
            (is (= 1 (count (:false l))))))
        (testing "base belief is untouched — neither color is believed, no contradiction"
          (is (empty? (v/sentexes-matching kb (list color item 'red) 'CxUniverse)))
          (is (empty? (v/sentexes-matching kb (list color item 'blue) 'CxUniverse)))
          (is (zero? (count (v/contradictions kb)))))
        (testing "and the truth values persist as inert sentexes in each context"
          ;; two truth values plus the labelingOf ownership marker
          (doseq [l (:labelings r)]
            (is (= 3 (count (v/sentexes-in-context kb (:context l)))))))))))

(deftest label-with-no-constraint-keeps-every-choice
  ;; Nothing forbids the choices, so the single optimum keeps them all.
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [candidate wants Item]
        (v/assert kb (list 'set/assumptionRule (list 'implies (list candidate '?c) (list wants '?c 'tea)))
                  'CxUniverse)
        (v/assert kb (list candidate Item) 'CxUniverse)
        (let [r (v/assert kb (list 'do/label 'CxUniverse (tu/tmp-ctx "Plan")) 'CxUniverse)]
          (is (= 1 (:count r)))
          (is (= 1 (count (:true (first (:labelings r)))))))))))

(deftest label-with-no-choices-does-nothing
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [p Tom]
      (v/assert kb (list p Tom) 'CxUniverse)
      (let [r (v/assert kb (list 'do/label 'CxUniverse (tu/tmp-ctx "Plan")) 'CxUniverse)]
        (is (zero? (:count r)))
        (is (= :no-choices (:reason r)))))))

(deftest grounding-honors-the-assumption-rules-exception
  ;; ground-heads is a fourth consumer of a rule's firing beside the three chainers:
  ;; a binding the exceptWhen holds of is not offered as a choice, the same decision
  ;; the chainers make by refusing to fire (docs/exceptions.md).
  (tu/with-cleared-kb [kb tu/fresh]
    (tu/with-terms [candidate banned wants Item Other]
      (v/assert kb (list 'exceptWhen (list banned '?c)
                         (list 'set/assumptionRule
                               (list 'implies (list candidate '?c) (list wants '?c 'tea))))
                'CxUniverse)
      (v/assert kb (list candidate Item) 'CxUniverse)
      (v/assert kb (list banned Item) 'CxUniverse)
      (testing "the only candidate is excepted, so there is nothing to solve"
        (let [r (v/assert kb (list 'do/label 'CxUniverse (tu/tmp-ctx "Plan")) 'CxUniverse)]
          (is (zero? (:count r)))
          (is (= :no-choices (:reason r)))))
      (when asp?
        (testing "an unbanned candidate is still offered"
          (v/assert kb (list candidate Other) 'CxUniverse)
          (let [r (v/assert kb (list 'do/label 'CxUniverse (tu/tmp-ctx "Plan")) 'CxUniverse)]
            (is (= 1 (:count r)))
            (is (= [(list wants Other 'tea)] (:true (first (:labelings r)))))))))))

;; ---- 6. groundings are never stored; a re-run replaces -------------------

(deftest groundings-are-never-stored
  ;; The menu is solver working state: it comes back in the result, and nothing
  ;; lands in the records beyond the labeling truth values themselves.
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (let [{:keys [color item]} (color-choices kb)
            r (v/assert kb (list 'do/label 'CxUniverse 'CxMenuPlan) 'CxUniverse)]
        (testing "the menu comes back in the result instead"
          (is (= #{(list color item 'red) (list color item 'blue)} (set (:choices r)))))
        (testing "no options context exists, in the hierarchy or as an extent"
          (is (not (contains? (set (v/contexts kb)) 'CxMenuPlanOptions)))
          (is (zero? (v/count-in-context kb 'CxMenuPlanOptions))))
        (testing "the choice predicate is stored only as labeling truth values"
          ;; two labelings × (one positive + one negative) — a stored menu would add
          ;; two more under the functor root
          (is (= 4 (v/count-with-functor kb color))))))))

(deftest label-replaces-a-previous-run
  ;; assert-inert is find-or-create and numbering restarts at 1, so without the
  ;; replace sweep a re-run after the base moved would union two groundings' truth
  ;; values into one context and leave surplus stale contexts for classify to sweep
  ;; back in.
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [candidate color Item]
        (v/assert kb (list 'set/assumptionRule
                           (list 'implies (list candidate '?c) (list color '?c 'red)))
                  'CxUniverse)
        (v/assert kb (list 'set/assumptionRule
                           (list 'implies (list candidate '?c) (list color '?c 'blue)))
                  'CxUniverse)
        (let [fh   (v/assert kb (list 'functional color) 'CxUniverse)
              cand (v/assert kb (list candidate Item) 'CxUniverse)
              r1   (v/assert kb '(do/label CxUniverse CxReplacePlan) 'CxUniverse)]
          (is (= 2 (:count r1)) "the clash splits the optima: two worlds")
          (testing "the base moves — the clash is retracted — and a re-run replaces"
            (v/retract! kb fh)
            (let [r2 (v/assert kb '(do/label CxUniverse CxReplacePlan) 'CxUniverse)]
              (is (= 1 (:count r2)) "no clash, one world keeping both choices")
              (testing "the surplus stale context dropped out of the hierarchy"
                (is (contains? (set (v/contexts kb)) 'CxReplacePlan1))
                (is (not (contains? (set (v/contexts kb)) 'CxReplacePlan2))))
              (testing "and the surviving context holds exactly the new truth values"
                ;; run 1 left a `(not …)` here; a union would still show it
                (is (= #{(list color Item 'red) (list color Item 'blue)}
                       (set (remove #(= 'labelingOf (first %))
                                    (map :sentence (v/sentexes-in-context kb 'CxReplacePlan1)))))))))
          (testing "a run that grounds no choices clears everything: its result is 'no labelings'"
            (v/retract! kb cand)
            (let [r3 (v/assert kb '(do/label CxUniverse CxReplacePlan) 'CxUniverse)]
              (is (= :no-choices (:reason r3)))
              (is (not (contains? (set (v/contexts kb)) 'CxReplacePlan1))))))))))

(deftest classify-replaces-its-previous-classification
  ;; A stale classification describes labelings that no longer exist; after the base
  ;; moves and the run is re-labeled, only the fresh classification may remain.
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [candidate color Item]
        (v/assert kb (list 'set/assumptionRule
                           (list 'implies (list candidate '?c) (list color '?c 'red)))
                  'CxUniverse)
        (v/assert kb (list 'set/assumptionRule
                           (list 'implies (list candidate '?c) (list color '?c 'blue)))
                  'CxUniverse)
        (let [fh (v/assert kb (list 'functional color) 'CxUniverse)]
          (v/assert kb (list candidate Item) 'CxUniverse)
          (v/assert kb '(do/label CxUniverse CxReclassPlan) 'CxUniverse)
          (let [c1 (v/assert kb '(do/classify CxReclassPlan) 'CxUniverse)]
            (is (= 2 (count (:supportable c1))) "tied worlds: both colors supportable"))
          (v/retract! kb fh)
          (v/assert kb '(do/label CxUniverse CxReclassPlan) 'CxUniverse)
          (let [c2 (v/assert kb '(do/classify CxReclassPlan) 'CxUniverse)]
            (is (= 2 (count (:forced c2))) "one world now: both colors forced")
            (is (empty? (:supportable c2)))
            (testing "the class context holds only the fresh classification"
              (is (= #{(list 'forced (list color Item 'red))
                       (list 'forced (list color Item 'blue))}
                     (set (map :sentence (v/sentexes-in-context kb 'CxReclassPlanClass))))))))))))

(deftest a-backendless-rerun-leaves-the-previous-run-standing
  ;; :no-backend computed nothing, so it must not destroy the artifact it failed to
  ;; replace — unlike :no-choices, which is a real (empty) result.
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (color-choices kb)
      (let [r1 (v/assert kb '(do/label CxUniverse CxKeepPlan) 'CxUniverse)]
        (is (= 2 (:count r1)))
        (with-redefs [solver/available? (constantly false)]
          (let [r2 (v/assert kb '(do/label CxUniverse CxKeepPlan) 'CxUniverse)]
            (is (= :no-backend (:reason r2)))))
        (testing "nothing was cleared"
          (is (contains? (set (v/contexts kb)) 'CxKeepPlan1))
          (is (contains? (set (v/contexts kb)) 'CxKeepPlan2))
          ;; two truth values plus the labelingOf marker, all still standing
          (is (= 3 (count (v/sentexes-in-context kb 'CxKeepPlan1)))))))))

(deftest a-user-context-matching-the-name-pattern-is-not-swept
  ;; Ownership is recorded (the labelingOf marker), never inferred from a name: a
  ;; user context that happens to be named like a labeling is neither read by
  ;; classify nor cleared by a re-run — with a destructive sweep, a name pattern
  ;; would be data loss.
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [p Tom]
        (color-choices kb)
        ;; a real user context whose name collides with what label will mint
        (v/assert kb '(genlCx CxSweepPlan1 CxUniverse) 'CxUniverse
                  {:strength :monotonic})
        (v/assert kb (list p Tom) 'CxSweepPlan1 {:strength :monotonic})
        (v/assert kb '(do/label CxUniverse CxSweepPlan) 'CxUniverse)
        (v/assert kb '(do/label CxUniverse CxSweepPlan) 'CxUniverse)
        (testing "the user's believed fact survived two runs of the sweep"
          (is (seq (v/sentexes-matching kb (list p Tom) 'CxSweepPlan1))))
        (testing "and classify aggregates only the marked labelings"
          (let [c (v/assert kb '(do/classify CxSweepPlan) 'CxUniverse)]
            (is (= 2 (:count c)))
            (is (not-any? #(= (list p Tom) %)
                          (concat (:forced c) (:supportable c) (:excluded c))))))))))

;; ---- 4. do/classify: gather brave/cautious over the labelings -----------

(deftest classify-gathers-brave-cautious-over-labelings
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (let [{:keys [color item]} (color-choices kb)
            into (tu/tmp-ctx "Plan")]
        (v/assert kb (list 'do/label 'CxUniverse into) 'CxUniverse)
        (let [c (v/assert kb (list 'do/classify into) 'CxUniverse)]
          (testing "both colors are supportable — each true in one world, false in the other"
            (is (= #{(list color item 'red) (list color item 'blue)} (set (:supportable c))))
            (is (empty? (:forced c)))
            (is (empty? (:excluded c))))
          (testing "and the classification persists as inert sentexes"
            (is (= #{(list 'supportable (list color item 'red))
                     (list 'supportable (list color item 'blue))}
                   (set (map :sentence (v/sentexes-in-context kb (:class-context c))))))))))))

(deftest classify-marks-an-unconstrained-choice-forced
  ;; A choice no constraint touches is kept in every labeling — a cautious consequence.
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (tu/with-terms [candidate wants Item]
        (v/assert kb (list 'set/assumptionRule (list 'implies (list candidate '?c) (list wants '?c 'tea)))
                  'CxUniverse)
        (v/assert kb (list candidate Item) 'CxUniverse)
        (let [into (tu/tmp-ctx "Plan")]
          (v/assert kb (list 'do/label 'CxUniverse into) 'CxUniverse)
          (let [c (v/assert kb (list 'do/classify into) 'CxUniverse)]
            (is (= [(list wants Item 'tea)] (:forced c)))
            (is (empty? (:supportable c)))))))))

;; ---- 5. imperative argument checks --------------------------------------

(deftest the-imperatives-check-their-arguments
  (tu/with-neutral-kb [kb tu/fresh]
    (doseq [form [(list 'do/label 'CxUniverse)                 ; one arg
                  (list 'do/label 'CxUniverse 'A 'B)           ; three
                  (list 'do/classify)                               ; none
                  (list 'do/classify 'A 'B)]]                       ; two
      (is (= :not-assertible
             (try (v/assert kb form 'CxUniverse) nil
                  (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))
          (str "refused: " (pr-str form))))
    (testing "and a do/ imperative is refused inside a rule"
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list 'implies (list 'p '?x) (list 'do/label 'A 'B)) 'CxUniverse))))))

;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.minimize-solve-test
  "`asp/minimize` and a priority-tagged `set/softConstraint`, which normalize into a soft
  constraint carrying the level and weight (docs/solving.md, \"`minimize` /
  soft-constraint priorities\"): a lower-priority weighted minimize breaks a matching's
  plateau without trading a match.  The solving tests are guarded on `asp?`; the normalize
  and rewrap tests run without a backend."
  (:require [clojure.java.io :as io]
            [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.asp.solver :as solver]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.rules :as rules]
            [vaelii.test-util :as tu]))

(def ^:private asp? (solver/available?))

(defn- sentex-of [kb h] (p/get-sentex (:records kb) h))

;; ---- 1. the surface normalizes into a marker-carrying soft constraint ----

(deftest minimize-normalizes-into-a-soft-with-a-cost-marker
  (testing "asp/minimize → a soft whose consequent is (minimizeCost priority weight-var)"
    (is (= '(set/softConstraint
             (implies (and (pickCity A1 ?c) (stepDist A1 ?c ?w))
                      (minimizeCost 1 ?w)))
           (rules/normalize-minimize
            '(asp/minimize 1 ?w (and (pickCity A1 ?c) (stepDist A1 ?c ?w)))))))
  (testing "the identity on a non-minimize sentence"
    (is (= '(pickCity A1 C1) (rules/normalize-minimize '(pickCity A1 C1))))))

(deftest a-priority-tags-a-soft-constraint-onto-its-marker
  (testing "set/softConstraint P → the priority rides a softPriority marker"
    (is (= '(set/softConstraint
             (implies (unmatched A1) (softPriority 2 (idleArmy A1))))
           (rules/normalize-soft-priority
            '(set/softConstraint 2 (implies (unmatched A1) (idleArmy A1)))))))
  (testing "a bare (unprioritized) soft is left alone"
    (is (= '(set/softConstraint (implies (unmatched A1) (idleArmy A1)))
           (rules/normalize-soft-priority
            '(set/softConstraint (implies (unmatched A1) (idleArmy A1))))))))

(deftest malformed-objectives-are-refused-before-storage
  (testing "a minimize priority must be a positive integer"
    (is (thrown? clojure.lang.ExceptionInfo
                 (rules/normalize-minimize '(asp/minimize 0 ?w (foo A1 ?w)))))
    (is (thrown? clojure.lang.ExceptionInfo
                 (rules/normalize-minimize '(asp/minimize x ?w (foo A1 ?w))))))
  (testing "a minimize weight slot must be a variable the body binds"
    (is (thrown? clojure.lang.ExceptionInfo
                 (rules/normalize-minimize '(asp/minimize 1 7 (foo A1 7)))))
    (is (thrown? clojure.lang.ExceptionInfo
                 (rules/normalize-minimize '(asp/minimize 1 ?w (foo A1 ?c))))
        "?w must occur in the body"))
  (testing "a priority is meaningless on a hard integrity constraint"
    (is (thrown? clojure.lang.ExceptionInfo
                 (rules/normalize-soft-priority
                  '(set/hardConstraint 2 (implies (unmatched A1) (idleArmy A1)))))))
  (testing "a priority must be a positive integer"
    (is (thrown? clojure.lang.ExceptionInfo
                 (rules/normalize-soft-priority
                  '(set/softConstraint -1 (implies (unmatched A1) (idleArmy A1))))))))

(deftest soft-cost-of-reads-level-and-weight-off-a-ground-marker
  (is (= {:priority 1 :weight 5 :marker '(minimizeCost 1 5)}
         (rules/soft-cost-of '(minimizeCost 1 5))))
  (is (= {:priority 2 :marker '(idleArmy A1)}
         (rules/soft-cost-of '(softPriority 2 (idleArmy A1)))))
  (is (= {:priority 1 :marker '(idleArmy A1)}
         (rules/soft-cost-of '(idleArmy A1)))
      "an ordinary soft marker reads back level 1, no weight"))

;; ---- 2. the surface round-trips through the record (rewrap) --------------

(deftest the-objectives-are-marked-soft-and-restore-their-surface
  (tu/with-neutral-kb [kb tu/fresh]
    (let [mini (v/assert kb '(asp/minimize 1 ?w (and (pickCity A1 ?c) (stepDist A1 ?c ?w)))
                         'CxObj)
          soft (v/assert kb '(set/softConstraint 2 (implies (unmatched A1) (idleArmy A1)))
                         'CxObj)]
      (testing "both store as soft constraint rules (never chaining)"
        (is (= :soft (rules/constraint-of (sentex-of kb mini))))
        (is (= :soft (rules/constraint-of (sentex-of kb soft))))
        (is (not (rules/forward-sentex? (sentex-of kb mini))))
        (is (not (rules/backward-sentex? (sentex-of kb mini)))))
      (testing "the priority/weight ride the consequent marker"
        (is (= 'minimizeCost (first (:consequent (sentex-of kb mini)))))
        (is (= 'softPriority (first (:consequent (sentex-of kb soft)))))))))

;; ---- 3. end to end: a weighted minimize breaks a matching plateau --------

(defn- install-pick!
  "Choose at most one city per army over the candidate pairs, maximizing matches at
  priority 2 (an unmatched army costs one) — the plateau every maximum matching ties on."
  [kb ctx cands]
  ;; inert solve rules (choices, constraints, objectives) are asserted monotonic, not
  ;; forward: they never chain, so a `:direction` says nothing — a solve grounds the
  ;; believed ones directly (docs/solving.md)
  (v/assert kb '(set/assumptionRule (implies (candCity ?a ?c) (pickCity ?a ?c)))
            ctx {:strength :monotonic})
  (v/assert kb '(functional pickCity) ctx {:strength :monotonic})
  (doseq [[a c] cands] (v/assert kb (list 'candCity a c) ctx {:strength :monotonic}))
  ;; priority 2 (dominant): an army that takes NONE of its candidate cities costs one
  (doseq [[a cs] (group-by first cands)]
    (v/assert kb (list 'set/softConstraint 2
                       (list 'implies
                             (cons 'and (for [[_ c] cs] (list 'not (list 'pickCity a c))))
                             (list 'idleArmy a)))
              ctx {:strength :monotonic})))

(defn- picks-of [labeling]
  (into {} (for [s (:true labeling) :when (= 'pickCity (first s))] [(nth s 1) (nth s 2)])))

(deftest a-distance-minimize-breaks-the-matching-tie
  ;; One army, two reachable cities: the match is a plateau (either city matches one).
  ;; A priority-1 distance minimize breaks it to the nearer city, deterministically.
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (install-pick! kb 'CxTie '[[A1 C1] [A1 C2]])
      (v/assert kb '(asp/minimize 1 ?w (and (pickCity A1 ?c) (stepDist A1 ?c ?w))) 'CxTie
                {:strength :monotonic})
      (v/assert kb '(stepDist A1 C1 1) 'CxTie {:strength :monotonic})
      (v/assert kb '(stepDist A1 C2 5) 'CxTie {:strength :monotonic})
      (let [r (v/assert kb '(do/label CxTie CxTiePlan :one) 'CxTie)]
        (is (= 1 (:count r)))
        (is (= 'C1 (get (picks-of (first (:labelings r))) 'A1))
            "the nearer city wins the tie (distance 1 < 5)")))))

(deftest the-higher-priority-match-dominates-any-lower-priority-weight
  ;; A single reachable city at a huge distance: leaving the army idle costs one at
  ;; priority 2, and NO distance at priority 1 can outweigh it — so the army still
  ;; matches.  This is the lexicographic separation a distinct priority level buys;
  ;; the same weight folded into one level would let 1000 outweigh the match.
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (install-pick! kb 'CxDom '[[A1 C1]])
      (v/assert kb '(asp/minimize 1 ?w (and (pickCity A1 ?c) (stepDist A1 ?c ?w))) 'CxDom
                {:strength :monotonic})
      (v/assert kb '(stepDist A1 C1 1000) 'CxDom {:strength :monotonic})
      (let [r (v/assert kb '(do/label CxDom CxDomPlan :one) 'CxDom)]
        (is (= 'C1 (get (picks-of (first (:labelings r))) 'A1))
            "matched despite distance 1000 — priority 2 dominates priority 1")))))

(deftest two-minimizes-at-one-priority-sum-their-weights
  ;; Within one objective level the cost is the sum over every minimize at that level.  A
  ;; distance minimize alone picks C2 (1 < 3); a fuel minimize at the same level adds 0 to C1
  ;; and 5 to C2, so the summed cost is C1 3 against C2 6 and the pick moves to C1.
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (install-pick! kb 'CxSum '[[A1 C1] [A1 C2]])
      (v/assert kb '(asp/minimize 1 ?w (and (pickCity A1 ?c) (stepDist A1 ?c ?w))) 'CxSum
                {:strength :monotonic})
      (v/assert kb '(stepDist A1 C1 3) 'CxSum {:strength :monotonic})
      (v/assert kb '(stepDist A1 C2 1) 'CxSum {:strength :monotonic})
      (let [r (v/assert kb '(do/label CxSum CxSumPlanOne :one) 'CxSum)]
        (is (= 'C2 (get (picks-of (first (:labelings r))) 'A1))
            "the distance minimize alone picks the nearer city"))
      (v/assert kb '(asp/minimize 1 ?f (and (pickCity A1 ?c) (fuelCost A1 ?c ?f))) 'CxSum
                {:strength :monotonic})
      (v/assert kb '(fuelCost A1 C1 0) 'CxSum {:strength :monotonic})
      (v/assert kb '(fuelCost A1 C2 5) 'CxSum {:strength :monotonic})
      (let [r (v/assert kb '(do/label CxSum CxSumPlanTwo :one) 'CxSum)]
        (is (= 'C1 (get (picks-of (first (:labelings r))) 'A1))
            "the summed level-1 cost is 3 for C1 and 6 for C2")))))

;; ---- 4. malformed input is refused at the entry point that can name it ----

(deftest check-reports-a-malformed-objective-that-assert-refuses
  ;; `check` reports the same `:not-well-formed` problem `assert` throws, as a returned
  ;; problem, for each malformed objective surface.
  (tu/with-neutral-kb [kb tu/fresh]
    (doseq [s '[(asp/minimize 0 ?w (stepDist A1 ?c ?w))
                (asp/minimize 1 ?w (stepDist A1 ?c ?d))
                (asp/minimize 1 7 (stepDist A1 ?c 7))
                (set/softConstraint -1 (implies (unmatched A1) (idleArmy A1)))
                (set/hardConstraint 2 (implies (unmatched A1) (idleArmy A1)))]]
      (testing (pr-str s)
        (is (some #(= :not-well-formed (:type %)) (v/check kb s 'CxObj))
            "check returns the problem instead of throwing")
        (is (= :not-well-formed
               (try (v/assert kb s 'CxObj) nil
                    (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))))))))

(deftest a-hand-written-internal-marker-is-refused
  ;; The six consequent markers the solve surfaces normalize into are not an authored
  ;; spelling.  A hand-written one skips its surface's operand checks, so the rule is refused
  ;; at assert and reported by check, whether the marker is the whole consequent, one conjunct
  ;; of it, or the consequent of a priority-tagged soft.
  (tu/with-neutral-kb [kb tu/fresh]
    (doseq [[s marker] '[[(set/softConstraint (implies (pickCity A1 ?c) (minimizeCost ?c 3)))
                          minimizeCost]
                         [(set/softConstraint (implies (unmatched A1) (softPriority 2 (idleArmy A1))))
                          softPriority]
                         [(set/hardConstraint (implies (pickCity ?a ?c) (cardAtMost ?a ?c)))
                          cardAtMost]
                         [(set/softConstraint (implies (pickCity ?a ?c) (cardAtLeast 1 ?c)))
                          cardAtLeast]
                         [(set/hardConstraint (implies (pickCity ?a ?c) (sumAtMost ?a ?c ?c)))
                          sumAtMost]
                         [(set/softConstraint (implies (pickCity ?a ?c) (sumAtLeast 1 ?c ?a)))
                          sumAtLeast]
                         [(set/softConstraint (implies (unmatched A1) (and (idleArmy A1) (minimizeCost 1 3))))
                          minimizeCost]
                         [(set/softConstraint 2 (implies (unmatched A1) (cardAtMost 1 A1)))
                          cardAtMost]]]
      (testing (pr-str s)
        (is (some #(and (= :not-well-formed (:type %)) (= marker (:marker %)))
                  (v/check kb s 'CxObj)))
        (let [e (try (v/assert kb s 'CxObj) nil
                     (catch clojure.lang.ExceptionInfo e e))]
          (is (= [:not-well-formed marker] [(:type (ex-data e)) (:marker (ex-data e))]))
          (is (re-find #"instead" (ex-message e)) "the refusal names the surface to write"))))
    (testing "the surface forms that normalize into the markers still assert"
      (is (int? (v/assert kb '(asp/atMost 1 ?c (pickCity ?a ?c)) 'CxObj)))
      (is (int? (v/assert kb '(asp/minimize 1 ?w (stepDist A1 ?c ?w)) 'CxObj))))))

(deftest a-weight-that-is-not-a-32-bit-integer-is-refused-at-the-solve
  ;; A minimize's weight is ordinary data, so its type is known only when a solve grounds
  ;; the body.  Grounding refuses a non-integer or a weight outside the solver's 32-bit range
  ;; as :not-well-formed naming the weight, rather than handing the backend a program it
  ;; rejects without naming the fact.
  (when asp?
    (doseq [bad [2.5 'Far 4294967296]]
      (testing (pr-str bad)
        (tu/with-cleared-kb [kb tu/fresh]
          (install-pick! kb 'CxWeight '[[A1 C1] [A1 C2]])
          (v/assert kb '(asp/minimize 1 ?w (and (pickCity A1 ?c) (stepDist A1 ?c ?w))) 'CxWeight
                    {:strength :monotonic})
          (v/assert kb (list 'stepDist 'A1 'C1 bad) 'CxWeight {:strength :monotonic})
          (v/assert kb '(stepDist A1 C2 1) 'CxWeight {:strength :monotonic})
          (let [e (try (v/assert kb '(do/label CxWeight CxWeightPlan :one) 'CxWeight) nil
                       (catch clojure.lang.ExceptionInfo e e))]
            (is (= :not-well-formed (:type (ex-data e))))
            (is (= bad (:weight (ex-data e))))
            (is (re-find #"asp/minimize weight must be an integer" (str (ex-message e))))))))))

;; ---- 5. the objectives export as authored and reload to the same rules ----

(defn- with-tmp-dirs
  "Call `f` with `n` fresh temporary directories, deleting them afterwards."
  [n f]
  (let [dirs (vec (repeatedly n #(.toFile (java.nio.file.Files/createTempDirectory
                                           "vaelii-minimize"
                                           (make-array java.nio.file.attribute.FileAttribute 0)))))]
    (try (apply f dirs)
         (finally (doseq [d dirs, ^java.io.File x (reverse (file-seq d))] (.delete x))))))

(deftest the-objectives-export-as-authored-and-reload-identically
  ;; `export-text!` writes a stored rule through `rules/rewrap`, which restores the authored
  ;; `asp/minimize` and priority-tagged `set/softConstraint` from the internal markers.  The
  ;; reload normalizes them back into the same stored rules, so a second export is
  ;; byte-identical.
  (with-tmp-dirs 2
    (fn [a b]
      (let [file "CxObjExport.txt"
            text (tu/with-cleared-kb [kb tu/fresh]
                   (v/assert kb '(genlCx CxObjExport CxUniverse) 'CxUniverse)
                   (v/assert kb '(asp/minimize 1 ?w (and (pickCity A1 ?c) (stepDist A1 ?c ?w)))
                             'CxObjExport)
                   (v/assert kb '(set/softConstraint 2 (implies (unmatched A1) (idleArmy A1)))
                             'CxObjExport)
                   (v/export-text! kb (.getPath ^java.io.File a))
                   (slurp (io/file a file)))]
        (testing "the file spells the surface forms, not the internal markers"
          (is (re-find #"\(asp/minimize 1 " text))
          (is (re-find #"\(set/softConstraint 2 \(implies " text))
          (is (not (re-find #"minimizeCost|softPriority" text))))
        (testing "the reload stores the same rules, so a second export is byte-identical"
          (tu/with-cleared-kb [kb tu/fresh]
            (v/load-text! kb (.getPath ^java.io.File a))
            (v/export-text! kb (.getPath ^java.io.File b))
            (is (= text (slurp (io/file b file))))))))))

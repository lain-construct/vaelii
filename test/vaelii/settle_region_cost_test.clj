;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.settle-region-cost-test
  "What a settle re-derives, as a **count** — the gate on the two memos being retired
  against the region that moved rather than against a global stamp.

  `clash-nogoods` and `negation-nogoods` each carry every standing pair forward from the
  last settle, and each abandons the carry when something the pairing depends on moves.
  What that costs when the test is wrong in the *cheap* direction is a wrong answer, and
  `clash_oracle_test` / `negation_oracle_test` are what hold it there.  What it costs when
  the test is wrong in the *expensive* direction is a settle proportional to the standing
  set on a KB where nothing about it moved — and since a settle runs after every mutation,
  that is a load quadratic in its own contradictions.  Nothing in the oracles can see it:
  both answers are correct.

  So the claim here is a count, and the counts are exact integers rather than durations,
  for `assert_cost_test`'s reason: a call count is a property of the algorithm where a
  millisecond is a property of the box.  Two workloads, one per memo, each built as the
  KB that turns its guard on:

  * a lone `genl` edge with nothing above or below it, retracted and re-asserted on a KB
    of n standing definitional dilemmas it separates nothing of.  Every edge write bumps
    the relation's generation, so a memo keyed on that generation re-derives every
    standing pair — two `checks/arbitrable-violations` calls apiece, one per side.
  * a lone `genlCx` edge with nothing below it, on a KB of n standing P/¬P dilemmas
    whose contexts it does not reach.  Same shape through the other relation: a memo
    keyed on the generation re-derives every opposed body, at two belief-filtered reads
    and a cross product apiece.

  **The bound is zero, not a small number.**  These edges are about nothing either memo
  holds, so the honest budget is that neither memo is asked anything at all — and a
  budget of zero is the one number that cannot drift quietly upward.  A plain fact is
  retracted beside each as the control, since zero is also what a KB does when the memo
  has stopped working entirely, and the control is what says the standing set is really
  standing.

  Sized at n = 60 rather than at the hundreds the measurement was taken over: the
  quantity is a count, so it does not need a large n to be readable, and the workload
  costs a second."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.settle :as settle]
            [vaelii.test-util :as tu]))

(def ^:private n
  "Standing dilemmas per workload.  Large enough that a per-pair term reads as a
  three-digit count rather than as a rounding one, small enough to cost a second."
  60)

;; ---- the clash memo ------------------------------------------------------

(defn- clash-kb
  "n individuals each holding two separated types, so the KB carries n standing
  definitional dilemmas — plus the two victims: one `genl` edge with nothing above or
  below it, and one plain fact."
  [kb]
  (v/assert kb '(disjoint srca_t srcb_t) 'CxUniverse {:strength :monotonic})
  (dotimes [i n]
    (let [x (symbol (str "SRC" i))]
      (v/assert kb (list 'srca_t x) 'CxUniverse {})
      (v/assert kb (list 'srcb_t x) 'CxUniverse {})))
  (v/assert kb '(genl srcvictim_t srctop_t) 'CxUniverse {:strength :monotonic})
  (v/assert kb '(srcPlain SrcTarget) 'CxUniverse {})
  kb)

(defn- arbitrable-calls
  "`checks/arbitrable-violations` calls made while `f` runs.  Redefined rather than
  instrumented, because the count is the whole measurement and the engine carries no
  counter for it."
  [f]
  (let [calls (atom 0)
        orig  checks/arbitrable-violations]
    (with-redefs [checks/arbitrable-violations
                  (fn [& args] (swap! calls inc) (apply orig args))]
      (f))
    @calls))

(deftest a-genl-edge-elsewhere-re-derives-no-standing-clash
  (let [kb (tu/fresh)]
    (try
      (binding [checks/*arbitrate-constraints?* true]
        (clash-kb kb)
        (is (= n (count (v/contradictions kb)))
            "the standing set is standing, or the counts below are about an empty memo")
        (testing "retracting the lone genl edge asks the checks nothing"
          (let [h (v/handle-of kb '(genl srcvictim_t srctop_t) 'CxUniverse)]
            (is (zero? (arbitrable-calls #(v/retract! kb h))))))
        (testing "and asserting it back asks them nothing either"
          (is (zero? (arbitrable-calls
                      #(v/assert kb '(genl srcvictim_t srctop_t) 'CxUniverse
                                 {:strength :monotonic})))))
        (testing "the control: a plain fact leaving is already free"
          (let [h (v/handle-of kb '(srcPlain SrcTarget) 'CxUniverse)]
            (is (zero? (arbitrable-calls #(v/retract! kb h))))))
        (is (= n (count (v/contradictions kb)))
            "and every standing dilemma is still reported"))
      (finally (tu/clear-kb! kb)))))

;; ---- the negation memo ---------------------------------------------------

(defn- negation-kb
  "n independent P/¬P dilemmas — a fresh predicate and a fresh individual apiece, so no
  pair shares a body with any other — plus the two victims: one `genlCx` edge with
  nothing below it, and one plain fact.

  No separation anywhere, so `constraint-nogoods` short-circuits and the clash memo is
  out of the picture."
  [kb]
  (dotimes [i n]
    (let [pr (symbol (str "srneg" i))
          x  (symbol (str "SRN" i))]
      (v/assert kb (list pr x) 'CxUniverse {})
      (v/assert kb (list 'not (list pr x)) 'CxUniverse {})))
  (v/assert kb '(genlCx CxSrVictim CxUniverse) 'CxUniverse {})
  (v/assert kb '(srPlain SrTarget) 'CxUniverse {})
  kb)

(defn- rederived-bodies
  "Opposed bodies re-derived while `f` runs.  `settle/body-nogoods` is the only
  re-derivation site, so one call is one body the memo did not carry."
  [f]
  (let [calls (atom 0)
        orig  @#'settle/body-nogoods]
    (with-redefs [settle/body-nogoods (fn [& args] (swap! calls inc) (apply orig args))]
      (f))
    @calls))

(deftest a-genlCx-edge-elsewhere-re-derives-no-standing-pairing
  (let [kb (tu/fresh)]
    (try
      (negation-kb kb)
      (is (= n (count (v/contradictions kb)))
          "the standing set is standing, or the counts below are about an empty memo")
      (testing "retracting the lone genlCx edge re-derives no body"
        (let [h (v/handle-of kb '(genlCx CxSrVictim CxUniverse)
                             'CxUniverse)]
          (is (zero? (rederived-bodies #(v/retract! kb h))))))
      (testing "and asserting it back re-derives none either"
        (is (zero? (rederived-bodies
                    #(v/assert kb '(genlCx CxSrVictim CxUniverse)
                               'CxUniverse {})))))
      (testing "the control: a plain fact leaving is already free"
        (let [h (v/handle-of kb '(srPlain SrTarget) 'CxUniverse)]
          (is (zero? (rederived-bodies #(v/retract! kb h))))))
      (is (= n (count (v/contradictions kb)))
          "and every standing dilemma is still reported")
      (finally (tu/clear-kb! kb)))))

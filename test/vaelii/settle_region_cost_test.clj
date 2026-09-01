;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.settle-region-cost-test
  "What a settle costs **the region**, as counts: how often the relabelled region is
  materialized, and how much is re-derived against it.  Two claims, and both are exact
  integers rather than durations, for `assert_cost_test`'s reason — a call count is a
  property of the algorithm where a millisecond is a property of the box.

  ## One: how many times the region is materialized

  `jtms/touched` is the relabelled region, and on the dense network reading it copies the
  whole bitmap into a boxed set — the KB's size on a rebuild, which is the path that
  network exists to make fit.  So the number of reads per settle is a cost in its own
  right, and it is pinned below at **2** for a one-pass settle and **3** for a two-pass
  one: `passes + 1`.

  The two, in the order they happen:

  1. **the pass's own region**, a delay shared by the pass's discovery, its defeat rounds
     and its revival re-seed — one per settle pass, and the one that is *supposed* to be
     there.
  2. **the finish's own region**, forced by the first consumer handed `@region` as an
     argument — the exposure pass, which then declines the work at its own vocabulary
     gate.  A rebuild declines all three exposure passes and the read still happens,
     because `record-clashes!` below them takes the region unconditionally.

  `passes + 1` is what the hoist that produced this shape set out to leave, and this file
  was pinned at `passes + 2` for one release while a third read stood in the way:
  `special/refresh-supersessions` read the region itself rather than taking the value
  `settle-finish` holds four lines above the call, so a KB that had never merged anything
  materialized the whole region — on the dense network, the KB's size on a rebuild — to
  reconcile an empty superseded set.  It takes the value now.  A read appearing here
  again is the regression this counts.

  ## Two: what a settle re-derives

  `clash-nogoods` and `negation-nogoods` each carry every standing pair forward from the
  last settle, and each abandons the carry when something the pairing depends on moves.
  What that costs when the test is wrong in the *cheap* direction is a wrong answer, and
  `clash_oracle_test` / `negation_oracle_test` are what hold it there.  What it costs when
  the test is wrong in the *expensive* direction is a settle proportional to the standing
  set on a KB where nothing about it moved — and since a settle runs after every mutation,
  that is a load quadratic in its own contradictions.  Nothing in the oracles can see it:
  both answers are correct.

  Two workloads, one per memo, each built as the KB that turns its guard on:

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
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.settle :as settle]
            [vaelii.test-util :as tu]))

(def ^:private n
  "Standing dilemmas per workload.  Large enough that a per-pair term reads as a
  three-digit count rather than as a rounding one, small enough to cost a second."
  60)

;; ---- how many times the region is materialized ---------------------------

(defn- region-reads
  "`jtms/touched` calls made while `f` runs.  Redefined rather than instrumented, because
  the count is the whole measurement and the engine carries no counter for it — and
  because a *materialization* is what costs, so the seam has to be the read and not the
  set it hands back.  `jtms/revived` reaches the region through this var too, so its
  one-arity is counted where it forces one and the value-taking arity is not, which is
  the distinction the hoist turns on."
  [f]
  (let [calls (atom 0)
        orig  jtms/touched]
    (with-redefs [jtms/touched (fn [& args] (swap! calls inc) (apply orig args))]
      (f))
    @calls))

(def ^:private one-pass-reads
  "Region materializations a settle that converges in one pass costs: the pass's own
  delay and the finish's delay.  `passes + 1`, which is the shape the hoist set out to
  leave — the ns docstring names the third read this file used to carry and why it went."
  2)

(deftest a-settle-materializes-its-region-once-per-pass-and-once-at-the-finish
  (let [kb (tu/isolated-fresh)]
    (try
      (tu/with-shipped-config
        ;; one write outside the count, so no reading below is a class-loading first call
        (v/assert kb '(srm_warm SrmWarm) 'CxUniverse {})
        (testing "a plain fact — nothing derived, nothing opposed, nothing merged"
          (is (= one-pass-reads (region-reads #(v/assert kb '(srm_plain SrmA) 'CxUniverse {})))))
        (testing "a forward rule firing"
          (v/assert-rule kb ['(srm_trig ?x)] '(srm_concl ?x) 'CxUniverse {:direction :forward})
          (is (= one-pass-reads (region-reads #(v/assert kb '(srm_trig SrmB) 'CxUniverse {}))))
          (is (v/ask? kb '(srm_concl SrmB) 'CxUniverse) "the firing must have placed"))
        (testing "and a retraction"
          (let [h (v/handle-of kb '(srm_plain SrmA) 'CxUniverse)]
            (is (= one-pass-reads (region-reads #(v/retract! kb h)))))))
      (finally (tu/clear-kb! kb)))))

(deftest a-batch-is-charged-per-settle-and-not-per-write
  ;; the reading `with-deferred-settle` exists for: fifty facts and one settle, so the
  ;; region is materialized what a settle costs and not what the batch holds
  (let [kb (tu/isolated-fresh)]
    (try
      (tu/with-shipped-config
        (v/assert kb '(srm_warm SrmWarm) 'CxUniverse {})
        (is (= one-pass-reads
               (region-reads #(v/with-deferred-settle kb
                                (dotimes [i 50]
                                  (v/assert kb (list 'srm_batch (symbol (str "SrmZ" i)))
                                            'CxUniverse {})))))))
      (finally (tu/clear-kb! kb)))))

(deftest a-defeat-costs-one-region-read-and-a-revival-costs-two
  ;; The per-*pass* term, isolated.  A monotonic negation arriving over a default fact
  ;; defeats it within the one pass that discovers it; retracting the winner revives the
  ;; fact, and the revival takes a second pass — so the reading moves by exactly one, which
  ;; is what says the growth term is the pass and not the belief move.
  (let [kb (tu/isolated-fresh)]
    (try
      (tu/with-shipped-config
        (v/assert kb '(srm_neg SrmX) 'CxUniverse {})
        (testing "the defeat converges in one pass"
          (is (= one-pass-reads
                 (region-reads #(v/assert kb '(not (srm_neg SrmX)) 'CxUniverse
                                          {:strength :monotonic}))))
          (is (not (v/ask? kb '(srm_neg SrmX) 'CxUniverse)) "the default must have lost"))
        (testing "the revival takes a second, and one more region read with it"
          (let [h (v/handle-of kb '(not (srm_neg SrmX)) 'CxUniverse)]
            (is (= (inc one-pass-reads) (region-reads #(v/retract! kb h)))))
          (is (v/ask? kb '(srm_neg SrmX) 'CxUniverse) "the default must be believed again")))
      (finally (tu/clear-kb! kb)))))

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
  (v/assert kb '(src_plain SrcTarget) 'CxUniverse {})
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
          (let [h (v/handle-of kb '(src_plain SrcTarget) 'CxUniverse)]
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
  (v/assert kb '(sr_plain SrTarget) 'CxUniverse {})
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
        (let [h (v/handle-of kb '(sr_plain SrTarget) 'CxUniverse)]
          (is (zero? (rederived-bodies #(v/retract! kb h))))))
      (is (= n (count (v/contradictions kb)))
          "and every standing dilemma is still reported")
      (finally (tu/clear-kb! kb)))))

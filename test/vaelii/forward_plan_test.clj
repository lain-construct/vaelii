;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.forward-plan-test
  "Cost-ordering the forward-chain antecedent join (`plan/order` in
  `chain/complete-antecedents` / `solve-rule`).  The semi-naive agenda pins one
  antecedent as the trigger; the planner orders the *rest* by estimated fan-out under
  the trigger's bindings.  The contract under test is the same one the backward
  chainers keep: reordering a conjunction changes only how fast the answer is reached,
  never the derived set — so the KB `plan/*enabled*` builds must match the one it
  builds with planning off.  (Terms are generated once and shared across both runs, so
  the two derived sets are comparable symbol-for-symbol.)"
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.plan :as plan]
            [vaelii.test-util :as tu]))

(defn- both-ways
  "Run `scenario` (a `kb -> value` fn) on a fresh KB with planning on and again with
  it off, returning `[on off]`."
  [scenario]
  [(tu/cleared-kb* tu/fresh scenario)
   (binding [plan/*enabled* false] (tu/cleared-kb* tu/fresh scenario))])

(deftest forward-join-planning-matches-unplanned
  (let [a (tu/tmp-pred) b (tu/tmp-pred) c (tu/tmp-pred) chain4 (tu/tmp-pred)
        X (tu/tmp-ind) Y1 (tu/tmp-ind) Y2 (tu/tmp-ind)
        Z1 (tu/tmp-ind) Z2 (tu/tmp-ind) W1 (tu/tmp-ind) W2 (tu/tmp-ind)
        ctx 'CxFam
        scenario
        (fn [kb]
          ;; chain4(?x,?w) :- a(?x,?y) ∧ b(?y,?z) ∧ c(?z,?w) — a three-way join, so
          ;; whichever fact triggers, two non-trigger antecedents are joined + planned
          (v/assert-rule kb [(list a '?x '?y) (list b '?y '?z) (list c '?z '?w)]
                         (list chain4 '?x '?w) ctx)
          (doseq [f [(list a X Y1) (list a X Y2)
                     (list b Y1 Z1) (list b Y2 Z2)
                     (list c Z1 W1) (list c Z2 W2)]]
            (v/assert kb f ctx))
          (set (map #(vec (rest (:sentence %))) (v/sentexes-matching kb (list chain4 '?x '?w) ctx))))
        [on off] (both-ways scenario)]
    (testing "the three-way forward join derives exactly the reachable endpoints"
      (is (= #{[X W1] [X W2]} on)))
    (testing "planning the join changes cost, not the derived set"
      (is (= on off)))))

(deftest forward-join-planning-handles-a-deferred-antecedent
  ;; a forward rule mixing a join with an evaluable: the planner must keep the deferred
  ;; literal after what binds its inputs (canonical order did), so the derived set is
  ;; unchanged whether planning is on or off.
  (let [birthYear (tu/tmp-pred) olderThan (tu/tmp-pred)
        P1 (tu/tmp-ind) P2 (tu/tmp-ind) ctx 'CxFam
        scenario
        (fn [kb]
          ;; olderThan(?a,?b) :- birthYear(?a,?ya) ∧ birthYear(?b,?yb) ∧ lessThan(?ya,?yb)
          (v/assert-rule kb [(list birthYear '?a '?ya)
                             (list birthYear '?b '?yb)
                             (list 'lessThan '?ya '?yb)]
                         (list olderThan '?a '?b) ctx)
          (v/assert kb (list birthYear P1 1940) ctx)
          (v/assert kb (list birthYear P2 1980) ctx)
          (set (map #(vec (rest (:sentence %))) (v/sentexes-matching kb (list olderThan '?a '?b) ctx))))
        [on off] (both-ways scenario)]
    (testing "the evaluable fires only with its inputs bound: P1 (1940) older than P2 (1980)"
      (is (= #{[P1 P2]} on)))
    (testing "planning does not disturb that"
      (is (= on off)))))

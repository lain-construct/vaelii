;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.violations-test
  "The dropped-conclusion ledger and chain instrumentation: drops accumulate
  across runs instead of being erased by the next assert,
  a completed firing with no placement context is recorded rather than silently
  evaporating, and a truncated chain is visible through `chain-stats`."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(deftest violations-accumulate-across-chaining-runs
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [person rock parentOf looksLike unrelated Boulder Muffet Spot]
      (v/assert kb (list 'genl person 'thing) 'CxUniverse)
      (v/assert kb (list 'genl rock 'thing) 'CxUniverse)
      (v/assert kb (list 'arg parentOf 1 person) 'CxUniverse)
      (v/assert kb (list rock Boulder) 'CxUniverse)
      (v/clear-violations! kb)
      ;; the rule derives (parentOf Boulder Muffet) for the stored (rock Boulder) — an
      ;; argument constraint, so there is no opposing sentex to arbitrate against and
      ;; the conclusion is dropped rather than placed (a disjointness clash *is*
      ;; arbitrated; see constraint_nogood_test)
      (v/assert-rule kb [(list rock '?x)] (list parentOf '?x Muffet) 'CxUniverse)
      (let [drops (filter #(= :arg-type (:violation %)) (v/violations kb))]
        (is (seq drops) "the derived inadmissible conclusion was recorded")
        (is (every? :run drops) "every entry carries its chaining run id"))
      (testing "a later, unrelated assert no longer erases the ledger"
        (v/assert kb (list unrelated Spot) 'CxUniverse)
        (is (seq (filter #(= :arg-type (:violation %)) (v/violations kb)))))
      (testing "clear-violations! is the one way to empty it"
        (v/clear-violations! kb)
        (is (empty? (v/violations kb)))))))

(deftest a-completed-firing-with-no-placement-context-is-recorded
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [dog barksAt Muffet CxIslandA CxIslandB]
      ;; rule and fact live in island contexts with no common descendant: the join
      ;; completes, then the conclusion has nowhere to land
      (v/assert-rule kb [(list dog '?x)] (list barksAt '?x '?x) CxIslandA)
      (v/clear-violations! kb)
      (v/assert kb (list dog Muffet) CxIslandB)
      (let [drops (filter #(= :no-placement (:violation %)) (v/violations kb))]
        (is (seq drops) "the evaporated firing was recorded")
        (is (= (list barksAt Muffet Muffet) (:sentence (first drops))))
        (is (empty? (v/sentexes-matching kb (list barksAt Muffet Muffet) '?ctx))
            "and the conclusion really was not placed")))))

(deftest a-truncated-chain-is-visible-in-chain-stats
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [tmpa tmpb Item]
      (v/assert-rule kb [(list tmpa '?x)] (list tmpb '?x) 'CxUniverse)
      (testing "a plain assert that hits max-depth flags the run"
        (v/assert kb (list tmpa Item) 'CxUniverse {:max-depth 0})
        (let [{:keys [runs last]} (v/chain-stats kb)]
          (is (pos? runs))
          (is (:truncated? last)
              "assert must not discard chain-all's result — nothing else surfaces this")))
      (testing "and an untruncated run clears the flag"
        (v/forward-chain kb)
        (is (not (:truncated? (:last (v/chain-stats kb)))))))))

(deftest the-ledger-keeps-its-newest-entries-rather-than-growing
  ;; The ledger accumulates across chaining runs, so a load that keeps dropping
  ;; conclusions would otherwise grow it without bound.  It is capped — and which end the
  ;; cap drops is the whole question.  Keeping the OLDEST would fill the ledger once and
  ;; then swallow every drop after it: a run whose conclusions are being refused, and a
  ;; ledger with nothing new to say about it, which is the silence the ledger exists to
  ;; break.
  (tu/with-neutral-kb [kb tu/fresh]
    (let [report (requiring-resolve 'vaelii.impl.violations/report)
          cap    @(requiring-resolve 'vaelii.impl.violations/max-violations)
          n      (+ cap 200)
          filed  (mapv (fn [i] {:violation :arg-type :sentence (list 'p i)}) (range n))]
      (v/clear-violations! kb)
      ;; each entry logs at :warn, and the point here is the arithmetic rather than the
      ;; logging — a thousand lines would bury whatever else the run had to report
      (with-bindings* {(requiring-resolve 'taoensso.trove/*log-fn*) (fn [& _] nil)}
        (fn [] (report kb filed)))
      (let [ledger (v/violations kb)]
        (is (= cap (count ledger)) "the ledger stops at its cap instead of growing")
        (is (= (mapv (fn [i] (list 'p i)) (range (- n cap) n)) (mapv :sentence ledger))
            "and what it kept is the newest entries, in the order they were filed")
        (is (every? :run ledger) "each still stamped with the chaining run that filed it"))
      (v/clear-violations! kb))))

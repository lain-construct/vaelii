;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.special-table-test
  "The special-predicate dispatch table's structural guarantees.

  The table (`vaelii.impl.special/entries`) is the one enumeration of the functors
  the engine interprets: integrate, disintegrate, rebuild and wff all walk it.  What
  makes that safe is `check-entries`, which runs at namespace load and refuses an
  entry whose cache arms are partial — the add/remove/rebuild mirroring the old
  hand-written conds left to review is now a build failure.  These tests pin the
  validator's teeth and the table's required contents; no KB is involved, so no
  fixture is either."
  (:require [clojure.spec.alpha :as s]
            [clojure.test :refer [deftest is testing]]
            [vaelii.impl.spec :as vspec]
            [vaelii.impl.special :as special]))

(deftest an-asymmetric-entry-fails-at-load
  (let [f (fn [_ _ _])]
    (testing "an integrate arm without its removal half throws"
      (is (thrown? clojure.lang.ExceptionInfo
                   (special/check-entries [['brokenPred {:integrate f}]]))))
    (testing "a disintegrate arm alone throws — the asymmetry cuts both ways"
      (is (thrown? clojure.lang.ExceptionInfo
                   (special/check-entries [['brokenPred {:disintegrate f}]]))))
    (testing "add and remove without the rebuild half throws — recover would forget it"
      (is (thrown? clojure.lang.ExceptionInfo
                   (special/check-entries [['brokenPred {:integrate f :disintegrate f}]]))))
    (testing "an entry with no arm at all throws — it can only be a typo"
      (is (thrown? clojure.lang.ExceptionInfo
                   (special/check-entries [['emptyPred {}]]))))
    (testing "the throw names the functor and the missing arms"
      (let [data (try (special/check-entries [['brokenPred {:integrate f}]])
                      (catch clojure.lang.ExceptionInfo e (ex-data e)))]
        (is (= 'brokenPred (:functor data)))
        (is (= [:disintegrate :rebuild] (:missing data)))))))

(deftest well-formed-entries-pass
  (let [f (fn [_ _ _])]
    (testing "the full cache triple passes"
      (is (special/check-entries [['okPred {:integrate f :disintegrate f :rebuild f}]])))
    (testing "a wff-only entry passes — argIsa and different maintain no cache"
      (is (special/check-entries [['okPred {:wff f}]])))))

(deftest the-live-table-passes-its-own-check
  ;; `entries` is defined through `check-entries`, so namespace load already proves
  ;; this — asserting it here keeps the wiring itself pinned (a refactor that stops
  ;; routing the def through the validator would pass load and fail here).
  (is (= special/entries (special/check-entries special/entries)))
  (is (= special/table (into {} special/entries))))

(deftest the-vocabulary-the-engine-interprets-is-present
  (testing "every cache-maintaining special predicate has an entry"
    (doseq [f '[genl genlContext disjoint disjointMetatype
                transitive symmetric reflexive functional inverse
                decontextualizedPredicate forcedDecontextualizedPredicate]]
      (is (contains? special/table f) (str f " missing from the table"))))
  (testing "the equality relations are entries too"
    (doseq [f '[rewriteOf sameAs equals]]
      (is (contains? special/table f) (str f " missing from the table"))))
  (testing "the wff-only vocabulary is dispatched through the same table"
    (doseq [f '[argIsa different]]
      (is (contains? special/table f) (str f " missing from the table")))))

(deftest the-property-kinds-marked-and-the-ones-specced-are-the-same-set
  ;; `has-prop?` and `props` are specced on `::vspec/prop-kind`, and the table is what
  ;; decides which kinds exist — a mark declares its kind through `prop-entry`'s
  ;; `:prop`.  Held together in both directions here, because each drift is silent on
  ;; its own: a kind the table marks and the spec omits is a documented call that
  ;; instrumentation refuses, and a kind the spec names and nothing marks is a
  ;; `has-prop?` that can only ever answer false.
  (let [marked  (into #{} (keep :prop) (vals special/table))
        specced (set (s/form ::vspec/prop-kind))]
    (is (contains? marked :transitive) "the table declares its kinds through :prop")
    (is (= marked specced))))

;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.lead-side-cost-test
  "The cost *shape* `res/*lead-side* :auto` buys, as a counted invariant — the complement
  of `matches_hierarchical_test`, which pins that the three lead sides return the same
  *set*.  Same set, different cost, and this is the cost half.

  `f59d6b70` led a broad-type clash retrieval from the term's own postings (a handful)
  rather than one predicate-scoped bucket per sub-predicate (`O(|spec-closure|)`), which
  is what collapsed a 12M-sentex cold rebuild's closing settle.  The win is a *shape*: the
  argument reads a broad retrieval costs are flat in how wide the predicate hierarchy is,
  where the per-spec lead grows with it.  `lein perf` would hold a shape like this as a
  ratio, but this one runs in the default suite so a change that quietly widens `:auto`'s
  read back toward the per-spec cost fails a week before the weekly sweep would say so —
  the same reasoning `clash_oracle_test/the-retrieval-strategy-does-not-change-what-clashes`
  gives for being a default-suite test.

  A **count**, not a duration, for `assert_cost_test`'s reasons: the quantity is an integer
  the engine computes, bit-identical across runs and machines, so the assertion is a shape
  (`:scoped` scales, `:auto` does not) rather than a threshold with a tolerance.  Pinned to
  `:backend :memory` for the same reason that file is: the seams live in `KvIndexStore`."
  (:require [clojure.test :refer [deftest is]]
            [vaelii.core :as v]
            [vaelii.impl.profile :as prof]
            [vaelii.impl.resolution :as res]
            [vaelii.test-util :as tu]))

(defn- arg-reads-at-width
  "The argument-family index reads (`:argument-root` + `:argument-slot`) that answering the
  broad query `(broadRel A ?y)` costs under `lead`, over an isolated KB whose `broadRel`
  has `width` sub-predicates and whose `A` holds two believed postings.  Builds the KB
  outside the instrument and measures only the realized retrieval — `doall`, so `:scoped`'s
  lazy per-spec fan is read to the end rather than short-circuited."
  [lead width]
  (let [kb (tu/isolated-fresh)]
    (try
      (let [subs (mapv #(symbol (str "lscSub" %)) (range width))]
        (doseq [s subs] (v/assert kb (list 'genl s 'lscBroadRel) 'CxPerf {:strength :monotonic}))
        (v/assert kb (list (subs 0) 'LscA 'LscB1) 'CxPerf {:strength :monotonic})
        (v/assert kb (list (subs 1) 'LscA 'LscB2) 'CxPerf {:strength :monotonic})
        (prof/start)
        (binding [res/*hierarchical-retrieval* true, res/*lead-side* lead]
          (doall (res/matches-visible kb '(lscBroadRel LscA ?y) 'CxPerf)))
        (let [r (:reads (prof/stop))]
          (+ (long (get r :argument-root 0)) (long (get r :argument-slot 0)))))
      (finally (prof/stop) (tu/clear-kb! kb)))))

(deftest small-side-reads-are-flat-in-the-hierarchy-width
  (let [scoped-narrow (arg-reads-at-width :scoped 4)
        scoped-wide   (arg-reads-at-width :scoped 16)
        auto-narrow   (arg-reads-at-width :auto 4)
        auto-wide     (arg-reads-at-width :auto 16)]
    ;; the fixture must actually vary the per-spec cost, or a flat `:auto` proves nothing
    (is (> scoped-wide scoped-narrow)
        (str ":scoped must scale with the hierarchy width — the fixture is not widening it ("
             scoped-narrow " -> " scoped-wide ")"))
    ;; the win: leading from the term's two postings costs the same however wide the
    ;; hierarchy above it grows
    (is (= auto-wide auto-narrow)
        (str ":auto's argument reads must be flat in the hierarchy width — the cold-rebuild "
             "small-side gain regressed (" auto-narrow " -> " auto-wide ")"))
    ;; and at the wide end the small side is the cheaper one it was chosen to be
    (is (< auto-wide scoped-wide)
        (str "at width 16 the small side must read fewer than the per-spec lead ("
             auto-wide " vs " scoped-wide ")"))))

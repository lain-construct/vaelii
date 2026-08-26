;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.lead-side-cost-test
  "The cost *shape* `res/*lead-side* :auto` buys, as a counted invariant — the complement
  of `matches_hierarchical_test`, which pins that the three lead sides return the same
  *set*.  Same set, different cost, and this is the cost half.

  `:auto` leads a broad-type clash retrieval from the term's own postings (a handful)
  rather than from one predicate-scoped bucket per sub-predicate (`O(|spec-closure|)`),
  which is what collapses a 12M-sentex cold rebuild's closing settle.  The win is a
  *shape*: the
  argument reads a broad retrieval costs are flat in how wide the predicate hierarchy is,
  where the per-spec lead grows with it.  `lein perf` would hold a shape like this as a
  ratio, but this one runs in the default suite so a change that quietly widens `:auto`'s
  read back toward the per-spec cost fails a week before the weekly sweep would say so —
  the same reasoning `clash_oracle_test/the-retrieval-strategy-does-not-change-what-clashes`
  gives for being a default-suite test.

  A **count**, not a duration, for `assert_cost_test`'s reasons: the quantity is an integer
  the engine computes, bit-identical across runs and machines, so the assertion is a shape
  (`:scoped` scales, `:auto` does not) rather than a threshold with a tolerance.

  The **storage is inherited** and the **switches are pinned**.  A shape holds on every
  backend — the columnar index delegates its flat `key -> set` families to an embedded
  `KvIndexStore`, so the two this file sums are recorded there too — and running it on all
  eight is coverage.  The switches are `tu/with-shipped-config`, and here they are
  belt-and-braces rather than a rescue: the two bindings this fixture already makes decide
  everything this query shape reads, which
  `the-reading-is-the-same-whatever-else-is-switched` measures rather than assumes.  The
  sibling gate `join_lead_cost_test` is the one where the pin carries weight."
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
        (tu/with-shipped-config
          (binding [res/*hierarchical-retrieval* true, res/*lead-side* lead]
            (doall (res/matches-visible kb '(lscBroadRel LscA ?y) 'CxPerf))))
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

(deftest the-reading-is-the-same-whatever-else-is-switched
  ;; Written after measuring, and it says less than it first looked like it would: this
  ;; file's own two bindings already decide everything its query shape reads, and no
  ;; switch outside them moves the number.  `*arg-root-retrieval*` is the one that looks
  ;; like it should — it is what moves a read off `:argument-root`, the family summed
  ;; above — and it gates the `:arg-roots` path for a ground argument STUCK BEHIND A
  ;; VARIABLE.  `(lscBroadRel LscA ?y)` pins its first argument, so it is not that shape
  ;; and the switch never applies.
  ;;
  ;; So this is an invariance rather than a rescue, and worth a test for the reason the
  ;; sibling gate is: a query shape edited into the stuck form would start reading
  ;; through a switch nothing here pins, and the number would move for a reason no line
  ;; in this file mentions.
  (let [base (arg-reads-at-width :auto 4)]
    (doseq [[label sym value] [["arg-root"      'vaelii.impl.resolution/*arg-root-retrieval* false]
                               ["structural"    'vaelii.impl.resolution/*structural-index* false]
                               ["min-depth"     'vaelii.impl.sentex/*min-indexed-depth* 2]
                               ["literal-cache" 'vaelii.impl.literal-cache/*enabled* false]]]
      (with-bindings* {(requiring-resolve sym) value}
        (fn [] (is (= base (arg-reads-at-width :auto 4))
                   (str "the argument reads moved under " label
                        " — a switch this file neither varies nor mentions")))))))

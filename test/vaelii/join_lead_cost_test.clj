;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.join-lead-cost-test
  "The cost *shape* the forward join's argument lead buys (`chain/join-matches`), as a
  counted invariant — the forward twin of `lead_side_cost_test`.

  A non-trigger antecedent `(broad ?x)` joined with `?x` already bound is one
  membership question.  Through the trie it is one walk per member of `broad`'s
  sub-predicate closure, so the firing's read count grows with how wide the type
  hierarchy under the antecedent is; through the argument lead it is the term's own
  postings, narrowed to the closure in memory, and flat in that width.  Same set either
  way — `matches_hierarchical_test` pins that — and this pins the cost half, as a
  **count** rather than a duration, for `assert_cost_test`'s reasons: an integer the
  engine computes, identical across runs and machines.

  **Width 0 is the fourth arm and it is not a boundary case.**  A functor with no
  sub-predicates is the overwhelmingly common one — every binary predicate nobody has
  written a `genl` under — and there the lead has no fan to collapse: `res/match-pattern`
  fast-paths a singleton closure to a single `raw-match`, whose `candidate-handles`
  already reads the argument roots for the shape the trie cannot narrow.  Taking the lead
  anyway buys nothing and pays for the apparatus, so at width 0 the join must read
  **exactly** what the reference matcher reads.  Varying only the width could never see
  that: a cost that is wrong at every width is flat in the width, and flat is what the
  three assertions below were written to reward.

  The axis is **`chain/*matcher*`**, not `res/*hierarchical-retrieval*`, and that is what
  makes the width-0 arm a claim about the join rather than about the run around it.
  Binding the matcher to anything not `identical?` to `res/match-pattern` is the one thing
  `join-matches` reads to decline the lead (that is the rete seam, and its docstring says
  so), so the reference arm is the reference *join* with the rest of the engine untouched.
  The retrieval switch would have moved the settle and the placement reads too, and at
  width 0 those are the whole difference between the arms.

  The **storage is inherited** and the **switches are pinned**, which is the opposite
  split from `assert_cost_test` and the right one here: what is claimed is a *shape* —
  flat against growing — and a shape holds on every backend, so running it on all eight is
  coverage rather than noise.  What a shape cannot survive is a different reader
  answering, which is what `tu/with-shipped-config` holds still."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.chain :as chain]
            [vaelii.impl.profile :as prof]
            [vaelii.impl.resolution :as res]
            [vaelii.test-util :as tu]))

(defn- reference-matcher
  "`res/match-pattern` behind one wrapper, so it is **not** `identical?` to it.  That one
  bit is what `chain/join-matches` reads to decline the argument lead, so this arm is the
  reference join answering the same set through the same reader — and nothing else in the
  run moves.  A plain `res/match-pattern` here would be the shipped arm twice over."
  [kb g context]
  (res/match-pattern kb g context))

(defn- firing-reads-at-width
  "The index reads a single forward firing costs when its bound type antecedent sits
  over a `jlc_broad` with `width` sub-predicates, joined by `lead?`'s matcher.  At width 0
  nothing sits under it and the trigger fact is stated at `jlc_broad` itself; above 0 it is
  stated at the first sub-predicate, so the fan is real.

  The KB is built with chaining off and outside the instrument; only the one chaining run
  that fires the rule over the trigger is measured.

  **Every switch the reading depends on is bound rather than inherited**, for the reason a
  count is pinned at all: it is a claim about one configuration.  `tu/with-shipped-config`
  hands back the shipped default of each, and `chain/*matcher*` is bound within it because
  that one is the axis under test.  It is also the one that bites the other way: under
  `VAELII_RETE=1`, whose `enable!` root-binds the alpha matcher, an unpinned run would
  answer both arms out of RAM and read the identical count — the rete seam behaving as
  `join-matches` documents, not a lead that regressed."
  [lead? width]
  (let [kb (tu/isolated-fresh)]
    (try
      (let [subs (mapv #(symbol (str "jlc_sub_" %)) (range width))]
        (doseq [s subs] (v/assert kb (list 'genl s 'jlc_broad) 'CxPerf {:strength :monotonic}))
        (v/assert kb (list (if (pos? width) (subs 0) 'jlc_broad) 'JlcA) 'CxPerf
                  {:strength :monotonic :chain? false})
        (v/assert-rule kb ['(jlcTrig ?x) '(jlc_broad ?x)] '(jlcConcl ?x) 'CxPerf
                       {:direction :forward :chain? false})
        (let [trig (v/assert kb '(jlcTrig JlcA) 'CxPerf {:strength :monotonic :chain? false})]
          (prof/start)
          (tu/with-shipped-config
            (binding [chain/*matcher* (if lead? res/match-pattern reference-matcher)]
              (chain/chain kb [trig] nil)))
          (let [r (:reads (prof/stop))]
            (is (v/ask? kb '(jlcConcl JlcA) 'CxPerf) "the firing must actually have placed")
            (reduce + 0 (vals r)))))
      (finally (prof/stop) (tu/clear-kb! kb)))))

(deftest a-bound-type-antecedent-joins-flat-in-the-subtype-width
  (let [trie-narrow (firing-reads-at-width false 4)
        trie-wide   (firing-reads-at-width false 16)
        lead-narrow (firing-reads-at-width true 4)
        lead-wide   (firing-reads-at-width true 16)]
    ;; the fixture must actually widen the trie's cost, or a flat lead proves nothing
    (is (> trie-wide trie-narrow)
        (str "the trie fan must scale with the subtype width — the fixture is not widening "
             "it (" trie-narrow " -> " trie-wide ")"))
    ;; the win: leading from the bound term's postings costs the same however many
    ;; subtypes sit under the antecedent's type
    (is (= lead-wide lead-narrow)
        (str "the join's reads must be flat in the subtype width — the argument lead "
             "regressed (" lead-narrow " -> " lead-wide ")"))
    (is (< lead-wide trie-wide)
        (str "at width 16 the lead must read fewer than the trie fan ("
             lead-wide " vs " trie-wide ")"))))

(deftest the-pin-holds-both-axes-that-were-measured-to-move-this-reading
  ;; The gate on the gate, and it is cheap enough to live in the default suite: the
  ;; matrix took twenty-four minutes to report that this file was reading the alpha
  ;; matcher's join, and the reading it reported was a plausible number rather than an
  ;; error.  Installed here is a matcher that cannot be mistaken for one — it throws —
  ;; so the claim is not "the count came out the same" but "the sweep's reader was never
  ;; asked".  `binding` rather than `alter-var-root` because a test that moves a root
  ;; hands it to whatever shares its shard.
  (binding [chain/*matcher*
            (fn [& _] (throw (ex-info "with-shipped-config let the sweep's matcher through"
                                      {:type ::matcher-leaked})))]
    (is (pos? (firing-reads-at-width true 4))
        "the measured firing reads the index through the pinned reference matcher")
    (is (pos? (firing-reads-at-width false 4))
        "and so does the trie arm, which is the same pin one binding further in"))
  ;; The second axis, and the one that does not announce itself: `:scoped` leads the
  ;; join from one predicate-scoped bucket per spec, so the reading stops being flat
  ;; (27 at width 4 against 39 at width 16, measured) and the claim above it inverts.
  ;; Nothing installs `:scoped` globally today — this is what makes sure nothing can.
  (binding [res/*lead-side* :scoped]
    (is (= (firing-reads-at-width true 4) (firing-reads-at-width true 16))
        "the pin restores `:auto`, so the join stays flat in the subtype width")))

(deftest with-no-sub-predicates-the-join-reads-what-the-reference-reads
  ;; The lead exists to collapse a fan.  With nothing under the antecedent's functor there
  ;; is no fan, `res/match-pattern`'s singleton-closure fast path is one `raw-match`, and
  ;; the lead's apparatus — three volatiles, a pattern memo, two `prof/profiling?` derefs,
  ;; `lead-agnostic?`'s own count probe — is paid for nothing.  So the two arms must read
  ;; the same number, and a lead taken over a functor with no sub-predicates fails here.
  (testing "width 0 — the common case, and the one the width axis alone cannot see"
    (let [reference (firing-reads-at-width false 0)
          shipped   (firing-reads-at-width true 0)]
      (is (= reference shipped)
          (str "a functor with no sub-predicates has no fan to collapse, so the join must "
               "read exactly what the reference matcher reads (" reference " vs " shipped
               ") — the argument lead is being taken over nothing"))))
  ;; ...and the gate is a gate, not a deletion: the lead must still be taken where the fan
  ;; is real, which is what separates this from removing `matches-hierarchical` outright.
  (testing "the fanned case is still led, so the gate did not turn the lead off"
    (is (< (firing-reads-at-width true 16) (firing-reads-at-width false 16))
        "at width 16 the shipped join must still beat the reference matcher")))

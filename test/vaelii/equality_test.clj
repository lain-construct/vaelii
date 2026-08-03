;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.equality-test
  "Equality — `rewriteOf` / `sameAs` / `equals`, and the `different` that survives
  them.  Every test here holds against the shipped feature: one belief-following
  partition behind the three relations, recomputed on edge change like the `genl`
  and `genlContext` closures beside it.

  Each test pins one decision from [docs/equality.md](../../docs/equality.md) and
  carries a comment naming it.  The shape under test is three assertable relations
  feeding **one equivalence closure**

    (rewriteOf Preferred Deprecated)   directional: the second argument is retired
    (sameAs A B)                       OWL, individuals, neither deprecated
    (equals A B)                       sameAs without the individuals restriction

  and one *unassertable* one, `(different A B ...)`, which is negation as failure
  over that closure — the unique-name assumption OWL drops and vaelii keeps.

  The four claims the shape makes are: a merge **migrates** every sentex mentioning
  the loser and **blocks** (never deletes) the stale spelling; congruence is a side
  effect of the term index, so a nested occurrence is rewritten too; the
  representative is **content-keyed**, so it cannot depend on arrival order; and
  `functional` **derives** an equality rather than throwing.

  House rules apply as everywhere else: gensym'd temporaries via `tu/with-terms`,
  engine vocabulary (`rewriteOf`, `sameAs`, `equals`, `different`, `functional`,
  `genl`, `disjoint`, `symmetric`, contexts) literal, and the neutral fixture
  asserts the KB is restored."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

;; ---- helpers -------------------------------------------------------------

(defn- believed?
  "Is `sentence` stored in `context` **and** currently believed?

  Deliberately not `query`: a merge **rewrites goals**, so `query` on the retired
  spelling answers with the representative's sentex.  That is the right behaviour and
  the wrong instrument for asking which spelling the KB actually believes, which is
  what most of these tests are about."
  [kb sentence context]
  (let [h (v/handle-of kb sentence context)]
    (boolean (and h (v/in? kb h)))))

(defn- stored-not-believed?
  "The signature of a **blocked** spelling: the sentex is still there (handles callers
  hold stay valid) and the JTMS holds it OUT."
  [kb sentence context]
  (let [h (v/handle-of kb sentence context)]
    (and (some? h) (some? (v/sentex kb h)) (not (v/in? kb h)))))

(defn- why-sentences
  "Every sentence mentioned anywhere in a `why` proof tree — the antecedents, the
  rules, and the informants' own sentences.  Flattened, because the doc requires that
  `why` *names* the functional declaration and both facts without saying which slot
  each lands in."
  [node]
  (when (map? node)
    (concat (when-let [s (:sentence node)] [s])
            (when-let [r (:rule node)] [r])
            (mapcat (fn [sup] (cons (:rule sup) (mapcat why-sentences (:because sup))))
                    (:support node)))))

(defn- permutations [coll]
  (if (<= (count coll) 1)
    (list (seq coll))
    (for [i (range (count coll))
          p (permutations (concat (take i coll) (drop (inc i) coll)))]
      (cons (nth coll i) p))))

;; ---- 1. the three relations and one closure ------------------------------
;; DECISION (Three assertable relations, one closure): "`rewriteOf` names the
;; representative and marks the loser deprecated."  Direction is the whole content of
;; the relation, so the preferred term must win *regardless* of how it sorts — this
;; test deliberately gives the preferred term the lexicographically **larger** name,
;; which is the tie-break `sameAs` would otherwise use.

(tu/deftest-kb rewrite-of-deprecates-its-second-argument-whatever-the-spelling
  (tu/with-terms [bornIn Chicago NameContext]
    (let [[lo hi] (sort [(tu/tmp-ind "Obama") (tu/tmp-ind "Obama")])]
      ;; the preferred term is `hi`, so lexicographic order cannot explain the outcome
      (v/assert kb (list bornIn lo Chicago) NameContext)
      (v/assert kb (list 'rewriteOf hi lo) NameContext)
      (testing "the fact is migrated to the preferred term"
        (is (believed? kb (list bornIn hi Chicago) NameContext)))
      (testing "and the deprecated spelling is blocked, not deleted"
        (is (stored-not-believed? kb (list bornIn lo Chicago) NameContext))))))

;; DECISION (Three assertable relations, one closure): "`sameAs` ... Both names stay
;; first-class; neither is deprecated; the representative is an internal detail" —
;; and the representative is then chosen by decision 2, the **lexicographically
;; smallest symbol**.  So the observable difference between `rewriteOf` and
;; `sameAs`/`equals` is exactly this: with the same two symbols and the same argument
;; order, `rewriteOf` elects its first argument and `sameAs` elects the smaller one.

(tu/deftest-kb same-as-states-no-preference-so-the-smaller-symbol-represents
  (tu/with-terms [bornIn Chicago NameContext]
    (let [[lo hi] (sort [(tu/tmp-ind "Obama") (tu/tmp-ind "Obama")])]
      (v/assert kb (list bornIn hi Chicago) NameContext)
      ;; written larger-first, so an implementation that trusted argument order would
      ;; elect `hi` and this test would catch it
      (v/assert kb (list 'sameAs hi lo) NameContext)
      (testing "the lexicographically smaller symbol represents the class"
        (is (believed? kb (list bornIn lo Chicago) NameContext)))
      (testing "so the fact written under the larger one is the blocked spelling"
        (is (stored-not-believed? kb (list bornIn hi Chicago) NameContext))))))

;; DECISION (Three assertable relations, one closure): "All three feed **one
;; equivalence closure**.  They differ in what they say *about* the members, not in
;; the classes they produce."  Each of the three, alone, must migrate.

(tu/deftest-kb all-three-relations-merge
  (doseq [rel ['rewriteOf 'sameAs 'equals]]
    (testing (str rel " merges its arguments")
      (tu/with-terms [bornIn Chicago NameContext]
        (let [[lo hi] (sort [(tu/tmp-ind "Ind") (tu/tmp-ind "Ind")])]
          ;; `lo` is both the preferred term of the rewrite and the lexicographic
          ;; winner, so all three relations must agree on it
          (v/assert kb (list bornIn hi Chicago) NameContext)
          (v/assert kb (list rel lo hi) NameContext)
          (is (believed? kb (list bornIn lo Chicago) NameContext)
              (str rel " did not migrate the fact to the representative"))
          (is (stored-not-believed? kb (list bornIn hi Chicago) NameContext)
              (str rel " did not block the non-representative spelling")))))))

;; DECISION (Choosing the representative): "Chains compose: `rewriteOf A B` and
;; `rewriteOf B C` make `A` the representative of all three."  The middle term is a
;; representative when the first edge is read alone, so a one-hop implementation
;; passes the A/B half and fails here.

(tu/deftest-kb a-rewrite-chain-composes-into-one-class-with-one-representative
  (tu/with-terms [bornIn Chicago Berlin NameContext]
    (tu/with-terms [A B C]
      (v/assert kb (list bornIn B Chicago) NameContext)
      (v/assert kb (list bornIn C Berlin)  NameContext)
      (v/assert kb (list 'rewriteOf A B) NameContext)
      (v/assert kb (list 'rewriteOf B C) NameContext)
      (testing "A represents all three, so both facts read under A"
        (is (believed? kb (list bornIn A Chicago) NameContext))
        (is (believed? kb (list bornIn A Berlin)  NameContext)))
      (testing "and neither of the two retired spellings is believed"
        (is (stored-not-believed? kb (list bornIn B Chicago) NameContext))
        (is (stored-not-believed? kb (list bornIn C Berlin)  NameContext)))
      (testing "B is deprecated too, so it does not represent C"
        (is (not (believed? kb (list bornIn B Berlin) NameContext)))))))

;; DECISION (Choosing the representative): "Order independence is non-negotiable
;; ..., so the choice can never depend on handle ids or arrival order — handles are
;; allocated in assertion order, and that was a real bug in the Nixon diamond."
;; Every ordering of the merge and the facts must produce the identical reading.  The
;; permutation harness is `order_independence_test`'s, on the isolated database pair
;; so the loop's clears cannot pull the scratch pair out from under this namespace.

(deftest the-representative-does-not-depend-on-assertion-order
  (tu/with-terms [bornIn worksAt Chicago Acme NameContext]
    (let [[lo hi] (sort [(tu/tmp-ind "Ind") (tu/tmp-ind "Ind")])
          ops     [#(v/assert % (list 'sameAs hi lo) NameContext)
                   #(v/assert % (list bornIn  hi Chicago) NameContext)
                   #(v/assert % (list worksAt lo Acme) NameContext)
                   #(v/assert % (list bornIn  lo Chicago) NameContext)]
          observe (fn [kb]
                    ;; the *reading*, never a handle: handles are allocated in
                    ;; assertion order, so one in the map would make every ordering
                    ;; differ for a reason that is not about belief
                    {:born-under-lo  (believed? kb (list bornIn  lo Chicago) NameContext)
                     :born-under-hi  (believed? kb (list bornIn  hi Chicago) NameContext)
                     :works-under-lo (believed? kb (list worksAt lo Acme)    NameContext)
                     :works-under-hi (believed? kb (list worksAt hi Acme)    NameContext)
                     :different      (v/ask? kb (list 'different lo hi) NameContext)})
          results (into #{} (map (fn [ordering]
                                   (let [k (tu/isolated-fresh)]
                                     (doseq [op ordering] (op k))
                                     (observe k))))
                        (permutations ops))]
      (is (= 1 (count results))
          (str "the representative moved with assertion order — "
               (count results) " distinct outcomes across 24 orderings: "
               (pr-str results)))
      (testing "and the one outcome elects the lexicographically smaller symbol"
        (let [r (first results)]
          (is (true?  (:born-under-lo  r)))
          (is (false? (:born-under-hi  r)))
          (is (true?  (:works-under-lo r)))
          (is (false? (:works-under-hi r)))
          (is (false? (:different r)) "merged terms are not different")))
      (tu/clear-kb! (tu/isolated-test-kb)))))

;; ---- 2. migration --------------------------------------------------------
;; DECISION (What a merge does — Migrate): "Each gets a rewritten twin under the
;; representative, **derived and justified** by `[the original sentex, the equality
;; sentex]`."  Derived, not re-asserted: the twin is not a premise, and its
;; justification names both parents.

(tu/deftest-kb the-migrated-twin-is-derived-and-justified-by-the-fact-and-the-equality
  (tu/with-terms [bornIn Chicago NameContext]
    (tu/with-terms [Pref Dep]
      (let [fact (v/assert kb (list bornIn Dep Chicago) NameContext)
            eq   (v/assert kb (list 'rewriteOf Pref Dep) NameContext)
            twin (v/handle-of kb (list bornIn Pref Chicago) NameContext)]
        (testing "the twin exists and is believed"
          (is (some? twin))
          (is (true? (v/in? kb twin))))
        (testing "it is derived, not asserted"
          (is (false? (v/premise? kb twin)))
          (is (seq (v/supporting-justifications kb twin))))
        (testing "and its justification names the original fact and the equality"
          (let [antes (set (mapcat :antecedents (v/supporting-justifications kb twin)))]
            (is (contains? antes fact) "the original sentex is not an antecedent")
            (is (contains? antes eq)   "the equality sentex is not an antecedent")))))))

;; DECISION (What a merge does — Block the original): "The stale spelling stays
;; stored but is not believed and does not match ...  Handles that callers already
;; hold stay valid."  Blocking, not sweeping: `exceptWhen` deletes an unsupported
;; conclusion, and this must **not**, because the premise is still the caller's.

(tu/deftest-kb the-stale-spelling-is-blocked-and-its-handle-stays-valid
  (tu/with-terms [bornIn Chicago NameContext]
    (tu/with-terms [Pref Dep]
      (let [h (v/assert kb (list bornIn Dep Chicago) NameContext)]
        (v/assert kb (list 'rewriteOf Pref Dep) NameContext)
        (testing "the handle the caller holds still resolves to its sentex"
          (is (some? (v/sentex kb h)))
          (is (= (list bornIn Dep Chicago) (:sentence (v/sentex kb h))))
          (is (= h (v/handle-of kb (list bornIn Dep Chicago) NameContext))))
        (testing "but it is not believed"
          (is (false? (v/in? kb h)))
          (is (false? (:believed? (v/why-not kb h)))))
        (testing "and it does not match — a raw level-2 lookup sees no believed hit"
          (is (empty? (v/lookup kb 2 (list bornIn Dep Chicago) NameContext))))))))

;; DECISION (What a merge does — Rewrite goals): "A query naming a non-representative
;; is rewritten before lookup, since its own sentexes are no longer believed."  So the
;; retired spelling is still a usable *question* even though it is not a usable
;; *answer* — which is what makes migration invisible to a caller who has not heard
;; about the merge.

(tu/deftest-kb a-goal-naming-the-deprecated-term-is-rewritten-and-still-answers
  (tu/with-terms [bornIn Chicago NameContext]
    (tu/with-terms [Pref Dep]
      (v/assert kb (list bornIn Dep Chicago) NameContext)
      (v/assert kb (list 'rewriteOf Pref Dep) NameContext)
      (testing "the closed goal answers under either spelling"
        (is (seq (v/sentexes-matching kb (list bornIn Pref Chicago) NameContext)))
        (is (seq (v/sentexes-matching kb (list bornIn Dep  Chicago) NameContext))
            "the goal was not rewritten to the representative before lookup")
        (is (true? (v/ask? kb (list bornIn Dep Chicago) NameContext))))
      (testing "and an open goal binds to the representative, not the retired name"
        (is (= #{Pref} (set (map #(get % '?who)
                                 (v/ask kb (list bornIn '?who Chicago) NameContext)))))))))

;; DECISION (What a merge does — Migrate): "Dedup falls out: when the rewritten form
;; already exists, find-or-create returns that handle and it simply gains a second
;; justification."  One handle with two supports, never two handles — this is the
;; claim that makes a merge idempotent against content the KB already had.

(tu/deftest-kb merging-two-spellings-of-one-fact-yields-one-handle-with-two-supports
  (tu/with-terms [bornIn Chicago NameContext]
    (tu/with-terms [Pref Dep]
      (let [pref-h (v/assert kb (list bornIn Pref Chicago) NameContext)
            _      (v/assert kb (list bornIn Dep  Chicago) NameContext)
            before (count (v/supporting-justifications kb pref-h))]
        (v/assert kb (list 'rewriteOf Pref Dep) NameContext)
        (testing "the representative's handle is unchanged"
          (is (= pref-h (v/handle-of kb (list bornIn Pref Chicago) NameContext))))
        (testing "it is still the premise the caller asserted"
          (is (true? (v/premise? kb pref-h)))
          (is (true? (v/in? kb pref-h))))
        (testing "and it gained a justification rather than spawning a second sentex"
          (is (> (count (v/supporting-justifications kb pref-h)) before)))
        (testing "exactly one believed sentex carries the predicate"
          (is (= 1 (count (v/sentexes-with-functor kb bornIn {:believed? true})))))))))

;; ---- 3. congruence -------------------------------------------------------
;; DECISION (Congruence comes free): "The inverted term index locates a term at **any
;; nesting depth**, and migration rewrites it there, so merging performs congruence
;; closure eagerly over all ground content."  The doc claims this falls out; nothing
;; else in the suite would notice if it did not, because every other test puts the
;; merged term in top-level argument position.

(tu/deftest-kb a-merged-term-nested-inside-a-compound-is-rewritten-too
  (tu/with-terms [reportedThat livesIn Ann Bob StoryContext]
    (tu/with-terms [Pref Dep]
      ;; Dep occurs only at depth 2 — never as an argument of the stored literal
      (v/assert kb (list reportedThat Ann (list livesIn Bob Dep)) StoryContext)
      (v/assert kb (list 'rewriteOf Pref Dep) StoryContext)
      (testing "the nested occurrence is rewritten, so the congruent twin exists"
        (is (believed? kb (list reportedThat Ann (list livesIn Bob Pref)) StoryContext)))
      (testing "and the nested stale spelling is blocked like a flat one"
        (is (stored-not-believed? kb (list reportedThat Ann (list livesIn Bob Dep))
                                  StoryContext))))))

;; DECISION (Interactions — Symmetric predicates): "Argument sorting for a symmetric
;; predicate is done at canonicalization time against the *stored* symbols.  A later
;; merge changes what the sorted order should be, so migration must re-canonicalize
;; rather than substitute textually."  A textual substitution leaves the twin's stored
;; sentence out of canonical order, which `handle-of` would hide (it probes both
;; orders), so the *stored sentence* is read directly.

(tu/deftest-kb migration-re-canonicalizes-a-symmetric-literal-rather-than-substituting
  (tu/with-terms [siblingOf KinContext]
    (let [[lo mid hi] (sort [(tu/tmp-ind "Ind") (tu/tmp-ind "Ind") (tu/tmp-ind "Ind")])]
      (v/assert kb (list 'symmetric siblingOf) KinContext)
      ;; stored canonically as (siblingOf lo mid)
      (v/assert kb (list siblingOf mid lo) KinContext)
      ;; retire `lo` in favour of `hi`, which sorts *after* mid
      (v/assert kb (list 'rewriteOf hi lo) KinContext)
      (let [twin (v/handle-of kb (list siblingOf mid hi) KinContext)]
        (testing "the twin exists"
          (is (some? twin)))
        (testing "and its stored sentence is re-canonicalized, not textually rewritten"
          (is (= (list siblingOf mid hi) (:sentence (v/sentex kb twin)))
              "the merge substituted textually and left (siblingOf hi mid) stored"))))))

;; ---- 4. retraction -------------------------------------------------------
;; DECISION (What a merge does): "Retraction needs no new code.  Dropping the equality
;; invalidates the derivations, the dependency-directed sweep collects the twins, and
;; unblocking revives the originals."  Both halves matter: a sweep that left the twin
;; stored would make the term count wrong, and an unblock that did not happen would
;; lose the caller's own premise.

(tu/deftest-kb retracting-the-equality-sweeps-the-twins-and-revives-the-originals
  (tu/with-terms [bornIn worksAt Chicago Acme NameContext]
    (tu/with-terms [Pref Dep]
      (let [f1 (v/assert kb (list bornIn  Dep Chicago) NameContext)
            f2 (v/assert kb (list worksAt Dep Acme)    NameContext)
            eq (v/assert kb (list 'rewriteOf Pref Dep) NameContext)]
        (testing "both twins exist while the equality holds"
          (is (believed? kb (list bornIn  Pref Chicago) NameContext))
          (is (believed? kb (list worksAt Pref Acme)    NameContext)))
        (v/retract! kb eq)
        (testing "the twins are swept — collected, not merely disbelieved"
          (is (nil? (v/handle-of kb (list bornIn  Pref Chicago) NameContext)))
          (is (nil? (v/handle-of kb (list worksAt Pref Acme)    NameContext))))
        (testing "and the originals are unblocked"
          (is (true? (v/in? kb f1)))
          (is (true? (v/in? kb f2)))
          (is (seq (v/sentexes-matching kb (list bornIn Dep Chicago) NameContext))))
        (testing "so the two symbols are different again"
          (is (true? (v/ask? kb (list 'different Pref Dep) NameContext))))))))

;; ---- 5. `different` ------------------------------------------------------
;; DECISION (The unique-name assumption survives): "`(different X Y)` is **provable
;; exactly when the arguments lie in no shared equivalence class** — so distinct
;; symbols denote distinct individuals until an equality sentex says otherwise."
;; All three phases in one test, because the interesting claim is the transition and
;; not any single reading.

(tu/deftest-kb different-tracks-the-closure-in-both-directions
  (tu/with-terms [NameContext]
    (tu/with-terms [Pref Dep]
      (testing "two unmerged symbols are different by the unique-name assumption"
        (is (true? (v/ask? kb (list 'different Pref Dep) NameContext))))
      (let [eq (v/assert kb (list 'sameAs Pref Dep) NameContext)]
        (testing "once merged they are not"
          (is (false? (v/ask? kb (list 'different Pref Dep) NameContext))))
        (v/retract! kb eq)
        (testing "and retracting the merge restores the difference — the closure split"
          (is (true? (v/ask? kb (list 'different Pref Dep) NameContext))))))))

;; DECISION (The unique-name assumption survives): "**Variable arity.**  `(different
;; A B C)` asserts the arguments are pairwise distinct."  Pairwise, so merging *any*
;; one pair must take the whole literal down — a check that only tested the first pair
;; would pass on a two-argument test and fail here.

(tu/deftest-kb different-is-variable-arity-and-pairwise
  (tu/with-terms [NameContext]
    (tu/with-terms [A B C]
      (testing "three pairwise-distinct symbols"
        (is (true? (v/ask? kb (list 'different A B C) NameContext))))
      ;; merge the pair that is *not* first, so a first-pair-only check is caught
      (v/assert kb (list 'sameAs B C) NameContext)
      (testing "merging any one pair falsifies the whole literal"
        (is (false? (v/ask? kb (list 'different A B C) NameContext))))
      (testing "while the untouched pair is still different"
        (is (true? (v/ask? kb (list 'different A B) NameContext)))))))

;; DECISION (The unique-name assumption survives): "**Not assertible.**  It is
;; answered by a prover and never stored.  Asserting it is rejected.  (An assertible
;; `different` would be OWL's `differentFrom` — a positive commitment that makes a
;; later `sameAs` contradictory.  Deliberately not built.)"

(tu/deftest-kb different-is-not-assertible
  (tu/with-terms [NameContext]
    (tu/with-terms [A B]
      (testing "asserting it is rejected"
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/assert kb (list 'different A B) NameContext))))
      (testing "and the refusal stores nothing"
        (is (nil? (v/handle-of kb (list 'different A B) NameContext)))
        (is (zero? (v/count-with-functor kb 'different)))
        (is (empty? (v/find-sentexes kb 'different)))))))

;; DECISION (The unique-name assumption survives): "**Ground only.**  The prover is
;; inapplicable unless every argument is bound.  `(different ?x Y)` would enumerate
;; every term in the KB that is not `Y`, so it is refused rather than answered
;; explosively."
;;
;; SPEC NOTE — "refused" is not pinned to a mechanism by the doc.  Since `different`
;; is a **prover**, and a prover declares `applicable?`, the reading taken here is
;; that an open goal makes it inapplicable, so `ask` yields nothing and the goal drops
;; out of `query-plan` (which lists applicable provers only).  The alternative reading
;; — throwing on an open `different` — would fail this test, which is the point: the
;; doc should say which.  The claim both readings share, and the one that actually
;; matters, is that nothing enumerates.

(tu/deftest-kb an-open-different-is-refused-rather-than-enumerated
  (tu/with-terms [bornIn Chicago NameContext]
    (tu/with-terms [A B C]
      (doseq [x [A B C]] (v/assert kb (list bornIn x Chicago) NameContext))
      (testing "the ground goal is claimed by some prover — the control"
        (is (seq (v/query-plan kb (list 'different A B) NameContext))))
      (testing "an unbound argument makes that prover inapplicable"
        ;; named by count rather than by class, since the doc names no prover
        (is (< (count (v/query-plan kb (list 'different '?x B) NameContext))
               (count (v/query-plan kb (list 'different A   B) NameContext)))
            "a prover claimed an open `different` goal"))
      (testing "and nothing enumerated the KB looking for non-B terms"
        (is (empty? (v/ask kb (list 'different '?x B)  NameContext)))
        (is (empty? (v/ask kb (list 'different '?x '?y) NameContext)))))))

;; DECISION (The unique-name assumption survives): "**Not canonicalized.**  No chain
;; merging ...  `lessThan` merges chains because it is **transitive** ... `different`
;; is **not** transitive — `A≠B` and `B≠C` say nothing about `A` and `C` — so
;; chain-merging it would manufacture a claim nobody made."
;;
;; `different` is never stored, so the only place a chain merge could happen is a rule
;; antecedent, where the literal *is* stored as part of the rule sentex.  That is what
;; is read back here: two `different` literals sharing a variable must survive
;; canonicalization as two literals, not collapse the way `(lessThan ?a ?b)` +
;; `(lessThan ?b ?c)` does.

(tu/deftest-kb a-different-chain-in-a-rule-antecedent-is-not-merged
  (tu/with-terms [triple item StoryContext]
    (let [rh (v/assert-rule kb [(list item '?a) (list item '?b) (list item '?c)
                                (list 'different '?a '?b)
                                (list 'different '?b '?c)]
                            (list triple '?a '?b '?c)
                            StoryContext)
          antes (:antecedent (v/sentex kb rh))
          diffs (filter #(= 'different (first %)) antes)]
      (testing "both literals survive — no chain merge"
        (is (= 2 (count diffs))
            (str "the two `different` literals were merged into "
                 (pr-str diffs) " — `different` is not transitive")))
      (testing "and neither grew an argument"
        (is (every? #(= 3 (count %)) diffs)))
      (testing "the rule fires for a binding the merged form would have rejected"
        ;; a=c is allowed: the rule constrains a≠b and b≠c and says nothing about a,c
        (tu/with-terms [X Y]
          (v/assert kb (list item X) StoryContext)
          (v/assert kb (list item Y) StoryContext)
          (is (seq (v/sentexes-matching kb (list triple X Y X) StoryContext))
              "a merged (different ?a ?b ?c) would have blocked a = c")))
      (testing "and a rule assert does not store a `different` fact"
        (is (zero? (v/count-with-functor kb 'different)))))))

;; DECISION (Interactions — Stratification): "`different` in a rule antecedent is a
;; **negative dependency**, so it joins the rule dependency graph beside `exceptWhen`.
;; A rule concluding an equality from a `different` antecedent is a cycle through
;; negation and is rejected — otherwise belief would depend on arrival order."

(tu/deftest-kb a-rule-concluding-an-equality-from-a-different-antecedent-is-rejected
  (tu/with-terms [candidate MergeContext]
    (tu/with-terms [Anchor]
      (testing "the one-rule cycle through negation is refused at assert time"
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/assert-rule kb [(list candidate '?x)
                                        (list 'different '?x Anchor)]
                                    (list 'sameAs '?x Anchor)
                                    MergeContext))))
      (testing "and the refusal leaves no rule behind"
        (is (empty? (v/sentexes-in-context kb MergeContext)))))))

;; ---- 6. `functional` -----------------------------------------------------
;; DECISION (`functional` infers equality instead of throwing): "`(functional P)` plus
;; two different values for the same first argument currently throws.  It will instead
;; **derive** an equality between the values."  Not throwing is half the claim; the
;; merge actually happening is the other half.
;;
;; SPEC NOTE — the doc says "an equality" without naming which of the three relations
;; is derived.  `equals` is this suite's choice (the values of a functional role are
;; any terms, not necessarily individuals, which is exactly `equals`'s remit).  The
;; assertions about *merging* are spelling-independent and stand whichever is chosen;
;; only the `derived-equality-exists` assertion below depends on it.
;;
;; Until this lands, the second `(motherOf Tom ...)` assert **throws** — that is the
;; behaviour under specification, so these three tests report as ERROR rather than
;; FAIL, and the two below never reach their assertions at all.

(tu/deftest-kb functional-derives-an-equality-instead-of-throwing
  (tu/with-terms [motherOf caresFor Tom FamContext]
    (let [[lo hi] (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])]
      (v/assert kb (list 'functional motherOf) FamContext)
      (v/assert kb (list motherOf Tom lo) FamContext)
      (testing "the second value does not throw"
        (is (some? (v/assert kb (list motherOf Tom hi) FamContext))))
      (testing "the two values are merged, so they are no longer different"
        (is (false? (v/ask? kb (list 'different lo hi) FamContext))))
      (testing "and a fact about either reads under the representative"
        (v/assert kb (list caresFor hi Tom) FamContext)
        (is (believed? kb (list caresFor lo Tom) FamContext)))
      (testing "the derived equality is itself a sentex"
        (is (some? (v/handle-of kb (list 'equals lo hi) FamContext)))))))

;; DECISION (`functional` infers equality instead of throwing): "Making it a real
;; justification rather than a side effect is what makes it safe ... the merge is
;; justified, `why` names exactly which declaration and which two facts caused it."
;; A silent merge would be the dangerous version of this feature, so the *inspectable*
;; half is pinned separately from the *reversible* half below.

(tu/deftest-kb why-on-a-functional-merge-names-the-declaration-and-both-facts
  (tu/with-terms [motherOf Tom FamContext]
    (let [[lo hi] (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])]
      (v/assert kb (list 'functional motherOf) FamContext)
      (v/assert kb (list motherOf Tom lo) FamContext)
      (v/assert kb (list motherOf Tom hi) FamContext)
      (let [eq (v/handle-of kb (list 'equals lo hi) FamContext)]
        (is (some? eq) "no derived equality to explain")
        (let [tree (v/why kb eq)
              said (set (why-sentences tree))]
          (testing "it is derived, not a premise"
            (is (true?  (:believed? tree)))
            (is (false? (:premise?  tree)))
            (is (seq (:support tree))))
          (testing "and the argument names the declaration and both facts"
            (is (contains? said (list 'functional motherOf))
                "why does not name the functional declaration that caused the merge")
            (is (contains? said (list motherOf Tom lo)))
            (is (contains? said (list motherOf Tom hi)))))))))

;; DECISION (`functional` infers equality instead of throwing): "retracting any one of
;; them runs the existing sweep and un-merges.  An opaque merge would be dangerous; an
;; inspectable, reversible one is knowledge."

(tu/deftest-kb retracting-either-functional-fact-un-merges-the-values
  (tu/with-terms [motherOf caresFor Tom FamContext]
    (let [[lo hi] (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])]
      (v/assert kb (list 'functional motherOf) FamContext)
      (v/assert kb (list motherOf Tom lo) FamContext)
      (let [second-fact (v/assert kb (list motherOf Tom hi) FamContext)]
        (v/assert kb (list caresFor hi Tom) FamContext)
        (testing "merged while both facts stand"
          (is (false? (v/ask? kb (list 'different lo hi) FamContext)))
          (is (believed? kb (list caresFor lo Tom) FamContext)))
        (v/retract! kb second-fact)
        (testing "retracting one of them un-merges"
          (is (true? (v/ask? kb (list 'different lo hi) FamContext)))
          (is (nil?  (v/handle-of kb (list 'equals lo hi) FamContext))))
        (testing "and the migrated twin is swept while the original revives"
          (is (nil? (v/handle-of kb (list caresFor lo Tom) FamContext)))
          (is (true? (believed? kb (list caresFor hi Tom) FamContext))))))))

;; DECISION (`functional` infers equality instead of throwing) meeting order
;; independence: a declaration has to reach the facts already stored exactly as it
;; reaches the facts that follow — the both-directions rule `entail-existing` states
;; for the argument constraints, and the same rule here.  The three tests above all
;; write the declaration first, which is the direction that was never the question:
;; the values a functional slot already holds are co-referent whether the KB is told
;; the predicate is functional before it is told the facts or after, and if it is not,
;; then whether two names denote one woman depends on which line of a file arrived
;; first.

(tu/deftest-kb a-functional-declaration-arriving-after-the-facts-merges-them-too
  (tu/with-terms [motherOf caresFor Tom FamContext]
    (let [[lo hi] (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])]
      (v/assert kb (list motherOf Tom lo) FamContext)
      (v/assert kb (list motherOf Tom hi) FamContext)
      (testing "before the declaration the two values are simply two values"
        (is (true? (v/ask? kb (list 'different lo hi) FamContext))))
      (v/assert kb (list 'functional motherOf) FamContext)
      (testing "the declaration merges what it now says was always one thing"
        (is (false? (v/ask? kb (list 'different lo hi) FamContext))))
      (testing "the derived equality is a sentex here too"
        (is (some? (v/handle-of kb (list 'equals lo hi) FamContext))))
      (testing "and a fact about either reads under the representative"
        (v/assert kb (list caresFor hi Tom) FamContext)
        (is (believed? kb (list caresFor lo Tom) FamContext))))))

(tu/deftest-kb the-functional-declaration-reaches-the-same-belief-from-either-end
  ;; the oracle for the test above: the same three sentences in the two orders that
  ;; matter, compared on what the KB *believes* rather than on what it stored
  (tu/with-terms [motherOf Tom FamContext]
    (let [[lo hi] (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])
          decl (list 'functional motherOf)
          f1   (list motherOf Tom lo)
          f2   (list motherOf Tom hi)
          reading (fn [] [(v/ask? kb (list 'different lo hi) FamContext)
                          (v/representative kb lo)
                          (v/representative kb hi)
                          (some? (v/handle-of kb (list 'equals lo hi) FamContext))])]
      (doseq [s [decl f1 f2]] (v/assert kb s FamContext))
      (let [declaration-first (reading)]
        (doseq [s [decl f1 f2]]
          (when-let [h (v/handle-of kb s FamContext)] (v/retract! kb h)))
        (doseq [s [f2 f1 decl]] (v/assert kb s FamContext))
        (is (= declaration-first (reading))
            "the same three sentences believe different things in the two orders")))))

(tu/deftest-kb a-retroactive-functional-merge-carries-the-same-argument
  ;; the merge is knowledge only if it is inspectable, and a retroactive one names the
  ;; same three sentexes a forward one does — otherwise `why` would explain one arrival
  ;; order and shrug at the other
  (tu/with-terms [motherOf Tom FamContext]
    (let [[lo hi] (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])]
      (v/assert kb (list motherOf Tom lo) FamContext)
      (v/assert kb (list motherOf Tom hi) FamContext)
      (v/assert kb (list 'functional motherOf) FamContext)
      (let [eq (v/handle-of kb (list 'equals lo hi) FamContext)]
        (is (some? eq) "no derived equality to explain")
        (let [said (set (why-sentences (v/why kb eq)))]
          (is (contains? said (list 'functional motherOf)))
          (is (contains? said (list motherOf Tom lo)))
          (is (contains? said (list motherOf Tom hi))))))))

(tu/deftest-kb retracting-a-retroactive-functional-declaration-un-merges
  ;; reversibility is the other half of "inspectable, reversible", and the declaration
  ;; is one of the three antecedents whichever order it arrived in
  (tu/with-terms [motherOf caresFor Tom FamContext]
    (let [[lo hi] (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])]
      (v/assert kb (list motherOf Tom lo) FamContext)
      (v/assert kb (list motherOf Tom hi) FamContext)
      (v/assert kb (list 'functional motherOf) FamContext)
      (v/assert kb (list caresFor hi Tom) FamContext)
      (testing "merged while the declaration stands"
        (is (false? (v/ask? kb (list 'different lo hi) FamContext)))
        (is (believed? kb (list caresFor lo Tom) FamContext)))
      (v/retract! kb (v/handle-of kb (list 'functional motherOf) FamContext))
      (testing "retracting the declaration un-merges the values it merged"
        (is (true? (v/ask? kb (list 'different lo hi) FamContext)))
        (is (nil?  (v/handle-of kb (list 'equals lo hi) FamContext))))
      (testing "and the migrated twin goes with it"
        (is (nil? (v/handle-of kb (list caresFor lo Tom) FamContext)))
        (is (true? (believed? kb (list caresFor hi Tom) FamContext)))))))

(tu/deftest-kb a-retroactive-declaration-collapses-a-whole-slot-not-one-pair
  ;; three spellings of one mother: the sweep is over the predicate's extent, so every
  ;; value in the slot lands in one class rather than the first pair it happens to meet
  (tu/with-terms [motherOf Tom FamContext]
    (let [[a b c] (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])]
      (doseq [m [a b c]] (v/assert kb (list motherOf Tom m) FamContext))
      (v/assert kb (list 'functional motherOf) FamContext)
      (testing "all three collapse to one representative"
        (is (= 1 (count (distinct (map #(v/representative kb %) [a b c]))))
            (str "three values did not reach one class: "
                 (pr-str (mapv #(v/representative kb %) [a b c]))))))))

;; ---- 7. disjointness -----------------------------------------------------
;; DECISION (Interactions — Disjointness): "A merge can *create* a violation:
;; `(dog Rex)` + `(cat Fluffy)` + merge makes one individual both.  So migration runs
;; the integrity checks that `place-conclusion` already runs, and a derived violation
;; is reported through `violations` rather than thrown."  Reported, not thrown: the
;; merge is a derivation, and a derivation that aborted would make belief depend on
;; firing order.

(tu/deftest-kb a-merge-that-creates-a-disjointness-violation-is-reported-not-thrown
  (tu/with-terms [dog cat PetContext]
    (tu/with-terms [Rex Fluffy]
      (v/assert kb (list 'disjoint dog cat) PetContext)
      (v/assert kb (list dog Rex)    PetContext)
      (v/assert kb (list cat Fluffy) PetContext)
      (testing "the merge itself does not throw"
        (is (some? (v/assert kb (list 'sameAs Rex Fluffy) PetContext))))
      (let [vs (v/violations kb)]
        (testing "the impossible twin is reported as a disjointness violation"
          (is (seq vs))
          (is (some #(= :disjoint (:violation %)) vs)
              (str "no :disjoint violation reported — got " (pr-str (map :violation vs))))))
      (testing "and the impossible twin was dropped, not stored"
        (let [rep (first (sort [Rex Fluffy]))
              other (if (= rep Rex) cat dog)]
          (is (nil? (v/handle-of kb (list other rep) PetContext))))))))

;; ---- 8. well-formedness --------------------------------------------------
;; DECISION (Choosing the representative): "A `rewriteOf` cycle has no representative
;; and is rejected by `wff`, like a `genl` cycle."  Both the two-edge cycle and the
;; longer one, because a check that only compared the two arguments of the edge being
;; asserted would pass the first and miss the second.

(tu/deftest-kb a-rewrite-of-cycle-is-rejected
  (tu/with-terms [NameContext]
    (tu/with-terms [A B C]
      (testing "the two-edge cycle"
        (v/assert kb (list 'rewriteOf A B) NameContext)
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/assert kb (list 'rewriteOf B A) NameContext))))
      (testing "the three-edge cycle, which a pairwise check would miss"
        (v/assert kb (list 'rewriteOf B C) NameContext)
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/assert kb (list 'rewriteOf C A) NameContext))))
      (testing "and a refused edge leaves nothing stored"
        (is (nil? (v/handle-of kb (list 'rewriteOf B A) NameContext)))
        (is (nil? (v/handle-of kb (list 'rewriteOf C A) NameContext)))))))

;; DECISION (Choosing the representative): a self-edge is the degenerate cycle, and it
;; is the one an import pipeline actually produces (the same term aligned to itself).

(tu/deftest-kb a-rewrite-of-self-edge-is-rejected
  (tu/with-terms [NameContext]
    (tu/with-terms [A]
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list 'rewriteOf A A) NameContext)))
      (is (nil? (v/handle-of kb (list 'rewriteOf A A) NameContext))))))

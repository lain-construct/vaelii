;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.relation-properties-test
  "The four relation properties added in #14, enforced rather than declared:

  * **`irreflexive`** — a self tuple `(P a a)` is refused at the entry point, the strict
    counterpart of `reflexive` and stronger than `asymmetric` (which admits it).
  * **`anti_symmetric`** — a believed converse `(P b a)` merges the two arguments,
    deriving `(equals a b)`, the antisymmetric twin of what `functional` does with two
    symbol values.
  * **`anti_transitive`** — the two-step chain and the direct step are convicted
    **together**, as the one nogood whose members are three rather than two
    (docs/nmtms.md).  Its classification and `(disjoint transitive anti_transitive)` are
    enforced beside that.
  * **`equivalence_relation`** — no engine code: three CxCore forward rules derive
    `symmetric`, `transitive` and `reflexive`, each enforced in turn.

  A CxCore-loaded KB on the collapsed single-predicate model (an algebraic property is one
  predicate, not a mark and a twin): each new property is one predicate with `(genl X
  binary_predicate)`, and the lattice sits on the bare marks — so the SHIPPED declarations
  are what is tested, not a hand-built fixture that could drift from the file."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh #(doto (tu/fresh) (tu/load-core!))))

(defn- ex-type
  "The `:type` on the ex-info a thunk throws, or nil if it does not throw."
  [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))

(def U 'CxUniverse)

(defn- orderings
  "Every arrival order of `xs`, so a multi-order case runs over all of them rather than
  over a hand-picked few."
  [xs]
  (if (< (count xs) 2)
    [(vec xs)]
    (for [x xs, tail (orderings (remove #{x} xs))]
      (into [x] tail))))

(defn- reach-entries
  "The `:detail` of each entry of kind `kind` that the late-mark report
  (`settle/report-unarbitrable-reach!`) filed through marked predicate `via`."
  [kb kind via]
  (into [] (comp (filter #(and (= kind (:violation %)) (= via (get-in % [:detail :via]))))
                 (map :detail))
        (v/violations kb)))

(defn- refused-or-reported
  "Run `steps` (a map of thunks) in `order`, then say whether the fact `ask` reads was
  refused, or is stored and named by a `kind` entry through `via` — the property a
  late mark owes in every arrival order."
  [kb order steps ask kind via]
  (let [refused (atom false)]
    (doseq [s order]
      (when (#{:irreflexive :anti-symmetric} (ex-type (steps s)))
        (reset! refused true)))
    (let [stored? (ask)]
      {:refused? @refused
       :stored?  stored?
       :ok?      (if stored?
                   (= 1 (count (reach-entries kb kind via)))
                   @refused)})))

;;; ── irreflexive: a self tuple is refused at the entry point ──────────────────

(tu/deftest-kb an-irreflexive-self-tuple-is-refused
  (tu/with-terms [before Alice]
    (v/assert kb (list 'irreflexive before) U)
    (testing "check predicts the refusal, and assert throws it"
      (is (= [:irreflexive] (mapv :type (v/check kb (list before Alice Alice) U))))
      (is (= :irreflexive (ex-type #(v/assert kb (list before Alice Alice) U)))))
    (testing "nothing was stored"
      (is (nil? (v/handle-of kb (list before Alice Alice) U)))
      (is (not (v/ask? kb (list before Alice Alice) U))))
    (testing "an ordinary non-self tuple of the same predicate is admitted"
      (tu/with-terms [Bob]
        (is (v/assert kb (list before Alice Bob) U))))))

(tu/deftest-kb an-irreflexive-refusal-holds-in-both-declaration-orders
  ;; The declaration-then-tuple order refuses at the entry point; the tuple-then-declaration
  ;; order is the arity case, not the asymmetric one — a lone self tuple names no second
  ;; sentex to defeat, so the stored tuple stands and the late mark reports rather than
  ;; retracts (docs/nmtms.md).  Both orders agree that a *new* self tuple is refused.
  (tu/with-terms [before Alice]
    (v/assert kb (list 'irreflexive before) U)
    (is (= :irreflexive (ex-type #(v/assert kb (list before Alice Alice) U))))
    (testing "and a fresh predicate declared the other way round refuses the same"
      (tu/with-terms [ahead Carol]
        (v/assert kb (list ahead Carol Carol) U)      ; tuple first — admitted
        (v/assert kb (list 'irreflexive ahead) U)      ; late mark
        (testing "a NEW self tuple is refused once the mark is present"
          (is (= :irreflexive (ex-type #(v/assert kb (list ahead 'CarolTwin 'CarolTwin) U)))))))))

(tu/deftest-kb retracting-the-irreflexive-declaration-lifts-the-refusal
  (tu/with-terms [before Alice]
    (let [decl (v/assert kb (list 'irreflexive before) U)]
      (is (= :irreflexive (ex-type #(v/assert kb (list before Alice Alice) U))))
      (v/retract! kb decl)
      (testing "with the mark gone the self tuple is admitted"
        (is (v/assert kb (list before Alice Alice) U))
        (is (v/ask? kb (list before Alice Alice) U))))))

(tu/deftest-kb irreflexive-refuses-under-both-constraint-policies
  ;; A lone self tuple is not arbitrable — there is no pair — so it refuses whatever the
  ;; policy says, exactly as a clash against known-true content does.  This is the
  ;; `asymmetric-is-not-policy-dependent-at-all` shape one property over.
  (tu/with-terms [before Alice]
    (v/assert kb (list 'irreflexive before) U)
    (doseq [arbitrate? [false true]]
      (binding [checks/*arbitrate-constraints?* arbitrate?]
        (testing (str "arbitrate=" arbitrate?)
          (is (= :irreflexive (ex-type #(v/assert kb (list before Alice Alice) U))))
          (is (empty? (v/contradictions kb))))))))

;;; ── a late irreflexive mark reports the self tuple it reaches ──────────
;;
;; A self tuple names no second sentex, so the conviction is not arbitrable: the entry
;; point refuses it under either policy, and a tuple stored before the mark reached it
;; stands.  The late mark then files a report rather than a nogood — the `arity` reading
;; (docs/nmtms.md) — so no arrival order leaves a convicted tuple nobody was told about.

(tu/deftest-kb a-late-irreflexive-mark-reports-the-self-tuple-it-arrives-over
  (testing "the mark first: the tuple is refused, and nothing is stored to report"
    (tu/with-terms [near Dora]
      (v/assert kb (list 'irreflexive near) U)
      (is (= :irreflexive (ex-type #(v/assert kb (list near Dora Dora) U))))
      (is (empty? (reach-entries kb :irreflexive near)))))
  (testing "the tuple first: it stands, and the late mark reports it"
    (tu/with-terms [near Dora]
      (v/assert kb (list near Dora Dora) U)
      (is (empty? (reach-entries kb :irreflexive near)) "no mark yet, nothing is wrong")
      (v/assert kb (list 'irreflexive near) U)
      (is (v/ask? kb (list near Dora Dora) U) "reported, not withdrawn")
      (let [[e & more] (reach-entries kb :irreflexive near)]
        (is (some? e) "the late mark files the report")
        (is (nil? more) "one entry for the mark")
        (is (= 1 (:count e)))
        (is (= [(list near Dora Dora)] (:sample e)))))))

(tu/deftest-kb a-self-tuple-under-a-descended-irreflexive-mark-is-refused-or-reported
  ;; The mark on `near`, the tuple of `nearish` beneath it, and the edge between them:
  ;; any of the three can arrive last, and the edge arriving last is a trigger of its own.
  (doseq [order (orderings [:mark :edge :tuple])]
    (tu/with-terms [near nearish Dora]
      (let [r (refused-or-reported
               kb order
               {:mark  #(v/assert kb (list 'irreflexive near) U)
                :edge  #(v/assert kb (list 'genl nearish near) U)
                :tuple #(v/assert kb (list nearish Dora Dora) U)}
               #(v/ask? kb (list nearish Dora Dora) U)
               :irreflexive near)]
        (is (:ok? r) (str "refused, or stored and reported once, under " (pr-str order)
                          ": " (pr-str r)))
        (is (= (:refused? r) (= :tuple (last order)))
            (str "refused exactly when the tuple arrives last, under " (pr-str order)))))))

(tu/deftest-kb a-self-tuple-across-a-context-edge-is-refused-or-reported
  ;; The fourth ingredient names no predicate: the mark in `CxUp`, the tuple in `CxDown`,
  ;; and the `genlCx` edge that lets the tuple's context see the mark.
  (doseq [order (orderings [:mark :ctx-edge :tuple])]
    (tu/with-terms [CxUp CxDown near Dora]
      (v/assert kb (list 'genlCx CxUp U) U)
      (let [r (refused-or-reported
               kb order
               {:mark     #(v/assert kb (list 'irreflexive near) CxUp)
                :ctx-edge #(v/assert kb (list 'genlCx CxDown CxUp) U)
                :tuple    #(v/assert kb (list near Dora Dora) CxDown)}
               #(v/ask? kb (list near Dora Dora) CxDown)
               :irreflexive near)]
        (is (:ok? r) (str "refused, or stored and reported once, under " (pr-str order)
                          ": " (pr-str r)))
        (is (= (:refused? r) (= :tuple (last order)))
            (str "refused exactly when the tuple arrives last, under " (pr-str order)))))))

(tu/deftest-kb a-budget-spent-on-innocent-facts-still-says-the-reach-was-cut
  ;; `aaa…` spends the budget and convicts nothing; `zzz…` sorts after it, holds the self
  ;; tuple, and is swept zero facts deep.  With no finding for a flag to ride on, the
  ;; truncation entry is the only thing that says a predicate went unswept.
  (binding [tax/*exposure-instance-budget* 4]
    (tu/with-terms [near Dora]
      (let [aaa (symbol (str "aaa" (name near)))
            zzz (symbol (str "zzz" (name near)))]
        (dotimes [i 5]
          (v/assert kb (list aaa Dora (symbol (str "TmpBud" i))) U))
        (v/assert kb (list zzz Dora Dora) U)
        (v/assert kb (list 'genl aaa near) U)
        (v/assert kb (list 'genl zzz near) U)
        (v/assert kb (list 'irreflexive near) U)
        (is (v/ask? kb (list zzz Dora Dora) U) "the self tuple stands, as it did before")
        (is (empty? (reach-entries kb :irreflexive near))
            "the premise: the budget ran out before the tuple was examined")
        (let [t (last (filter #(= :unarbitrable-reach-truncated (:violation %))
                              (v/violations kb)))]
          (is (some? t) "and the pass says a predicate went unswept rather than nothing")
          (is (= [aaa zzz] (get-in t [:detail :sample]))
              "naming the one that spent the budget and the one that got none")
          (is (= 4 (get-in t [:detail :budget])))
          (is (re-find #"went unswept" (get-in t [:detail :message]))))))))

(tu/deftest-kb a-revived-mark-reports-again-and-a-revived-tuple-does-not
  ;; the ledger is cleared before each revival, so an entry after it is filed by it
  (testing "the mark revives: it is in the moved region and reports as an arriving one"
    (tu/with-terms [near Dora]
      (v/assert kb (list near Dora Dora) U)
      (v/assert kb (list 'irreflexive near) U)
      (let [d (v/assert kb (list 'not (list 'irreflexive near)) U {:strength :monotonic})]
        (v/clear-violations! kb)
        (v/retract! kb d)
        (is (v/ask? kb (list 'irreflexive near) U))
        (is (= 1 (count (reach-entries kb :irreflexive near)))))))
  (testing "the tuple revives under the standing mark: the pass reads no plain fact"
    (tu/with-terms [near Dora]
      (v/assert kb (list near Dora Dora) U)
      (v/assert kb (list 'irreflexive near) U)
      (let [d (v/assert kb (list 'not (list near Dora Dora)) U {:strength :monotonic})]
        (v/clear-violations! kb)
        (v/retract! kb d)
        (is (v/ask? kb (list near Dora Dora) U))
        (is (empty? (reach-entries kb :irreflexive near)))))))

;;; ── anti_symmetric: a believed converse merges the two arguments ───────

(defn- merged?
  "Is the antisymmetric-derived `(equals a b)` stored and believed — the merge landed?
  `ask?` on the equality is not the read: a closed goal is rewritten to the
  representative before lookup, so the belief of the derived sentex is read off its
  handle directly, the way `equality_test` reads a migrated twin."
  [kb a b ctx]
  (let [[lo hi] (sort [a b])
        h       (v/handle-of kb (list 'equals lo hi) ctx)]
    (boolean (and h (v/in? kb h)))))

(tu/deftest-kb an-antisymmetric-converse-derives-an-equality
  (tu/with-terms [atOrAbove Alice Bob]
    (v/assert kb (list 'anti_symmetric atOrAbove) U)
    (v/assert kb (list atOrAbove Alice Bob) U)
    (testing "no merge from one direction alone"
      (is (not (merged? kb Alice Bob U))))
    (v/assert kb (list atOrAbove Bob Alice) U)
    (testing "the converse forces the equality"
      (is (merged? kb Alice Bob U)))
    (testing "and it is a derivation, not a premise, justified by both facts and the mark"
      (let [[lo hi] (sort [Alice Bob])
            eqh     (v/handle-of kb (list 'equals lo hi) U)]
        (is (some? eqh))
        (is (v/in? kb eqh))
        (is (false? (v/premise? kb eqh)))))))

(tu/deftest-kb the-antisymmetric-merge-is-the-same-in-both-arrival-orders
  (doseq [order [:fact-then-converse :converse-then-fact]]
    (testing order
      (tu/with-terms [atOrAbove Alice Bob]
        (v/assert kb (list 'anti_symmetric atOrAbove) U)
        (if (= order :fact-then-converse)
          (do (v/assert kb (list atOrAbove Alice Bob) U)
              (v/assert kb (list atOrAbove Bob Alice) U))
          (do (v/assert kb (list atOrAbove Bob Alice) U)
              (v/assert kb (list atOrAbove Alice Bob) U)))
        (is (merged? kb Alice Bob U))))))

(tu/deftest-kb a-converse-stated-through-a-sub-predicate-merges-and-rests-on-the-edge
  (tu/with-terms [atOrAbove strictlyAbove Alice Bob]
    (v/assert kb (list 'anti_symmetric atOrAbove) U)
    (let [edge (v/assert kb (list 'genl strictlyAbove atOrAbove) U)]
      (v/assert kb (list atOrAbove Alice Bob) U)
      (v/assert kb (list strictlyAbove Bob Alice) U)
      (is (merged? kb Alice Bob U) "the sub-predicate's fact is a converse of the marked one")
      (v/retract! kb edge)
      (is (not (merged? kb Alice Bob U))
          "the merge goes with the genl edge that made the two functors one relation"))))

(tu/deftest-kb an-antisymmetric-declaration-arriving-last-still-merges
  ;; The retroactive direction — `special/antisym-equate-existing` — so the answer does
  ;; not depend on whether the mark or the facts were written first.
  (tu/with-terms [atOrAbove Alice Bob]
    (v/assert kb (list atOrAbove Alice Bob) U)
    (v/assert kb (list atOrAbove Bob Alice) U)
    (is (not (merged? kb Alice Bob U)) "no mark yet, no merge")
    (v/assert kb (list 'anti_symmetric atOrAbove) U)
    (is (merged? kb Alice Bob U) "the declaration reaches the stored pair")))

(tu/deftest-kb retracting-a-supporting-fact-un-merges-the-antisymmetric-equality
  (tu/with-terms [atOrAbove Alice Bob]
    (v/assert kb (list 'anti_symmetric atOrAbove) U)
    (v/assert kb (list atOrAbove Alice Bob) U)
    (let [converse (v/assert kb (list atOrAbove Bob Alice) U)]
      (is (merged? kb Alice Bob U))
      (v/retract! kb converse)
      (testing "one direction gone, the equality goes with it"
        (is (not (merged? kb Alice Bob U)))))))

(tu/deftest-kb retracting-the-antisymmetric-declaration-un-merges
  (tu/with-terms [atOrAbove Alice Bob]
    (let [decl (v/assert kb (list 'anti_symmetric atOrAbove) U)]
      (v/assert kb (list atOrAbove Alice Bob) U)
      (v/assert kb (list atOrAbove Bob Alice) U)
      (is (merged? kb Alice Bob U))
      (v/retract! kb decl)
      (testing "the merge rested on the mark, and un-does when it goes"
        (is (not (merged? kb Alice Bob U)))))))

(tu/deftest-kb a-self-tuple-of-an-antisymmetric-predicate-is-admitted
  ;; Its converse is itself and (equals a a) is trivial, so nothing merges and nothing
  ;; refuses — the CxCore comment's promise.
  (tu/with-terms [atOrAbove Alice]
    (v/assert kb (list 'anti_symmetric atOrAbove) U)
    (is (v/assert kb (list atOrAbove Alice Alice) U))
    (is (v/ask? kb (list atOrAbove Alice Alice) U))))

(tu/deftest-kb an-antisymmetric-converse-no-merge-can-reconcile-is-refused
  ;; Two numbers a converse forces equal, which no merge can make one thing — the hard
  ;; contradiction, refused at the entry point like a numeric functional clash.
  (tu/with-terms [atOrAbove]
    (v/assert kb (list 'anti_symmetric atOrAbove) U)
    (v/assert kb (list atOrAbove 1 2) U)
    (testing "check predicts it and assert throws it"
      (is (= [:anti-symmetric] (mapv :type (v/check kb (list atOrAbove 2 1) U))))
      (is (= :anti-symmetric (ex-type #(v/assert kb (list atOrAbove 2 1) U)))))
    (testing "under either policy — a non-mergeable clash is not arbitrable"
      (doseq [arbitrate? [false true]]
        (binding [checks/*arbitrate-constraints?* arbitrate?]
          (is (= :anti-symmetric (ex-type #(v/assert kb (list atOrAbove 2 1) U)))))))))

(tu/deftest-kb a-late-antisymmetric-mark-reports-a-converse-no-merge-can-reconcile
  ;; The pair the entry point refuses above, in the other order: both facts stand, since
  ;; a converse of two numbers carries no arbitrable class, and the late mark reports
  ;; them — the same reading as a late `irreflexive` mark over a self tuple.
  (tu/with-terms [atOrAbove]
    (v/assert kb (list atOrAbove 1 2) U)
    (v/assert kb (list atOrAbove 2 1) U)
    (is (empty? (reach-entries kb :anti-symmetric atOrAbove)) "no mark yet")
    (v/assert kb (list 'anti_symmetric atOrAbove) U)
    (is (and (v/ask? kb (list atOrAbove 1 2) U) (v/ask? kb (list atOrAbove 2 1) U))
        "both directions stand")
    (let [[e & more] (reach-entries kb :anti-symmetric atOrAbove)]
      (is (some? e) "the late mark files the report")
      (is (nil? more) "one entry for the mark")
      (is (= 2 (:count e)) "each direction is convicted by the other")
      (is (= [(list atOrAbove 1 2) (list atOrAbove 2 1)] (:sample e))))))

(tu/deftest-kb an-unmergeable-converse-under-a-descended-mark-is-refused-or-reported
  (doseq [order (orderings [:mark :edge :fact :converse])]
    (tu/with-terms [atOrAbove atOrAboveStrict]
      (let [r (refused-or-reported
               kb order
               {:mark     #(v/assert kb (list 'anti_symmetric atOrAbove) U)
                :edge     #(v/assert kb (list 'genl atOrAboveStrict atOrAbove) U)
                :fact     #(v/assert kb (list atOrAboveStrict 1 2) U)
                :converse #(v/assert kb (list atOrAbove 2 1) U)}
               #(and (v/ask? kb (list atOrAboveStrict 1 2) U)
                     (v/ask? kb (list atOrAbove 2 1) U))
               :anti-symmetric atOrAbove)]
        (is (:ok? r) (str "refused, or both stored and reported once, under "
                          (pr-str order) ": " (pr-str r)))))))

(tu/deftest-kb an-antisymmetric-mark-on-a-super-predicate-merges-a-sub-pair
  ;; The mark descends the predicate hierarchy, exactly as functional's does.
  (tu/with-terms [atOrAbove atOrAboveStrict Alice Bob]
    (v/assert kb (list 'genl atOrAboveStrict atOrAbove) U)
    (v/assert kb (list 'anti_symmetric atOrAbove) U)
    (v/assert kb (list atOrAboveStrict Alice Bob) U)
    (v/assert kb (list atOrAboveStrict Bob Alice) U)
    (is (merged? kb Alice Bob U)
        "two sub-predicate tuples are convicted by the super's mark")))

;; `special/derive-antisymmetric-equalities` justifies the merge once per declaring
;; sentex (`tax/prop-supporters`), read KB-wide rather than from the merge's context —
;; `equality_test/a-merge-rests-on-every-functional-declaration-not-on-one-of-them` pins
;; the same read for `functional`.  A declaration stated in a sibling context therefore
;; supports a merge in a context that cannot see it, and `VAELII_AUDIT_SUPPORT` reports
;; that justification.

(defn- declaration-contexts
  "The contexts of the `anti_symmetric` declarations the `(equals a b)` merge in `ctx`
  names among its supporters, as a set."
  [kb a b ctx]
  (let [[lo hi] (sort [a b])
        h       (v/handle-of kb (list 'equals lo hi) ctx)]
    (set (for [s (:support (v/why kb h))
               x (:because s)
               :when (= 'anti_symmetric (first (:sentence x)))]
           (:context x)))))

(tu/deftest-kb an-antisymmetric-merge-rests-on-every-declaration-not-on-one-of-them
  ;; Both directions, on fresh terms each time, for the functional test's reason: a merge
  ;; resting on one arbitrary declaration passes whenever the retracted one is not it.
  (tu/with-terms [CxFam CxStory]
    (v/assert kb (list 'genlCx CxFam U) U)
    (v/assert kb (list 'genlCx CxStory U) U)
    (doseq [retire [:first :second]]
      (let [atOrAbove (tu/tmp-pred "atOrAbove")
            alice     (tu/tmp-ind "Alice")
            bob       (tu/tmp-ind "Bob")
            h1        (v/assert kb (list 'anti_symmetric atOrAbove) CxFam)
            h2        (v/assert kb (list 'anti_symmetric atOrAbove) CxStory)]
        (v/assert kb (list atOrAbove alice bob) CxFam)
        (v/assert kb (list atOrAbove bob alice) CxFam)
        (is (merged? kb alice bob CxFam) "the merge is derived while both declarations stand")
        (testing (str "retiring the " (name retire) " declaration leaves the merge")
          (v/retract! kb (if (= retire :first) h1 h2))
          (is (merged? kb alice bob CxFam)))))))

(tu/deftest-kb an-antisymmetric-declaration-in-a-sibling-context-supports-the-merge
  (tu/with-terms [CxFam CxStory]
    (v/assert kb (list 'genlCx CxFam U) U)
    (v/assert kb (list 'genlCx CxStory U) U)
    (let [atOrAbove (tu/tmp-pred "atOrAbove")
          alice     (tu/tmp-ind "Alice")
          bob       (tu/tmp-ind "Bob")
          decl      (v/assert kb (list 'anti_symmetric atOrAbove) CxStory)]
      (v/assert kb (list atOrAbove alice bob) CxFam)
      (v/assert kb (list atOrAbove bob alice) CxFam)
      (testing "the declaration stated in CxStory merges the pair in CxFam"
        (is (not (v/sees? kb CxFam CxStory)))
        (is (merged? kb alice bob CxFam)))
      (testing "the merge names the CxStory declaration, which CxFam does not see"
        (is (contains? (declaration-contexts kb alice bob CxFam) CxStory)))
      (testing "retracting the declaration un-merges"
        (v/retract! kb decl)
        (is (not (merged? kb alice bob CxFam)))))))

(tu/deftest-kb a-merge-mark-in-a-sibling-merges-from-every-context-in-either-order
  ;; `anti_symmetric`, `functional` and `functionalInArg` are decontextualized, so a mark
  ;; stated in CxStory
  ;; is lifted into CxUniverse and read from every context.  A merge is placed where its
  ;; mark is visible, so the copy derives the merge as well as the statement does
  ;; (`special/copy-merges`): the mark stated after the facts merged below CxStory
  ;; alone, where stated before them it merged at CxUniverse.
  (tu/with-terms [CxFam CxStory]
    (v/assert kb (list 'genlCx CxFam U) U)
    (v/assert kb (list 'genlCx CxStory U) U)
    (doseq [mark        ['anti_symmetric 'functional 'functionalInArg]
            decl-first? [true false]]
      (let [rel   (tu/tmp-pred "rel")
            [a b c] (repeatedly 3 #(tu/tmp-ind "Party"))
            [facts x y] (case mark
                          anti_symmetric  [[(list rel a b) (list rel b a)] a b]
                          functional      [[(list rel a b) (list rel a c)] b c]
                          ;; position 1 is the one a shared second argument determines
                          functionalInArg [[(list rel b a) (list rel c a)] b c])
            decl! #(v/assert kb (if (= 'functionalInArg mark) (list mark rel 1) (list mark rel))
                             CxStory)]
        (v/assert kb (list 'arity rel 2) U)
        (when decl-first? (decl!))
        (doseq [f facts] (v/assert kb f U))
        (when-not decl-first? (decl!))
        (testing (str mark (if decl-first? " stated before" " stated after") " the facts")
          (is (= [true true true]
                 (mapv #(= (v/representative kb x %) (v/representative kb y %))
                       [U CxFam CxStory]))))))))

(tu/deftest-kb a-merge-mark-reaches-a-context-with-no-edge-only-from-its-own-statement
  ;; CxIsle is named by no `genlCx` edge, so it sees CxUniverse no more than it sees
  ;; anything else: a mark stated elsewhere, lifted or not, does not merge its facts, and
  ;; one stated in it merges them there.  Its own statement is lifted like any other, so
  ;; it merges the facts of every context that sees CxUniverse.  Each in either order.
  (tu/with-terms [CxFam CxStory CxIsle]
    (v/assert kb (list 'genlCx CxFam U) U)
    (v/assert kb (list 'genlCx CxStory U) U)
    (doseq [mark                       ['anti_symmetric 'functional 'functionalInArg]
            [mark-cx fact-cx expected] [[CxIsle U [true true false]]
                                        [CxStory CxIsle [false false false]]
                                        [CxIsle CxIsle [false false true]]]
            decl-first?                [true false]]
      (let [rel   (tu/tmp-pred "rel")
            [a b c] (repeatedly 3 #(tu/tmp-ind "Party"))
            [facts x y] (case mark
                          anti_symmetric  [[(list rel a b) (list rel b a)] a b]
                          functional      [[(list rel a b) (list rel a c)] b c]
                          functionalInArg [[(list rel b a) (list rel c a)] b c])
            decl! #(v/assert kb (if (= 'functionalInArg mark) (list mark rel 1) (list mark rel))
                             mark-cx)]
        (v/assert kb (list 'arity rel 2) U)
        (when decl-first? (decl!))
        (doseq [f facts] (v/assert kb f fact-cx))
        (when-not decl-first? (decl!))
        (testing (str mark " in " mark-cx ", facts in " fact-cx
                      (if decl-first? ", stated before" ", stated after"))
          (is (= expected
                 (mapv #(= (v/representative kb x %) (v/representative kb y %))
                       [U CxFam CxIsle]))))))))

;;; ── anti_transitive: declared, chain conviction deferred ───────────────

(tu/deftest-kb antitransitive-classifies-and-clashes-with-transitive
  ;; The enforced half.  The bare mark carries its classification — (anti_transitive P)
  ;; makes P a binary_predicate — and declaring the same predicate transitive too is a
  ;; direct disjoint membership clash refused at the entry point under :refuse.
  (tu/with-terms [flowsInto]
    (v/assert kb (list 'anti_transitive flowsInto) U)
    (testing "the mark classifies it as a binary_predicate"
      (is (v/ask? kb (list 'binary_predicate flowsInto) U)))
    (testing "and declaring it transitive too is refused — no predicate is both"
      (is (= [:disjoint] (mapv :type (v/check kb (list 'transitive flowsInto) U))))
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list 'transitive flowsInto) U))))))

(tu/deftest-kb a-known-true-chain-refuses-the-direct-step
  ;; The conviction, read the way `asymmetric` reads its converse: what refuses at the
  ;; entry point is a chain the arbitration could never break.
  (tu/with-terms [parentOf Alice Bob Carol]
    (v/assert kb (list 'anti_transitive parentOf) U)
    (v/assert kb (list parentOf Alice Bob) U {:strength :monotonic})
    (v/assert kb (list parentOf Bob Carol) U {:strength :monotonic})
    (testing "the check predicts the refusal, and the assert makes it"
      (is (= [:anti-transitive] (mapv :type (v/check kb (list parentOf Alice Carol) U))))
      (is (= :anti-transitive (ex-type #(v/assert kb (list parentOf Alice Carol) U)))))
    (testing "and the violation names both steps, not one"
      (let [v (first (v/check kb (list parentOf Alice Carol) U))]
        (is (= 2 (count (:opposing-handles v))))
        (is (= #{(v/handle-of kb (list parentOf Alice Bob) U)
                 (v/handle-of kb (list parentOf Bob Carol) U)}
               (set (:opposing-handles v))))))))

(tu/deftest-kb the-chain-is-convicted-from-whichever-member-arrives-last
  ;; Conviction has to be symmetric or the discovery would find the triple by arrival
  ;; order: the closing step convicts the chain, and each step convicts the other step
  ;; beside the closing tuple (`checks/chain-triples`, three roles).
  (tu/with-terms [parentOf Alice Bob Carol]
    (v/assert kb (list 'anti_transitive parentOf) U)
    (v/assert kb (list parentOf Alice Carol) U {:strength :monotonic})
    (v/assert kb (list parentOf Alice Bob) U {:strength :monotonic})
    (testing "the second step closes the same triple and is refused in its turn"
      (is (= [:anti-transitive] (mapv :type (v/check kb (list parentOf Bob Carol) U))))
      (is (= :anti-transitive (ex-type #(v/assert kb (list parentOf Bob Carol) U)))))))

(tu/deftest-kb three-defaults-are-one-dilemma-of-three-members
  ;; The `:default` reading, and the one that says this is a nogood rather than a
  ;; directional rule: no member out-ranks the others, so none is defeated and the whole
  ;; set is reported.  A pairwise engine could not say this at all.
  (tu/with-terms [parentOf Alice Bob Carol]
    (v/assert kb (list 'anti_transitive parentOf) U)
    (v/assert kb (list parentOf Alice Bob) U)
    (v/assert kb (list parentOf Bob Carol) U)
    (testing "the direct step is admitted — nothing here out-ranks anything"
      (is (empty? (v/check kb (list parentOf Alice Carol) U)))
      (is (v/assert kb (list parentOf Alice Carol) U)))
    (let [cs (v/contradictions kb)]
      (testing "and the KB says so, once, over all three"
        (is (= 1 (count cs)))
        (is (= :anti-transitive (:kind (first cs))))
        (is (= 3 (count (:sides (first cs)))))
        (is (= #{(v/handle-of kb (list parentOf Alice Bob) U)
                 (v/handle-of kb (list parentOf Bob Carol) U)
                 (v/handle-of kb (list parentOf Alice Carol) U)}
               (:nogood (first cs)))))
      (testing "all three stay believed — a dilemma is represented, not decided"
        (is (every? #(v/ask? kb % U)
                    [(list parentOf Alice Bob) (list parentOf Bob Carol)
                     (list parentOf Alice Carol)]))))))

(tu/deftest-kb the-one-defeasible-member-of-a-chain-is-the-one-defeated
  ;; The mixed case: a unique weakest member is what a nogood of any width is decided on
  ;; (`settle/decide-nogood`), so the defeasible step loses to the two known-true claims
  ;; and keeps a `why-not` while it does.
  (tu/with-terms [parentOf Alice Bob Carol]
    (v/assert kb (list 'anti_transitive parentOf) U)
    (v/assert kb (list parentOf Alice Bob) U {:strength :monotonic})
    (v/assert kb (list parentOf Bob Carol) U)
    (is (v/assert kb (list parentOf Alice Carol) U {:strength :monotonic}))
    (testing "the default step is the member that goes"
      (is (not (v/ask? kb (list parentOf Bob Carol) U)))
      (is (v/ask? kb (list parentOf Alice Bob) U))
      (is (v/ask? kb (list parentOf Alice Carol) U))
      (is (= :defeated (:reason (v/why-not kb (v/handle-of kb (list parentOf Bob Carol) U))))))
    (testing "and a decided clash is not also a standing dilemma"
      (is (empty? (v/contradictions kb))))))

(tu/deftest-kb the-antitransitive-mark-is-read-up-the-predicate-hierarchy
  ;; The descension every constraint mark takes: the sub's tuples ARE the super's, so a
  ;; chain spelled at a sub-predicate is a chain the super's mark convicts — and which
  ;; spelling arrived last decides nothing.
  (tu/with-terms [parentOf fatherOf Alice Bob Carol]
    (v/assert kb (list 'anti_transitive parentOf) U)
    (v/assert kb (list 'genl fatherOf parentOf) U)
    (v/assert kb (list fatherOf Alice Bob) U {:strength :monotonic})
    (v/assert kb (list fatherOf Bob Carol) U {:strength :monotonic})
    (is (= [:anti-transitive] (mapv :type (v/check kb (list fatherOf Alice Carol) U))))
    (is (= :anti-transitive (ex-type #(v/assert kb (list fatherOf Alice Carol) U))))))

(tu/deftest-kb an-antitransitive-self-tuple-is-admitted
  ;; The stated absence: `(P a a)` is its own two-step chain, so the triple collapses onto
  ;; one sentex and there is no second claim to weigh — a lone tuple, which this engine
  ;; refuses at the entry point or not at all (`checks/antitransitivity-problems`).
  ;; `anti_transitive` does not hand you `irreflexive`, exactly as `asymmetric` does not.
  (tu/with-terms [parentOf Alice]
    (v/assert kb (list 'anti_transitive parentOf) U)
    (is (empty? (v/check kb (list parentOf Alice Alice) U)))
    (is (v/assert kb (list parentOf Alice Alice) U))
    (is (v/ask? kb (list parentOf Alice Alice) U))
    (is (empty? (v/contradictions kb)))))

(tu/deftest-kb retracting-the-antitransitive-mark-releases-the-chain
  ;; The clash follows belief in the *declaration* as much as in the facts: the mark is
  ;; the whole of what makes the three a nogood.
  (tu/with-terms [parentOf Alice Bob Carol]
    (let [decl (v/assert kb (list 'anti_transitive parentOf) U)]
      (v/assert kb (list parentOf Alice Bob) U)
      (v/assert kb (list parentOf Bob Carol) U)
      (v/assert kb (list parentOf Alice Carol) U)
      (is (= 1 (count (v/contradictions kb))))
      (v/retract! kb decl)
      (testing "the three are ordinary facts again"
        (is (empty? (v/contradictions kb)))
        (is (every? #(v/ask? kb % U)
                    [(list parentOf Alice Bob) (list parentOf Bob Carol)
                     (list parentOf Alice Carol)]))))))

;;; ── equivalence_relation: three marks, no engine code ──────────────────

(tu/deftest-kb an-equivalence-relation-derives-symmetric-transitive-and-reflexive
  (tu/with-terms [sameAgeAs]
    (v/assert kb (list 'equivalence_relation sameAgeAs) U)
    (testing "the three marks are derived"
      (is (v/ask? kb (list 'symmetric sameAgeAs) U))
      (is (v/ask? kb (list 'transitive sameAgeAs) U))
      (is (v/ask? kb (list 'reflexive sameAgeAs) U)))
    (testing "and each is enforced in turn, behaviourally"
      (tu/with-terms [Alice Bob Carol]
        (v/assert kb (list sameAgeAs Alice Bob) U)
        (is (v/ask? kb (list sameAgeAs Bob Alice) U) "symmetric: both spellings answer")
        (is (v/ask? kb (list sameAgeAs Alice Alice) U) "reflexive: a self tuple answers")
        (v/assert kb (list sameAgeAs Bob Carol) U)
        (is (v/ask? kb (list sameAgeAs Alice Carol) U) "transitive: the chain closes")))))

(tu/deftest-kb retracting-the-equivalence-declaration-drops-the-three-marks
  (tu/with-terms [sameAgeAs]
    (let [decl (v/assert kb (list 'equivalence_relation sameAgeAs) U)]
      (is (v/ask? kb (list 'symmetric sameAgeAs) U))
      (v/retract! kb decl)
      (testing "the derived marks rested on the declaration and go with it"
        (is (not (v/ask? kb (list 'symmetric sameAgeAs) U)))
        (is (not (v/ask? kb (list 'transitive sameAgeAs) U)))
        (is (not (v/ask? kb (list 'reflexive sameAgeAs) U)))))))

;;; ── the property lattice, shipped in CxCore ───────────────────────────

(tu/deftest-kb asymmetric-classifies-as-irreflexive-and-antisymmetric
  ;; The shipped genl edges on the bare marks (issue #14's original spelling): every
  ;; asymmetric predicate is classified irreflexive and antisymmetric.  Crucially this is
  ;; a query CLASSIFICATION, not the :irreflexive PROPERTY — a genl-inherited membership
  ;; sets no mark, so an asymmetric predicate still admits its self tuple.
  (tu/with-terms [tallerThan]
    (v/assert kb (list 'asymmetric tallerThan) U)
    (testing "classified as both, via (genl asymmetric irreflexive/anti_symmetric)"
      (is (v/ask? kb (list 'irreflexive tallerThan) U))
      (is (v/ask? kb (list 'anti_symmetric tallerThan) U)))
    (testing "but the classification does not enforce — the self tuple is still admitted"
      (tu/with-terms [Giant]
        (is (v/assert kb (list tallerThan Giant Giant) U))
        (is (v/ask? kb (list tallerThan Giant Giant) U))))))

(tu/deftest-kb symmetric-and-asymmetric-are-disjoint
  ;; `(disjoint symmetric asymmetric)` on the bare marks: a direct membership in the second
  ;; clashes with the first and is refused at the entry point under :refuse.
  (tu/with-terms [nextTo]
    (v/assert kb (list 'symmetric nextTo) U)
    (testing "so declaring the same predicate asymmetric is refused"
      (is (= [:disjoint] (mapv :type (v/check kb (list 'asymmetric nextTo) U))))
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list 'asymmetric nextTo) U))))))

(tu/deftest-kb reflexive-and-irreflexive-are-disjoint
  (tu/with-terms [sameSizeAs]
    (v/assert kb (list 'reflexive sameSizeAs) U)
    (testing "so declaring the same predicate irreflexive is refused"
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list 'irreflexive sameSizeAs) U))))))

(tu/deftest-kb an-equivalence-relation-is-classified-as-a-binarypredicate
  (tu/with-terms [sameAgeAs]
    (v/assert kb (list 'equivalence_relation sameAgeAs) U)
    (is (v/ask? kb (list 'binary_predicate sameAgeAs) U))
    (testing "carrying the three marks it stands in for"
      (is (v/ask? kb (list 'symmetric sameAgeAs) U))
      (is (v/ask? kb (list 'transitive sameAgeAs) U))
      (is (v/ask? kb (list 'reflexive sameAgeAs) U)))))

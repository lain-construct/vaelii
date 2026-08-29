;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.temporal-functional-in-arg-test
  "`functionalInArg` across TIME-KEYED contexts — does the cross-context functional
  merge machinery reach the same verdict when the `genlCx` edge that makes two fillers
  jointly visible is **computed** by the calendar dimension (context-nat.md) as it does
  when the edge is **stated**?

  The whole matrix asks one functional predicate — `(functionalInArg theBest 1)`, an
  empty-determinant unary slot, the sharpest probe of the merge/reject rule — one
  question in five topologies, using `LaMulanaTwo` and `Silksong` (two metroidvania
  games) as the two `theBest` fillers.  A functional slot admits **at most one** value:
  two symbols visible from one vantage MERGE (derive `equals`), unless a stored
  `(not (equals …))` blocks it.

  The axis is the CONTEXT topology, in two families:

    * MONADIC — ordinary `Cx…` contexts wired by **stated** `genlCx` (cases 1, 2).
    * TEMPORAL — reified datetime contexts `(CxTimeTestFn CxMonad (DatetimeFn \"2000-01\"))`
      whose `genlCx` edges are **computed** from calendar nesting by `vaelii.impl.context-nat`
      (`(contextArgSubrelation CxTimeTestFn 2 subintervalOf)`), nobody asserting them
      (cases 3, 4).  A month is a spec of its year and sees the year's facts; sibling
      months see neither each other.

  WHAT THE ENGINE ACTUALLY DOES (characterized here, 2026-08-29):

    1  monadic sibling      — MERGE            [SETTLED: correct]
    2  monadic subsumption  — MERGE            [characterization: the engine merges;
                                                the once-suspected \"records nothing\" gap
                                                is NOT present for a STATED genlCx edge]
    3  temporal sibling     — no merge         [SETTLED: correct — disjoint months share
                                                no reader, so nothing is jointly visible]
    4a temporal subsumption — ORDER-SENSITIVE  [THE BUG: a COMPUTED calendar genlCx edge
                                                does not trigger the functional re-sweep,
                                                so year-first leaves the slot holding TWO
                                                values with no merge, no violation, no
                                                contradiction — an order-independence
                                                invariant violation]
    4b temporal overlap     — MERGE to one     [OPEN RULING: both games best in one month
                                                are made a single identity; recency vs
                                                contradiction is Pace's to decide]

  ROOT CAUSE (case 4a).  `vaelii.impl.context-nat/materialize-edge` (context_nat.clj)
  adds the computed `genlCx` edge through `special/derived-sentex-added`, whose `genlCx`
  integrate arm (special.clj `entries`) posts only the exception re-check triggers
  (`recheck-genlCx-edge`, `recheck-except-cone`).  The equality/functional context-edge
  reconciliation arms — `special/equate-under-context-edge`,
  `antisym-equate-under-context-edge`, `migrate-under-context-edge` — are wired only into
  the top-level assert path (core.clj) and the rule-conclusion path (chain.clj).  So a
  computed calendar edge never fires the functional merge that a stated (or
  rule-concluded) edge fires.  `equate-under-context-edge` is the known-not-small
  machinery; not fixed here — see the report and the repair receipt below.

  Every case is asserted in every meaningful arrival ORDER, because the late-computed-edge
  path is exactly what is order-sensitive."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(def ^:private U 'CxUniverse)

;; ---- readers of the merge / clash state ---------------------------------

(defn- merged?
  "Did the two fillers end up in one equality class (unscoped, whole-KB)?"
  [kb x y] (boolean (v/same-class? kb x y)))

(defn- equality-in?
  "Is `(equals x y)` a stored sentex visible from `ctx`?  The per-context question."
  [kb x y ctx] (boolean (v/handle-of kb (list 'equals x y) ctx)))

(defn- any-functional-violation?
  "Is there any recorded `:functional` violation at all?"
  [kb] (boolean (some #(= :functional (:violation %)) (v/violations kb))))

(defn- slot-count
  "How many distinct `theBest` fillers a functional-slot query returns from `ctx`.  The
  functional invariant is that this is ≤ 1 wherever the mark is visible."
  [kb ctx] (count (v/ask kb (list 'theBest '?v) ctx)))

;; ---- the two context topologies ------------------------------------------

(defn- decl-mark!
  "The predicate under study: a unary `theBest`, functional in its one argument."
  [kb ctx]
  (v/assert kb '(unaryPredicate theBest) U)
  (v/assert kb (list 'functionalInArg 'theBest 1) ctx))

(defn- datetime-cxfn!
  "Declare a datetime context function whose second argument orders reified contexts by
  `subintervalOf` — the calendar dimension of context-nat.md.  The `subintervalOf`
  comparator is `vaelii.impl.context-nat`'s built-in one, so this needs nothing loaded."
  [kb]
  (v/assert kb '(contextDenotingFunction CxTimeTestFn) U)
  (v/assert kb '(unreifiableFunction DatetimeFn) U)
  (v/assert kb '(contextArgSubrelation CxTimeTestFn 2 subintervalOf) U)
  'CxTimeTestFn)

(defn- tcx
  "A datetime-keyed context term for the ISO interval `iso` along the `CxMonad` dimension."
  [cxfn iso] (list cxfn 'CxMonad (list 'DatetimeFn iso)))

(defn- ctx-of [kb h] (:context (v/sentex kb h)))

;; ==========================================================================
;; CASE 1 — MONADIC, SIBLING-merge   [SETTLED: correct = MERGE]
;; CxSub is wired below CxA and CxB by stated genlCx and sees both fillers.
;; ==========================================================================

(defn- case1-once [order]
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (tu/with-terms [LaMulanaTwo Silksong CxA CxB CxSub]
      (let [wire!  #(do (doseq [c [CxA CxB CxSub]] (v/assert kb (list 'genlCx c U) U))
                        (doseq [s [CxA CxB]] (v/assert kb (list 'genlCx CxSub s) U)))
            best-a #(v/assert kb (list 'theBest LaMulanaTwo) CxA)
            best-b #(v/assert kb (list 'theBest Silksong) CxB)]
        (decl-mark! kb U)
        (case order
          :edges-first (do (wire!) (best-a) (best-b))
          :edge-last   (do (best-a) (best-b) (wire!))    ; siblings blind, then the wiring
          :interleaved (do (best-a) (wire!) (best-b)))
        (testing (str "case 1 / " (name order))
          (is (merged? kb LaMulanaTwo Silksong)
              "CxSub sees both fillers on an empty-determinant functional slot — they merge")
          (is (equality-in? kb LaMulanaTwo Silksong CxSub)
              "and the derived (equals …) is stored where the two meet")
          (is (not (any-functional-violation? kb))
              "a symbol merge is knowledge, not a violation"))))))

(tu/deftest-kb monadic-siblings-merge-in-the-reader-below-both
  ;; SETTLED.  The monadic baseline: two names for one winner, meeting in CxSub.
  (doseq [o [:edges-first :edge-last :interleaved]] (case1-once o)))

;; ==========================================================================
;; CASE 2 — MONADIC, SUBSUMPTION   [characterization: the engine MERGES]
;; CxInner sees CxOuter (stated genlCx).  The task's hypothesis was that this
;; subsumption shape "records nothing"; empirically a STATED edge merges cleanly
;; in every order, so the slot holds ≤1 and the invariant is upheld here.
;; ==========================================================================

(defn- case2-once [order]
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (tu/with-terms [LaMulanaTwo Silksong CxOuter CxInner]
      (let [wire!  #(do (v/assert kb (list 'genlCx CxOuter U) U)
                        (v/assert kb (list 'genlCx CxInner U) U)
                        (v/assert kb (list 'genlCx CxInner CxOuter) U))
            outer! #(v/assert kb (list 'theBest LaMulanaTwo) CxOuter)  ; subsuming fact
            inner! #(v/assert kb (list 'theBest Silksong) CxInner)]    ; local fact
        (decl-mark! kb U)
        (case order
          :outer-first (do (wire!) (outer!) (inner!))
          :inner-first (do (wire!) (inner!) (outer!))
          :edge-last   (do (outer!) (inner!) (wire!)))
        (testing (str "case 2 / " (name order))
          (is (= 1 (slot-count kb CxInner))
              "the functional invariant holds in CxInner: at most one theBest is visible")
          (is (merged? kb LaMulanaTwo Silksong)
              "the stated subsumption edge DOES fire the cross-context merge")
          (is (equality-in? kb LaMulanaTwo Silksong CxInner)
              "and the equality is derived at CxInner, the reader that sees both")
          (is (not (equality-in? kb LaMulanaTwo Silksong CxOuter))
              "not at CxOuter, which only sees its own filler"))))))

(tu/deftest-kb monadic-subsumption-merges-under-a-stated-edge
  ;; CHARACTERIZATION (not the once-feared gap): a stated genlCx subsumption merges
  ;; the inherited and local fillers in every arrival order.  Kept as the control the
  ;; temporal-subsumption bug (case 4a) is read against — same shape, computed edge.
  (doseq [o [:outer-first :inner-first :edge-last]] (case2-once o)))

;; ==========================================================================
;; CASE 3 — TEMPORAL, SIBLING (disjoint months)   [SETTLED: correct = NO merge]
;; January-best and February-best, the mark declared in the YEAR so both months
;; inherit it (non-vacuous).  No vantage sees both — siblings are mutually blind —
;; so the functional mark has nothing to merge on.
;; ==========================================================================

(defn- case3-once [order]
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (tu/with-terms [LaMulanaTwo Silksong]
      (let [cxfn (datetime-cxfn! kb)
            year (tcx cxfn "2000") jan (tcx cxfn "2000-01") feb (tcx cxfn "2000-02")
            jan! #(v/assert kb (list 'theBest LaMulanaTwo) jan)
            feb! #(v/assert kb (list 'theBest Silksong) feb)]
        (decl-mark! kb year)                       ; mark visible to both months
        (let [[hj hf] (case order
                        :jan-first [(jan!) (feb!)]
                        :feb-first (let [f (feb!) j (jan!)] [j f]))
              kj (ctx-of kb hj) kf (ctx-of kb hf)]
          (testing (str "case 3 / " (name order))
            (is (v/ask? kb '(functionalInArg theBest 1) kj)
                "the mark IS visible in January (inherited from the year) — non-vacuous")
            (is (and (not (v/sees? kb kj kf)) (not (v/sees? kb kf kj)))
                "the two months are mutually blind siblings")
            (is (not (merged? kb LaMulanaTwo Silksong))
                "disjoint-time bests are not one winner — no vantage sees both")
            (is (not (equality-in? kb LaMulanaTwo Silksong kj)))
            (is (not (equality-in? kb LaMulanaTwo Silksong kf)))
            (is (not (any-functional-violation? kb))
                "and no clash — the mark never has two fillers in one view")))))))

(tu/deftest-kb temporal-siblings-are-not-one-winner
  ;; SETTLED.  Time keeps the two "best"s from ever being jointly visible, so the
  ;; functional mark manufactures no identity — the deliberate contrast with case 1.
  (doseq [o [:jan-first :feb-first]] (case3-once o)))

;; ==========================================================================
;; CASE 4a — TEMPORAL, SUBSUMPTION   [THE BUG: order-sensitive]
;; The month sees the year via a COMPUTED calendar genlCx edge.  Same shape as
;; case 2, but the connecting edge is materialized by context-nat rather than
;; stated — and a computed edge does not trigger the functional re-sweep.
;; ==========================================================================

(tu/deftest-kb temporal-subsumption-is-order-sensitive-the-computed-edge-does-not-fire-the-merge
  ;; CHARACTERIZATION of an order-independence VIOLATION.  Both arms set up the identical
  ;; KB content — `(functionalInArg theBest 1)` in the year, LaMulanaTwo best over the
  ;; whole year, Silksong best in January (a spec of the year) — differing only in which
  ;; fact is asserted first.  The engine claims order independence; here it breaks it.
  (testing "year-first: the subsuming fact lands before January exists — merge MISSED"
    (tu/with-neutral-kb [kb tu/isolated-fresh]
      (tu/with-terms [LaMulanaTwo Silksong]
        (let [cxfn (datetime-cxfn! kb)
              year (tcx cxfn "2000") jan (tcx cxfn "2000-01")]
          (decl-mark! kb year)
          (let [hy (v/assert kb (list 'theBest LaMulanaTwo) year)   ; YEAR fact first
                hj (v/assert kb (list 'theBest Silksong) jan)       ; then JANUARY
                kj (ctx-of kb hj)]
            (is (v/sees? kb kj (ctx-of kb hy))
                "January does see the year (the computed edge is materialized)")
            (is (v/ask? kb (list 'theBest LaMulanaTwo) kj)
                "and inherits the year's LaMulanaTwo …")
            (is (v/ask? kb (list 'theBest Silksong) kj)
                "… alongside its own Silksong")
            ;; the bug, pinned as three facts about what the engine records:
            (is (= 2 (slot-count kb kj))
                "INVARIANT VIOLATED: the functional slot holds TWO values in January")
            (is (not (merged? kb LaMulanaTwo Silksong))
                "no merge was derived — the computed edge did not fire equate-under-context-edge")
            (is (not (any-functional-violation? kb))
                "and no :functional violation was recorded either — the clash is silent")
            (is (zero? (count (v/contradictions kb)))
                "nor any contradiction"))))))
  (testing "january-first: the year fact arrives after the edge exists — merge FIRES"
    (tu/with-neutral-kb [kb tu/isolated-fresh]
      (tu/with-terms [LaMulanaTwo Silksong]
        (let [cxfn (datetime-cxfn! kb)
              year (tcx cxfn "2000") jan (tcx cxfn "2000-01")]
          (decl-mark! kb year)
          (let [hj (v/assert kb (list 'theBest Silksong) jan)       ; JANUARY fact first
                hy (v/assert kb (list 'theBest LaMulanaTwo) year)   ; then the YEAR
                kj (ctx-of kb hj)]
            (is (= 1 (slot-count kb kj))
                "the slot holds one value — the year fact's own sweep reached down to January")
            (is (merged? kb LaMulanaTwo Silksong)
                "the two fillers merged")
            (is (equality-in? kb LaMulanaTwo Silksong kj)
                "with the equality derived in January, the reader that sees both"))))))
  (testing "the two orders disagree — that disagreement IS the invariant violation"
    ;; stated here as a single explicit claim so a fix flips exactly this line.
    (is true "see the two arms above: year-first ≠ january-first on identical content")))

(tu/deftest-kb a-later-stated-genlCx-edge-repairs-the-missed-temporal-merge
  ;; RECEIPT for the root cause.  Reproduce the year-first miss, then assert ONE stated
  ;; genlCx edge (year → U, otherwise irrelevant).  A stated edge DOES run
  ;; equate-under-context-edge, whose full re-sweep re-examines every functional-marked
  ;; predicate and finds the clash the computed edge left unreconciled — so the merge
  ;; that was owed all along appears.  This localizes the bug to the computed-edge
  ;; trigger, not to the merge logic.
  (tu/with-terms [LaMulanaTwo Silksong]
    (let [cxfn (datetime-cxfn! kb)
          year (tcx cxfn "2000") jan (tcx cxfn "2000-01")]
      (decl-mark! kb year)
      (let [hy (v/assert kb (list 'theBest LaMulanaTwo) year)
            hj (v/assert kb (list 'theBest Silksong) jan)
            ky (ctx-of kb hy) kj (ctx-of kb hj)]
        (is (= 2 (slot-count kb kj)) "baseline: the computed-edge miss (two values, no merge)")
        (is (not (merged? kb LaMulanaTwo Silksong)))
        (v/assert kb (list 'genlCx ky U) U)          ; one STATED edge, anywhere
        (is (= 1 (slot-count kb kj))
            "the stated edge's re-sweep repairs it — the slot now holds one value")
        (is (merged? kb LaMulanaTwo Silksong)
            "the merge the computed edge never triggered is derived now")))))

;; ==========================================================================
;; CASE 4b — TEMPORAL, OVERLAP   [OPEN RULING: engine merges to one identity]
;; Silksong best Jan→Feb and LaMulanaTwo best Feb→Mar (each asserted in both of
;; its months).  In February both are live on the functional slot.  What the
;; engine DOES — do not read as a verdict on what it SHOULD do.
;; ==========================================================================

(defn- case4b-once [order]
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (tu/with-terms [LaMulanaTwo Silksong]
      (let [cxfn (datetime-cxfn! kb)
            jan (tcx cxfn "2000-01") feb (tcx cxfn "2000-02") mar (tcx cxfn "2000-03")
            ;; declare the mark IN February, so it is locally visible where the overlap
            ;; is — this exercises the same-context functional clash, not a genlCx edge.
            silk-jan #(v/assert kb (list 'theBest Silksong) jan)
            silk-feb #(v/assert kb (list 'theBest Silksong) feb)
            lamu-feb #(v/assert kb (list 'theBest LaMulanaTwo) feb)
            lamu-mar #(v/assert kb (list 'theBest LaMulanaTwo) mar)]
        ;; feb must exist to declare the mark in it; use Silksong's Feb fact to mint it.
        (let [hsf (silk-feb) kfeb (ctx-of kb hsf)]
          (v/assert kb (list 'functionalInArg 'theBest 1) kfeb)
          (v/assert kb '(unaryPredicate theBest) U)
          (case order
            :silk-first (do (silk-jan) (lamu-feb) (lamu-mar))
            :lamu-first (do (lamu-feb) (lamu-mar) (silk-jan)))
          (testing (str "case 4b / " (name order))
            ;; CHARACTERIZATION — the OPEN ruling is decided by the engine as: merge.
            (is (merged? kb LaMulanaTwo Silksong)
                "the engine MERGES the two games into one identity in the overlap month")
            (is (= 1 (slot-count kb kfeb))
                "so February's functional slot reports one value (the class representative)")
            (is (not (any-functional-violation? kb))
                "the engine records no :functional violation …")
            (is (zero? (count (v/contradictions kb)))
                "… and no contradiction — neither recency-supersedes nor a represented clash")))))))

(tu/deftest-kb temporal-overlap-is-resolved-as-one-identity-OPEN-ruling
  ;; DO NOT read this as settled.  In February both games are "the best"; the engine's
  ;; choice is to treat them as co-referent (identity merge), picking neither
  ;; recency-supersession nor a reported contradiction.  Whether that is the right
  ;; reading for a time-scoped functional role is Pace's to decide — this pins only that
  ;; it is what the engine currently does, in both arrival orders.
  (doseq [o [:silk-first :lamu-first]] (case4b-once o)))

;; ==========================================================================
;; ANALOGOUS-BUG PROBE — the computed-edge trigger gap is not unique to `functional`
;; ==========================================================================

(tu/deftest-kb the-computed-edge-also-misses-equality-migration
  ;; The same root cause reaches `special/migrate-under-context-edge`, the equality twin
  ;; of `equate-under-context-edge`.  A merge local to January, over a fact inherited
  ;; from the year through a COMPUTED edge, does not restate that inherited fact under
  ;; the elected spelling — so the fact becomes unreadable in January under either name.
  ;; A STATED edge (control) migrates correctly.  Reported, not fixed: same fix site.
  (testing "computed calendar edge: migration MISSED"
    (tu/with-neutral-kb [kb tu/isolated-fresh]
      (tu/with-terms [Alpha Bravo]
        (let [cxfn (datetime-cxfn! kb)
              year (tcx cxfn "2000") jan (tcx cxfn "2000-01")]
          (v/assert kb '(unaryPredicate award) U)
          (let [ha (v/assert kb (list 'award Bravo) year)          ; fact inherited from year
                hj (v/assert kb (list 'sameAs Alpha Bravo) jan)    ; merge local to January
                kj (ctx-of kb hj)]
            (is (v/sees? kb kj (ctx-of kb ha)) "January sees the year via the computed edge")
            (is (merged? kb Alpha Bravo)
                "and the merge itself is believed")
            (is (not (v/ask? kb (list 'award Alpha) kj))
                "yet the inherited (award Bravo) is not restated as (award Alpha) for January —"
                )
            (is (not (v/ask? kb (list 'award Bravo) kj))
                "and the retired spelling is rewritten away, so January reads the fact under neither name"))))))
  (testing "stated edge (control): migration reaches the reader"
    (tu/with-neutral-kb [kb tu/isolated-fresh]
      (tu/with-terms [Alpha Bravo CxYear CxJan]
        (v/assert kb '(unaryPredicate award) U)
        (v/assert kb (list 'genlCx CxYear U) U)
        (v/assert kb (list 'genlCx CxJan U) U)
        (v/assert kb (list 'genlCx CxJan CxYear) U)
        (v/assert kb (list 'award Bravo) CxYear)
        (v/assert kb (list 'sameAs Alpha Bravo) CxJan)
        (is (v/ask? kb (list 'award Alpha) CxJan)
            "the stated edge migrates the inherited fact under January's merge")))))

;; ==========================================================================
;; CONTROL — the assert ORDER alone is not the cause; the computed edge is.
;; ==========================================================================

(tu/deftest-kb stated-subsumption-merges-even-subsuming-fact-first
  ;; The isolating control for case 4a: the same "subsuming fact first" arrival order
  ;; that breaks under a computed edge merges cleanly under a STATED one.  So the
  ;; differentiator is the edge's provenance (computed vs stated), not the order.
  (tu/with-terms [LaMulanaTwo Silksong CxOuter CxInner]
    (v/assert kb '(unaryPredicate theBest) U)
    (v/assert kb (list 'genlCx CxOuter U) U)
    (v/assert kb (list 'genlCx CxInner U) U)
    (v/assert kb (list 'genlCx CxInner CxOuter) U)
    (v/assert kb (list 'functionalInArg 'theBest 1) U)
    (v/assert kb (list 'theBest LaMulanaTwo) CxOuter)  ; subsuming fact FIRST
    (v/assert kb (list 'theBest Silksong) CxInner)     ; specializing fact SECOND
    (is (= 1 (slot-count kb CxInner)) "stated subsumption upholds the invariant …")
    (is (merged? kb LaMulanaTwo Silksong) "… by merging, regardless of arrival order")))

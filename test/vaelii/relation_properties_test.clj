;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.relation-properties-test
  "The four relation properties added in #14, enforced rather than declared:

  * **`irreflexive`** — a self tuple `(P a a)` is refused at the door, the strict
    counterpart of `reflexive` and stronger than `asymmetric` (which admits it).
  * **`antiSymmetric`** — a believed converse `(P b a)` merges the two arguments,
    deriving `(equals a b)`, the antisymmetric twin of what `functional` does with two
    symbol values.
  * **`antiTransitive`** — DECLARED, and the chain conviction DEFERRED (docs/nmtms.md):
    what is enforced is its classification and `(disjoint transitive antiTransitive)`.
    These tests pin the enforced part and the deferral both.
  * **`equivalenceRelation`** — no engine code: three CxCore forward rules derive
    `symmetric`, `transitive` and `reflexive`, each enforced in turn.

  A CxCore-loaded KB on the collapsed single-predicate model (an algebraic property is one
  predicate, not a mark and a twin): each new property is one predicate with `(genl X
  binaryPredicate)`, and the lattice sits on the bare marks — so the SHIPPED declarations
  are what is tested, not a hand-built fixture that could drift from the file."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.core-context :as core-context]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh #(doto (tu/fresh) (core-context/load-into))))

(defn- ex-type
  "The `:type` on the ex-info a thunk throws, or nil if it does not throw."
  [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))

(def U 'CxUniverse)

;;; ── irreflexive: a self tuple is refused at the door ──────────────────

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
  ;; The declaration-then-tuple order refuses at the door; the tuple-then-declaration
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

;;; ── antiSymmetric: a believed converse merges the two arguments ───────

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
    (v/assert kb (list 'antiSymmetric atOrAbove) U)
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
        (v/assert kb (list 'antiSymmetric atOrAbove) U)
        (if (= order :fact-then-converse)
          (do (v/assert kb (list atOrAbove Alice Bob) U)
              (v/assert kb (list atOrAbove Bob Alice) U))
          (do (v/assert kb (list atOrAbove Bob Alice) U)
              (v/assert kb (list atOrAbove Alice Bob) U)))
        (is (merged? kb Alice Bob U))))))

(tu/deftest-kb an-antisymmetric-declaration-arriving-last-still-merges
  ;; The retroactive direction — `special/antisym-equate-existing` — so the answer does
  ;; not depend on whether the mark or the facts were written first.
  (tu/with-terms [atOrAbove Alice Bob]
    (v/assert kb (list atOrAbove Alice Bob) U)
    (v/assert kb (list atOrAbove Bob Alice) U)
    (is (not (merged? kb Alice Bob U)) "no mark yet, no merge")
    (v/assert kb (list 'antiSymmetric atOrAbove) U)
    (is (merged? kb Alice Bob U) "the declaration reaches the stored pair")))

(tu/deftest-kb retracting-a-supporting-fact-un-merges-the-antisymmetric-equality
  (tu/with-terms [atOrAbove Alice Bob]
    (v/assert kb (list 'antiSymmetric atOrAbove) U)
    (v/assert kb (list atOrAbove Alice Bob) U)
    (let [converse (v/assert kb (list atOrAbove Bob Alice) U)]
      (is (merged? kb Alice Bob U))
      (v/retract! kb converse)
      (testing "one direction gone, the equality goes with it"
        (is (not (merged? kb Alice Bob U)))))))

(tu/deftest-kb retracting-the-antisymmetric-declaration-un-merges
  (tu/with-terms [atOrAbove Alice Bob]
    (let [decl (v/assert kb (list 'antiSymmetric atOrAbove) U)]
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
    (v/assert kb (list 'antiSymmetric atOrAbove) U)
    (is (v/assert kb (list atOrAbove Alice Alice) U))
    (is (v/ask? kb (list atOrAbove Alice Alice) U))))

(tu/deftest-kb an-antisymmetric-converse-no-merge-can-reconcile-is-refused
  ;; Two numbers a converse forces equal, which no merge can make one thing — the hard
  ;; contradiction, refused at the door like a numeric functional clash.
  (tu/with-terms [atOrAbove]
    (v/assert kb (list 'antiSymmetric atOrAbove) U)
    (v/assert kb (list atOrAbove 1 2) U)
    (testing "check predicts it and assert throws it"
      (is (= [:anti-symmetric] (mapv :type (v/check kb (list atOrAbove 2 1) U))))
      (is (= :anti-symmetric (ex-type #(v/assert kb (list atOrAbove 2 1) U)))))
    (testing "under either policy — a non-mergeable clash is not arbitrable"
      (doseq [arbitrate? [false true]]
        (binding [checks/*arbitrate-constraints?* arbitrate?]
          (is (= :anti-symmetric (ex-type #(v/assert kb (list atOrAbove 2 1) U)))))))))

(tu/deftest-kb an-antisymmetric-mark-on-a-super-predicate-merges-a-sub-pair
  ;; The mark descends the predicate hierarchy, exactly as functional's does.
  (tu/with-terms [atOrAbove atOrAboveStrict Alice Bob]
    (v/assert kb (list 'genl atOrAboveStrict atOrAbove) U)
    (v/assert kb (list 'antiSymmetric atOrAbove) U)
    (v/assert kb (list atOrAboveStrict Alice Bob) U)
    (v/assert kb (list atOrAboveStrict Bob Alice) U)
    (is (merged? kb Alice Bob U)
        "two sub-predicate tuples are convicted by the super's mark")))

;;; ── antiTransitive: declared, chain conviction deferred ───────────────

(tu/deftest-kb antitransitive-classifies-and-clashes-with-transitive
  ;; The enforced half.  The bare mark carries its classification — (antiTransitive P)
  ;; makes P a binaryPredicate — and declaring the same predicate transitive too is a
  ;; direct disjoint membership clash refused at the door under :refuse.
  (tu/with-terms [flowsInto]
    (v/assert kb (list 'antiTransitive flowsInto) U)
    (testing "the mark classifies it as a binaryPredicate"
      (is (v/ask? kb (list 'binaryPredicate flowsInto) U)))
    (testing "and declaring it transitive too is refused — no predicate is both"
      (is (= [:disjoint] (mapv :type (v/check kb (list 'transitive flowsInto) U))))
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list 'transitive flowsInto) U))))))

(tu/deftest-kb the-antitransitive-chain-conviction-is-deferred
  ;; The honest limit: a two-step chain does NOT yet make the direct step contradictory.
  ;; Pinning it here means the day the settle machinery grows a three-party nogood, this
  ;; test flips and is updated deliberately rather than silently.
  (tu/with-terms [parentOf Alice Bob Carol]
    (v/assert kb (list 'antiTransitive parentOf) U)
    (v/assert kb (list parentOf Alice Bob) U)
    (v/assert kb (list parentOf Bob Carol) U)
    (testing "the direct step is admitted — the chain nogood is not formed"
      (is (v/assert kb (list parentOf Alice Carol) U)))))

;;; ── equivalenceRelation: three marks, no engine code ──────────────────

(tu/deftest-kb an-equivalence-relation-derives-symmetric-transitive-and-reflexive
  (tu/with-terms [sameAgeAs]
    (v/assert kb (list 'equivalenceRelation sameAgeAs) U)
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
    (let [decl (v/assert kb (list 'equivalenceRelation sameAgeAs) U)]
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
    (testing "classified as both, via (genl asymmetric irreflexive/antiSymmetric)"
      (is (v/ask? kb (list 'irreflexive tallerThan) U))
      (is (v/ask? kb (list 'antiSymmetric tallerThan) U)))
    (testing "but the classification does not enforce — the self tuple is still admitted"
      (tu/with-terms [Giant]
        (is (v/assert kb (list tallerThan Giant Giant) U))
        (is (v/ask? kb (list tallerThan Giant Giant) U))))))

(tu/deftest-kb symmetric-and-asymmetric-are-disjoint
  ;; `(disjoint symmetric asymmetric)` on the bare marks: a direct membership in the second
  ;; clashes with the first and is refused at the door under :refuse.
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
    (v/assert kb (list 'equivalenceRelation sameAgeAs) U)
    (is (v/ask? kb (list 'binaryPredicate sameAgeAs) U))
    (testing "carrying the three marks it stands in for"
      (is (v/ask? kb (list 'symmetric sameAgeAs) U))
      (is (v/ask? kb (list 'transitive sameAgeAs) U))
      (is (v/ask? kb (list 'reflexive sameAgeAs) U)))))

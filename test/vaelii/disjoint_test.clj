;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.disjoint-test
  "disjoint and disjointMetatype, and the contradiction detection they drive."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(tu/deftest-kb disjoint-blocks-conflicting-membership
  (let [dog (tu/tmp-type) cat (tu/tmp-type)
        muffet (tu/tmp-ind) whiskers (tu/tmp-ind)]
    ;; the declaration constrains where it is visible, so the asserting context is
    ;; wired below it — the same wiring the starter's spindle gives every real one
    (v/assert kb (list 'genlCx 'CxNaturalWorld 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'disjoint dog cat) 'CxUniverse)
    (v/assert kb (list dog muffet) 'CxNaturalWorld)
    (testing "the same individual can't take a disjoint type"
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list cat muffet) 'CxNaturalWorld))))
    (testing "a compatible individual is unaffected"
      (is (v/assert kb (list cat whiskers) 'CxNaturalWorld)))))

(tu/deftest-kb disjointness-inherited-through-genl
  (let [dog (tu/tmp-type) mammal (tu/tmp-type)
        trout (tu/tmp-type) fish (tu/tmp-type) muffet (tu/tmp-ind)]
    (v/assert kb (list 'genlCx 'CxNaturalWorld 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genl dog mammal) 'CxUniverse)
    (v/assert kb (list 'genl trout fish) 'CxUniverse)
    (v/assert kb (list 'disjoint mammal fish) 'CxUniverse)
    (v/assert kb (list dog muffet) 'CxNaturalWorld)
    (testing "subtypes of disjoint types are disjoint"
      (is (v/disjoint? kb dog trout))
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list trout muffet) 'CxNaturalWorld))))))

(tu/deftest-kb disjoint-type-makes-members-disjoint
  (let [animalSpecies (tu/tmp-pred)
        dog (tu/tmp-type) cat (tu/tmp-type) fish (tu/tmp-type) muffet (tu/tmp-ind)]
    (v/assert kb (list 'genlCx 'CxNaturalWorld 'CxUniverse) 'CxUniverse)
    (v/assert kb (list animalSpecies dog) 'CxUniverse)
    (v/assert kb (list animalSpecies cat) 'CxUniverse)
    (v/assert kb (list 'disjointMetatype animalSpecies) 'CxUniverse)   ; members become pairwise disjoint
    (v/assert kb (list dog muffet) 'CxNaturalWorld)
    (testing "members of a disjoint metatype are disjoint"
      (is (v/disjoint? kb dog cat))
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list cat muffet) 'CxNaturalWorld))))
    (testing "a member added after the declaration is also disjoint"
      (v/assert kb (list animalSpecies fish) 'CxUniverse)
      (is (v/disjoint? kb dog fish)))))

(tu/deftest-kb a-metatype-separates-predicates-not-only-individuals
  ;; the definitional checks admit any term, so the predicate meta-ontology is
  ;; enforced the way the domain is — this is what makes relationKind bite
  (let [kind (tu/tmp-pred) instanceKind (tu/tmp-type) typeKind (tu/tmp-type)
        rel (tu/tmp-pred) other (tu/tmp-pred)]
    (v/assert kb (list 'genl instanceKind 'predicate) 'CxUniverse)
    (v/assert kb (list 'genl typeKind 'predicate) 'CxUniverse)
    (v/assert kb (list kind instanceKind) 'CxUniverse)
    (v/assert kb (list kind typeKind) 'CxUniverse)
    (v/assert kb (list 'disjointMetatype kind) 'CxUniverse)
    (v/assert kb (list instanceKind rel) 'CxUniverse)
    (testing "one predicate cannot take both kinds"
      (is (v/disjoint? kb instanceKind typeKind))
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list typeKind rel) 'CxUniverse))))
    (testing "a different predicate is unaffected"
      (is (v/assert kb (list typeKind other) 'CxUniverse)))))

(tu/deftest-kb argisa-constrains-a-predicate-valued-position
  ;; (argIsa typeToInstancePred 1 typeRelationPredicate) is only enforceable because
  ;; the argument check reaches past CapitalCamelCase individuals
  (let [typeKind (tu/tmp-type) otherKind (tu/tmp-type) link (tu/tmp-pred)
        typeLevel (tu/tmp-pred) instanceLevel (tu/tmp-pred) unclassified (tu/tmp-pred)]
    (v/assert kb (list 'genl typeKind 'thing) 'CxUniverse)
    (v/assert kb (list 'genl otherKind 'thing) 'CxUniverse)
    (v/assert kb (list 'argIsa link 1 typeKind) 'CxUniverse)
    (v/assert kb (list typeKind typeLevel) 'CxUniverse)
    (v/assert kb (list otherKind unclassified) 'CxUniverse)
    (testing "a correctly classified predicate satisfies the constraint"
      (is (v/assert kb (list link typeLevel instanceLevel) 'CxUniverse)))
    (testing "a predicate typed as something else violates it"
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list link unclassified instanceLevel) 'CxUniverse))))
    (testing "open-world survives: a predicate with no type at all cannot violate"
      (is (v/assert kb (list link (tu/tmp-pred) instanceLevel) 'CxUniverse)))))

;;; ── the reach of a disjointness: exactly its declaration's visibility ──

(tu/deftest-kb a-disjointness-counts-only-where-its-declaration-is-visible
  ;; The OpenCyc shape, now answered the way Cyc answers it: the context cone is
  ;; applied at lookup, so a `(disjoint …)` stated in one context separates the
  ;; pair exactly where that statement is visible.  Cyc states `(disjointWith
  ;; #$Place #$Agent-Generic)` in PhysicalGeographyMt alone, and separately makes a
  ;; city both a place and (via GeopoliticalEntity, an Organization) an agent — and
  ;; stays consistent, because the disjointness and the full subsumption path never
  ;; coexist in any one context's cone.  A sibling context that cannot see the
  ;; declaration is not constrained by it; the unscoped read still reports every
  ;; declaration in the KB, which is what a global auditor wants.
  (tu/with-terms [a_place an_agent a_city CxPhysicalGeography CxGeography
                  Delhi Cairo Rome]
    (v/assert kb (list 'genl a_place 'thing) 'CxUniverse)
    (v/assert kb (list 'genl an_agent 'thing) 'CxUniverse)
    (v/assert kb (list 'genl a_city a_place) 'CxUniverse)

    ;; two contexts that cannot see each other
    (v/assert kb (list 'genlCx CxPhysicalGeography 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxGeography 'CxUniverse) 'CxUniverse)
    (is (not (v/sees? kb CxGeography CxPhysicalGeography)))

    ;; the disjointness is stated in one of them only
    (v/assert kb (list 'disjoint a_place an_agent) CxPhysicalGeography)

    (testing "it holds where its declaration is visible"
      (is (v/disjoint? kb a_place an_agent CxPhysicalGeography)))
    (testing "and not in the sibling, which never said it and cannot see it"
      (is (not (v/disjoint? kb a_place an_agent CxGeography))))
    (testing "the unscoped read still sees every declaration in the KB"
      (is (v/disjoint? kb a_place an_agent)))

    (testing "so the membership admissible where it is stated is admitted"
      (v/assert kb (list a_city Delhi) CxGeography)
      (is (v/assert kb (list an_agent Delhi) CxGeography)
          "Delhi is a city here; the separation was stated elsewhere, out of sight"))

    (testing "while the declaring context still refuses its own"
      (v/assert kb (list a_city Cairo) CxPhysicalGeography)
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list an_agent Cairo) CxPhysicalGeography))))

    (testing "retracting the one supporter releases the declaring context too"
      ;; refcounting is orthogonal to scoping: one supporter, so retraction tears
      ;; the cache entry down and the declaring context stops refusing
      (v/retract! kb (v/handle-of kb (list 'disjoint a_place an_agent) CxPhysicalGeography))
      (is (not (v/disjoint? kb a_place an_agent)))
      (v/assert kb (list a_city Rome) CxPhysicalGeography)
      (is (v/assert kb (list an_agent Rome) CxPhysicalGeography)))))

;;; ── which context may hold the conflicting membership ────────────────

;; The check has two halves, both context-scoped, and a three-context lattice is what
;; pins each.  Two incomparable specifics under one general:
;;
;;      CxUniverse
;;            │
;;         CxC
;;         ╱      ╲
;;   CxA    CxB
;;
;; `(disjoint t1 t2)` in A alone; the two halves are then
;;   - **is the pair disjoint?** — the declaration (and any genl edge the
;;     disjointness closes under) must be visible from the asserting context;
;;   - **does X already hold the other type?** — `types-of`, filtered by the same
;;     genlCx up-closure.
;; So the declaration's context and the membership's context are both decisive: a
;; context is only ever refused on grounds it can see.

(defn- assert-outcome
  "`:ok`, or the `:type` of the refusal — so a case reads as a value rather than as
  the presence or absence of a throw."
  [kb sentence context]
  (try (v/assert kb sentence context) :ok
       (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))

(tu/deftest-kb which-of-three-contexts-admits-the-conflicting-membership
  (tu/with-terms [CxA CxB CxC t1 t2 Pip Quo]
    (v/assert kb (list 'genl t1 'thing) 'CxUniverse)
    (v/assert kb (list 'genl t2 'thing) 'CxUniverse)
    (v/assert kb (list 'genlCx CxC 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxA CxC) 'CxUniverse)
    (v/assert kb (list 'genlCx CxB CxC) 'CxUniverse)
    (v/assert kb (list 'disjoint t1 t2) CxA)

    (testing "the lattice: siblings see neither each other nor themselves from above"
      (is (not (v/sees? kb CxA CxB)))
      (is (not (v/sees? kb CxB CxA)))
      (is (not (v/sees? kb CxC CxA)))
      (is (v/sees? kb CxA CxC))
      (is (v/sees? kb CxC 'CxUniverse)))

    (testing "the membership up in CxUniverse: only A refuses"
      ;; every context in the lattice sees CxUniverse, so every one of them reads
      ;; the (t1 Pip) that could make (t2 Pip) a violation — but only A can see the
      ;; disjointness, stated in A itself, so B and C are no longer refused on a
      ;; declaration made below C in a sibling of B
      (v/assert kb (list t1 Pip) 'CxUniverse)
      (is (= {CxA :disjoint, CxB :ok, CxC :ok}
             (into {} (for [c [CxA CxB CxC]]
                        [c (assert-outcome kb (list t2 Pip) c)])))))

    (testing "the membership down in A: only A is refused"
      ;; the same disjointness, the same three contexts — only the membership moved,
      ;; and it moved out of B's and C's sight
      (v/assert kb (list t1 Quo) CxA)
      (is (= {CxA :disjoint, CxB :ok, CxC :ok}
             (into {} (for [c [CxA CxB CxC]]
                        [c (assert-outcome kb (list t2 Quo) c)])))))))

(tu/deftest-kb a-general-context-may-be-given-what-a-specific-one-forbids
  ;; The corollary, and the sharp edge: the check runs once, where the sentence is
  ;; written, against what *that* context can see.  Writing the conflicting
  ;; membership into the more general context is admitted — C cannot see A — and the
  ;; clash that creates *for A* is a real contradiction A can see whole.  Seeing a
  ;; clash and being blamed for one are different questions: the writer is refused
  ;; only on grounds it can see, and the joint question is answered by `settle`'s
  ;; exposure pass, as a `:disjoint` ledger entry naming where the clash is visible
  ;; from.  This test is the acceptance criterion for that split.
  (tu/with-terms [CxA CxC t1 t2 Pip]
    (v/assert kb (list 'genl t1 'thing) 'CxUniverse)
    (v/assert kb (list 'genl t2 'thing) 'CxUniverse)
    (v/assert kb (list 'genlCx CxC 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxA CxC) 'CxUniverse)
    (v/assert kb (list 'disjoint t1 t2) 'CxUniverse)
    (v/assert kb (list t1 Pip) CxA)

    (testing "admitted in the general context, which cannot see the specific one"
      (is (= :ok (assert-outcome kb (list t2 Pip) CxC))))

    (testing "and A now reads both halves of a pair it is the only context to refuse"
      (is (= #{t1 t2} (set (v/types-of kb Pip CxA))))
      (is (= :disjoint (assert-outcome kb (list t2 Pip) CxA))
          "stating it in A directly is still refused — only the route through C is open"))

    (testing "the ledger reports the clash, naming the context that sees it"
      (let [vs (v/violations kb)]
        (is (= [:disjoint] (mapv :violation vs)))
        (let [d (:detail (first vs))]
          (is (= Pip (:term d)))
          (is (= #{CxA} (:visible-from d)))
          (is (= #{t1 t2} (into #{} (map first) (:held d)))))))

    (testing "exposure is a report, not an arbitration: belief is untouched"
      (is (empty? (v/conflicts kb)))
      (is (empty? (v/contradictions kb))))))

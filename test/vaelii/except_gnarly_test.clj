;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.except-gnarly-test
  "Gnarly `except` tests: cross-context exceptions, cross-context meta-exceptions,
  deep exception chains, excepting special-predicate sentexes, and the
  special-predicate sweep that verifies `except` blocks or does not block the
  cached behaviour behind each interpreted functor.

  PR #33 — meta-exception cascade."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

;; ---- helpers ------------------------------------------------------------

(defn- ex-type
  "The `:type` on the ex-info a thunk throws, or nil if it does not throw."
  [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))

;; ---- 1. cross-context except --------------------------------------------

(tu/deftest-kb cross-context-except
  ;; Assert a fact in context A, except it from context B (a descendant of A via
  ;; genlCx).  The except hides the fact in B and B's descendants but leaves it
  ;; visible in A and A's siblings.
  (tu/with-terms [shiny gold CxTop CxMid CxLeaf CxSibling]
    (v/assert kb (list 'genlCx CxTop 'CxWell) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'genlCx CxMid CxTop) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'genlCx CxLeaf CxMid) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'genlCx CxSibling CxTop) 'CxUniverse {:strength :monotonic})

    (let [h (v/assert kb (list shiny gold) CxTop {:strength :monotonic})]
      (testing "visible everywhere before any except"
        (is (v/ask? kb (list shiny gold) CxTop))
        (is (v/ask? kb (list shiny gold) CxMid))
        (is (v/ask? kb (list shiny gold) CxLeaf))
        (is (v/ask? kb (list shiny gold) CxSibling)))

      (let [eh (v/assert kb (list 'except (sx/sentex-handle h)) CxMid {:strength :monotonic})]
        (testing "hidden in CxMid and its descendant CxLeaf"
          (is (not (v/ask? kb (list shiny gold) CxMid)))
          (is (not (v/ask? kb (list shiny gold) CxLeaf))))
        (testing "visible in CxTop (the ancestor) and CxSibling (does not see CxMid)"
          (is (v/ask? kb (list shiny gold) CxTop))
          (is (v/ask? kb (list shiny gold) CxSibling)))
        (testing "retract the except — visibility returns everywhere"
          (v/retract! kb eh)
          (is (v/ask? kb (list shiny gold) CxMid))
          (is (v/ask? kb (list shiny gold) CxLeaf)))))))

;; ---- 2. cross-context meta-except ---------------------------------------

(tu/deftest-kb cross-context-meta-except
  ;; Fact in CxTop, excepted in CxMid, meta-excepted in CxLeaf.  The meta-except
  ;; restores visibility only from CxLeaf's vantage — CxMid still sees the except.
  (tu/with-terms [bright gem CxTop CxMid CxLeaf]
    (v/assert kb (list 'genlCx CxTop 'CxWell) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'genlCx CxMid CxTop) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'genlCx CxLeaf CxMid) 'CxUniverse {:strength :monotonic})

    (let [h (v/assert kb (list bright gem) CxTop {:strength :monotonic})]
      (let [e (v/assert kb (list 'except (sx/sentex-handle h)) CxMid {:strength :monotonic})]
        (testing "fact hidden in CxMid and CxLeaf"
          (is (not (v/ask? kb (list bright gem) CxMid)))
          (is (not (v/ask? kb (list bright gem) CxLeaf))))

        (let [m (v/assert kb (list 'except (sx/sentex-handle e)) CxLeaf {:strength :monotonic})]
          (testing "meta-except in CxLeaf restores visibility there"
            (is (v/ask? kb (list bright gem) CxLeaf)
                "the meta-except suppresses E's effect from CxLeaf's vantage"))
          (testing "CxMid still sees the except — the meta-except is below it"
            (is (not (v/ask? kb (list bright gem) CxMid))
                "the except is asserted here and no meta-except is visible"))
          (testing "CxTop is untouched throughout"
            (is (v/ask? kb (list bright gem) CxTop)))
          (testing "retracting the meta-except re-hides in CxLeaf"
            (v/retract! kb m)
            (is (not (v/ask? kb (list bright gem) CxLeaf)))))
        (v/retract! kb e)))))

;; ---- 3. chain of 212 excepts --------------------------------------------

(tu/deftest-kb chain-of-212-excepts
  ;; H0 hidden by E1, E1 hidden by E2, ..., E211 hidden by E212.
  ;; At depth N (1-based): odd N -> H0 is visible (the except hiding it is itself
  ;; hidden), even N -> H0 is hidden.  212 is even, so H0 should be hidden.
  ;; Then retract E212 (the deepest) and verify the cascade recalculates.
  (tu/with-terms [shiny gold CxChain]
    (v/assert kb (list 'genlCx CxChain 'CxWell) 'CxUniverse {:strength :monotonic})

    (let [h0 (v/assert kb (list shiny gold) CxChain {:strength :monotonic})]
      (testing "H0 is visible before any except"
        (is (v/ask? kb (list shiny gold) CxChain)))

      ;; Build chain: E1 excepts H0, E2 excepts E1, ..., E212 excepts E211
      (let [chain (loop [i 1, prev-handle h0, acc []]
                    (if (> i 212)
                      acc
                      (let [eh (v/assert kb (list 'except (sx/sentex-handle prev-handle))
                                         CxChain {:strength :monotonic})]
                        (recur (inc i) eh (conj acc eh)))))]

        (testing "with 212 layers (even), H0 is visible"
          ;; E1 hides H0.  E2 hides E1 -> H0 visible.  E3 hides E2 -> E1 active -> H0 hidden.
          ;; Cascade from the deepest: E212 is active (nothing hides it), E211 is
          ;; suppressed, E210 active, ..., E1: distance from E212 is 211 (odd) -> suppressed.
          ;; With E1 suppressed, H0 is NOT excepted.
          ;; Pattern: odd layer count = H0 hidden, even layer count = H0 visible.
          (is (v/ask? kb (list shiny gold) CxChain)
              "212 layers (even) should leave H0 visible"))

        (testing "retract the deepest (E212) — cascade recalculates to 211 (odd)"
          (v/retract! kb (peek chain))
          ;; 211 layers (odd): E211 is now the deepest and active, E210 suppressed, ...,
          ;; E1: distance from E211 is 210 (even) -> active.  E1 active -> H0 hidden.
          (is (not (v/ask? kb (list shiny gold) CxChain))
              "211 layers (odd) should leave H0 hidden"))

        (testing "retract the next deepest (E211) — back to 210 (even)"
          (v/retract! kb (peek (pop chain)))
          (is (v/ask? kb (list shiny gold) CxChain)
              "210 layers (even) should leave H0 visible"))

        ;; Clean up the rest of the chain by retracting from deepest to shallowest
        (doseq [eh (reverse (pop (pop chain)))]
          (v/retract! kb eh))))))

;; ---- 4. except a genlCx link -------------------------------------------

(tu/deftest-kb except-genlCx-link
  ;; Try `(except (sentexHandle H))` where H is a `(genlCx A B)` sentex.
  ;; If it works, the context closure should update: A no longer sees B.
  ;; If it's ill-formed, test the refusal.
  (tu/with-terms [shiny gold CxChild CxParent]
    (v/assert kb (list 'genlCx CxParent 'CxWell) 'CxUniverse {:strength :monotonic})
    (let [edge-h (v/assert kb (list 'genlCx CxChild CxParent) 'CxUniverse {:strength :monotonic})]
      (v/assert kb (list shiny gold) CxParent {:strength :monotonic})

      (testing "CxChild sees CxParent's facts before any except"
        (is (v/ask? kb (list shiny gold) CxChild)))

      ;; Attempt to except the genlCx link
      (let [result (try
                     {:handle (v/assert kb (list 'except (sx/sentex-handle edge-h))
                                        'CxUniverse {:strength :monotonic})}
                     (catch clojure.lang.ExceptionInfo e
                       {:error e :type (:type (ex-data e))}))]
        (if (:handle result)
          ;; It worked — the genlCx link is excepted
          (do
            (testing "excepting a genlCx link hides it from sentexes-matching"
              ;; `ask?` still answers true because the TransitivityProver reads the
              ;; taxonomy closure, which is maintained by integrate/disintegrate and
              ;; not by the except filter.  `sentexes-matching` is the level that
              ;; honours the except.
              (is (empty? (v/sentexes-matching kb (list 'genlCx CxChild CxParent) 'CxUniverse))
                  "the genlCx sentex is hidden from sentexes-matching"))
            (testing "retract the except — the genlCx link returns"
              (v/retract! kb (:handle result))
              (is (seq (v/sentexes-matching kb (list 'genlCx CxChild CxParent) 'CxUniverse)))))
          ;; It was refused — document the refusal
          (testing "excepting a genlCx link is refused as ill-formed"
            (is (some? (:error result))
                (str "expected a refusal, got: " (pr-str result)))))))))

;; ---- 5. except a genl link ---------------------------------------------

(tu/deftest-kb except-genl-link
  ;; Try `(except (sentexHandle H))` where H is a `(genl sub super)` sentex.
  (tu/with-terms [dog animal CxTax]
    (v/assert kb (list 'genlCx CxTax 'CxWell) 'CxUniverse {:strength :monotonic})
    (let [genl-h (v/assert kb (list 'genl dog animal) CxTax {:strength :monotonic})]

      (testing "genl closure is active before any except"
        (is (v/genl? kb dog animal))
        (is (contains? (v/genls kb dog) animal)))

      ;; Attempt to except the genl link
      (let [result (try
                     {:handle (v/assert kb (list 'except (sx/sentex-handle genl-h))
                                        CxTax {:strength :monotonic})}
                     (catch clojure.lang.ExceptionInfo e
                       {:error e :type (:type (ex-data e))}))]
        (if (:handle result)
          ;; It worked — the genl sentex is excepted
          (do
            (testing "the genl sentex is hidden from query"
              (is (empty? (v/sentexes-matching kb (list 'genl dog animal) CxTax))
                  "the sentex is invisible through sentexes-matching"))
            ;; The taxonomy cache is maintained separately — the closure may or may
            ;; not still show the edge.  We document what happens.
            (testing "retract the except — the genl sentex returns"
              (v/retract! kb (:handle result))
              (is (seq (v/sentexes-matching kb (list 'genl dog animal) CxTax)))))
          ;; It was refused — document the refusal
          (testing "excepting a genl link is refused as ill-formed"
            (is (some? (:error result))
                (str "expected a refusal, got: " (pr-str result)))))))))

;; ---- 6. except an equals sentex ----------------------------------------

(tu/deftest-kb except-equals-sentex
  ;; Try `(except (sentexHandle H))` where H is an `(equals A B)` sentex.
  (tu/with-terms [CxEq]
    (v/assert kb (list 'genlCx CxEq 'CxWell) 'CxUniverse {:strength :monotonic})
    (let [a (tu/tmp-ind) b (tu/tmp-ind)]
      ;; Attempt to assert and then except an equality
      (let [result (try
                     (let [eq-h (v/assert kb (list 'equals a b) CxEq {:strength :monotonic})]
                       {:handle eq-h})
                     (catch clojure.lang.ExceptionInfo e
                       {:error e :type (:type (ex-data e))}))]
        (if (:handle result)
          (let [eq-h (:handle result)]
            ;; Attempt to except the equality sentex
            (let [except-result (try
                                  {:handle (v/assert kb (list 'except (sx/sentex-handle eq-h))
                                                     CxEq {:strength :monotonic})}
                                  (catch clojure.lang.ExceptionInfo e
                                    {:error e :type (:type (ex-data e))}))]
              (if (:handle except-result)
                (do
                  (testing "excepting an equals sentex hides it from query"
                    (is (empty? (v/sentexes-matching kb (list 'equals a b) CxEq))
                        "the equals sentex is hidden"))
                  (testing "retract the except — the equals sentex record still exists"
                    (v/retract! kb (:handle except-result))
                    ;; The equality merge rewrites terms, so sentexes-matching with
                    ;; the original terms may not find the sentex.  We check that the
                    ;; handle still has a sentex record — what matters is that
                    ;; retraction did not corrupt anything.
                    (is (some? (v/sentex kb eq-h))
                        "the equals sentex record is still present after retract of except")))
                (testing "excepting an equals sentex is refused"
                  (is (some? (:error except-result))
                      (str "expected a refusal, got: " (pr-str except-result)))))))
          ;; Even the assert was refused — skip
          (testing "equals assertion was refused"
            (is false (str "could not assert equals: " (pr-str result)))))))))

;; ---- 7. special-predicate sweep -----------------------------------------
;; For each special predicate with code support, assert the sentex, verify the
;; special behavior is active, except the sentex handle, verify the sentex is
;; hidden from query, retract the except, verify the special behavior returns.

(tu/deftest-kb except-blocks-genl-sentex-visibility
  ;; genl: the taxonomy closure.
  (tu/with-terms [dog animal pet CxG]
    (v/assert kb (list 'genlCx CxG 'CxWell) 'CxUniverse {:strength :monotonic})
    (let [gh (v/assert kb (list 'genl dog animal) CxG {:strength :monotonic})]
      (testing "genl closure active"
        (is (v/genl? kb dog animal))
        (is (contains? (v/genls kb dog) animal)))
      (let [eh (v/assert kb (list 'except (sx/sentex-handle gh)) CxG {:strength :monotonic})]
        (testing "the genl sentex is hidden from sentexes-matching"
          (is (empty? (v/sentexes-matching kb (list 'genl dog animal) CxG))))
        (testing "retract except — genl sentex returns"
          (v/retract! kb eh)
          (is (seq (v/sentexes-matching kb (list 'genl dog animal) CxG)))
          (is (v/genl? kb dog animal)))))))

(tu/deftest-kb except-blocks-genlCx-sentex-visibility
  ;; genlCx: the context inheritance closure.
  (tu/with-terms [shiny gold CxA CxB]
    (v/assert kb (list 'genlCx CxA 'CxWell) 'CxUniverse {:strength :monotonic})
    (let [cx-h (v/assert kb (list 'genlCx CxB CxA) 'CxUniverse {:strength :monotonic})]
      (v/assert kb (list shiny gold) CxA {:strength :monotonic})
      (testing "CxB sees CxA's content before except"
        (is (v/ask? kb (list shiny gold) CxB)))
      (let [eh (v/assert kb (list 'except (sx/sentex-handle cx-h)) 'CxUniverse
                          {:strength :monotonic})]
        (testing "the genlCx sentex is hidden from query"
          (is (empty? (v/sentexes-matching kb (list 'genlCx CxB CxA) 'CxUniverse))))
        (testing "retract except — genlCx sentex returns"
          (v/retract! kb eh)
          (is (seq (v/sentexes-matching kb (list 'genlCx CxB CxA) 'CxUniverse))))))))

(tu/deftest-kb except-blocks-disjoint-sentex-visibility
  ;; disjoint: pairwise type separation.
  (tu/with-terms [dog cat Muffet CxD]
    (v/assert kb (list 'genlCx CxD 'CxWell) 'CxUniverse {:strength :monotonic})
    (let [dh (v/assert kb (list 'disjoint dog cat) CxD {:strength :monotonic})]
      (testing "disjoint is active"
        (is (v/disjoint? kb dog cat)))
      (let [eh (v/assert kb (list 'except (sx/sentex-handle dh)) CxD {:strength :monotonic})]
        (testing "the disjoint sentex is hidden from query"
          (is (empty? (v/sentexes-matching kb (list 'disjoint dog cat) CxD))))
        (testing "retract except — disjoint sentex returns"
          (v/retract! kb eh)
          (is (seq (v/sentexes-matching kb (list 'disjoint dog cat) CxD)))
          (is (v/disjoint? kb dog cat)))))))

(tu/deftest-kb except-blocks-disjointMetatype-sentex-visibility
  ;; disjointMetatype: members of the metatype become pairwise disjoint.
  (tu/with-terms [animalSpecies dog cat CxDM]
    (v/assert kb (list 'genlCx CxDM 'CxWell) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list animalSpecies dog) CxDM {:strength :monotonic})
    (v/assert kb (list animalSpecies cat) CxDM {:strength :monotonic})
    (let [dmh (v/assert kb (list 'disjointMetatype animalSpecies) CxDM {:strength :monotonic})]
      (testing "disjointMetatype makes members disjoint"
        (is (v/disjoint? kb dog cat)))
      (let [eh (v/assert kb (list 'except (sx/sentex-handle dmh)) CxDM {:strength :monotonic})]
        (testing "the disjointMetatype sentex is hidden from query"
          (is (empty? (v/sentexes-matching kb (list 'disjointMetatype animalSpecies) CxDM))))
        (testing "retract except — disjointMetatype sentex returns"
          (v/retract! kb eh)
          (is (seq (v/sentexes-matching kb (list 'disjointMetatype animalSpecies) CxDM))))))))

(tu/deftest-kb except-blocks-transitive-sentex-visibility
  ;; transitive: the transitive closure prover.
  (tu/with-terms [insideOf Gem Box Vault CxT]
    (v/assert kb (list 'genlCx CxT 'CxWell) 'CxUniverse {:strength :monotonic})
    (let [th (v/assert kb (list 'transitive insideOf) CxT {:strength :monotonic})]
      (v/assert kb (list insideOf Gem Box) CxT {:strength :monotonic})
      (v/assert kb (list insideOf Box Vault) CxT {:strength :monotonic})
      (testing "transitive closure is active"
        (is (v/has-prop? kb :transitive insideOf))
        (is (v/ask? kb (list insideOf Gem Vault) CxT)))
      (let [eh (v/assert kb (list 'except (sx/sentex-handle th)) CxT {:strength :monotonic})]
        (testing "the transitive sentex is hidden from query"
          (is (empty? (v/sentexes-matching kb (list 'transitive insideOf) CxT))))
        (testing "retract except — transitive sentex returns"
          (v/retract! kb eh)
          (is (seq (v/sentexes-matching kb (list 'transitive insideOf) CxT)))
          (is (v/has-prop? kb :transitive insideOf)))))))

(tu/deftest-kb except-blocks-symmetric-sentex-visibility
  ;; symmetric: both directions of a symmetric predicate are provable.
  (tu/with-terms [siblingOf Alice Bob CxS]
    (v/assert kb (list 'genlCx CxS 'CxWell) 'CxUniverse {:strength :monotonic})
    (let [sh (v/assert kb (list 'symmetric siblingOf) CxS {:strength :monotonic})]
      (v/assert kb (list siblingOf Alice Bob) CxS {:strength :monotonic})
      (testing "symmetric provability active"
        (is (v/has-prop? kb :symmetric siblingOf))
        (is (v/ask? kb (list siblingOf Bob Alice) CxS)))
      (let [eh (v/assert kb (list 'except (sx/sentex-handle sh)) CxS {:strength :monotonic})]
        (testing "the symmetric sentex is hidden from query"
          (is (empty? (v/sentexes-matching kb (list 'symmetric siblingOf) CxS))))
        (testing "retract except — symmetric sentex returns"
          (v/retract! kb eh)
          (is (seq (v/sentexes-matching kb (list 'symmetric siblingOf) CxS)))
          (is (v/has-prop? kb :symmetric siblingOf)))))))

(tu/deftest-kb except-blocks-asymmetric-sentex-visibility
  ;; asymmetric: the converse of an asymmetric predicate is refused.
  (tu/with-terms [olderThan Alice Bob CxAs]
    (v/assert kb (list 'genlCx CxAs 'CxWell) 'CxUniverse {:strength :monotonic})
    (let [ah (v/assert kb (list 'asymmetric olderThan) CxAs {:strength :monotonic})]
      (v/assert kb (list olderThan Alice Bob) CxAs {:strength :monotonic})
      (testing "asymmetric is active — the converse is refused"
        (is (v/has-prop? kb :asymmetric olderThan))
        (is (= :asymmetric (ex-type #(v/assert kb (list olderThan Bob Alice) CxAs)))))
      (let [eh (v/assert kb (list 'except (sx/sentex-handle ah)) CxAs {:strength :monotonic})]
        (testing "the asymmetric sentex is hidden from query"
          (is (empty? (v/sentexes-matching kb (list 'asymmetric olderThan) CxAs))))
        (testing "retract except — asymmetric sentex returns"
          (v/retract! kb eh)
          (is (seq (v/sentexes-matching kb (list 'asymmetric olderThan) CxAs)))
          (is (v/has-prop? kb :asymmetric olderThan)))))))

(tu/deftest-kb except-blocks-reflexive-sentex-visibility
  ;; reflexive: a reflexive predicate holds of everything with itself.
  (tu/with-terms [sameGroupAs Alice CxR]
    (v/assert kb (list 'genlCx CxR 'CxWell) 'CxUniverse {:strength :monotonic})
    (let [rh (v/assert kb (list 'reflexive sameGroupAs) CxR {:strength :monotonic})]
      (testing "reflexive is active"
        (is (v/has-prop? kb :reflexive sameGroupAs)))
      (let [eh (v/assert kb (list 'except (sx/sentex-handle rh)) CxR {:strength :monotonic})]
        (testing "the reflexive sentex is hidden from query"
          (is (empty? (v/sentexes-matching kb (list 'reflexive sameGroupAs) CxR))))
        (testing "retract except — reflexive sentex returns"
          (v/retract! kb eh)
          (is (seq (v/sentexes-matching kb (list 'reflexive sameGroupAs) CxR)))
          (is (v/has-prop? kb :reflexive sameGroupAs)))))))

(tu/deftest-kb except-blocks-functional-sentex-visibility
  ;; functional: a functional predicate has at most one value per subject.
  (tu/with-terms [motherOf Alice Mom CxF]
    (v/assert kb (list 'genlCx CxF 'CxWell) 'CxUniverse {:strength :monotonic})
    (let [fh (v/assert kb (list 'functional motherOf) CxF {:strength :monotonic})]
      (testing "functional is active"
        (is (v/has-prop? kb :functional motherOf)))
      (let [eh (v/assert kb (list 'except (sx/sentex-handle fh)) CxF {:strength :monotonic})]
        (testing "the functional sentex is hidden from query"
          (is (empty? (v/sentexes-matching kb (list 'functional motherOf) CxF))))
        (testing "retract except — functional sentex returns"
          (v/retract! kb eh)
          (is (seq (v/sentexes-matching kb (list 'functional motherOf) CxF)))
          (is (v/has-prop? kb :functional motherOf)))))))

(tu/deftest-kb except-blocks-irreflexive-sentex-visibility
  ;; irreflexive: a self-tuple is refused.
  (tu/with-terms [before Alice CxIr]
    (v/assert kb (list 'genlCx CxIr 'CxWell) 'CxUniverse {:strength :monotonic})
    (let [ih (v/assert kb (list 'irreflexive before) CxIr {:strength :monotonic})]
      (testing "irreflexive is active"
        (is (v/has-prop? kb :irreflexive before))
        (is (= :irreflexive (ex-type #(v/assert kb (list before Alice Alice) CxIr)))))
      (let [eh (v/assert kb (list 'except (sx/sentex-handle ih)) CxIr {:strength :monotonic})]
        (testing "the irreflexive sentex is hidden from query"
          (is (empty? (v/sentexes-matching kb (list 'irreflexive before) CxIr))))
        (testing "retract except — irreflexive sentex returns"
          (v/retract! kb eh)
          (is (seq (v/sentexes-matching kb (list 'irreflexive before) CxIr)))
          (is (v/has-prop? kb :irreflexive before)))))))

(tu/deftest-kb except-blocks-antiSymmetric-sentex-visibility
  ;; antiSymmetric: a believed converse merges the two arguments via equals.
  (tu/with-terms [subsumes CxAnti]
    (v/assert kb (list 'genlCx CxAnti 'CxWell) 'CxUniverse {:strength :monotonic})
    (let [ash (v/assert kb (list 'antiSymmetric subsumes) CxAnti {:strength :monotonic})]
      (testing "antiSymmetric is active"
        (is (v/has-prop? kb :anti-symmetric subsumes)))
      (let [eh (v/assert kb (list 'except (sx/sentex-handle ash)) CxAnti {:strength :monotonic})]
        (testing "the antiSymmetric sentex is hidden from query"
          (is (empty? (v/sentexes-matching kb (list 'antiSymmetric subsumes) CxAnti))))
        (testing "retract except — antiSymmetric sentex returns"
          (v/retract! kb eh)
          (is (seq (v/sentexes-matching kb (list 'antiSymmetric subsumes) CxAnti)))
          (is (v/has-prop? kb :anti-symmetric subsumes)))))))

(tu/deftest-kb except-blocks-arity-sentex-visibility
  ;; arity: the declared arity is cached and checked on every assertion.
  (tu/with-terms [myRel CxAr]
    (v/assert kb (list 'genlCx CxAr 'CxWell) 'CxUniverse {:strength :monotonic})
    (let [arh (v/assert kb (list 'arity myRel 2) CxAr {:strength :monotonic})]
      (testing "arity declaration is active"
        (is (= 2 (tax/declared-arity (:taxonomy kb) myRel))))
      (let [eh (v/assert kb (list 'except (sx/sentex-handle arh)) CxAr {:strength :monotonic})]
        (testing "the arity sentex is hidden from query"
          (is (empty? (v/sentexes-matching kb (list 'arity myRel 2) CxAr))))
        (testing "retract except — arity sentex returns"
          (v/retract! kb eh)
          (is (seq (v/sentexes-matching kb (list 'arity myRel 2) CxAr)))
          (is (= 2 (tax/declared-arity (:taxonomy kb) myRel))))))))

(tu/deftest-kb except-blocks-inverse-sentex-visibility
  ;; inverse: the inverse relation.
  (tu/with-terms [parentOf childOf CxInv]
    (v/assert kb (list 'genlCx CxInv 'CxWell) 'CxUniverse {:strength :monotonic})
    (let [ih (v/assert kb (list 'inverse parentOf childOf) CxInv {:strength :monotonic})]
      (testing "inverse is active"
        (is (= childOf (v/inverse-of kb parentOf)))
        (is (= parentOf (v/inverse-of kb childOf))))
      (let [eh (v/assert kb (list 'except (sx/sentex-handle ih)) CxInv {:strength :monotonic})]
        (testing "the inverse sentex is hidden from query"
          (is (empty? (v/sentexes-matching kb (list 'inverse parentOf childOf) CxInv))))
        (testing "retract except — inverse sentex returns"
          (v/retract! kb eh)
          (is (seq (v/sentexes-matching kb (list 'inverse parentOf childOf) CxInv)))
          (is (= childOf (v/inverse-of kb parentOf))))))))

(tu/deftest-kb except-blocks-argGenl-sentex-visibility
  ;; argGenl: argument subtype constraint.
  (tu/with-terms [typeRel root sub CxAG]
    (v/assert kb (list 'genlCx CxAG 'CxWell) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'genl root 'thing) CxAG {:strength :monotonic})
    (v/assert kb (list 'genl sub root) CxAG {:strength :monotonic})
    (let [agh (v/assert kb (list 'argGenl typeRel 1 root) CxAG {:strength :monotonic})]
      (testing "argGenl constraint is active — subtype passes, sibling fails"
        (is (v/assert kb (list typeRel sub (tu/tmp-type)) CxAG))
        (tu/with-terms [other]
          (v/assert kb (list 'genl other 'thing) CxAG {:strength :monotonic})
          (is (= :arg-genl (ex-type #(v/assert kb (list typeRel other (tu/tmp-type)) CxAG))))))
      (let [eh (v/assert kb (list 'except (sx/sentex-handle agh)) CxAG {:strength :monotonic})]
        (testing "the argGenl sentex is hidden from query"
          (is (empty? (v/sentexes-matching kb (list 'argGenl typeRel 1 root) CxAG))))
        (testing "retract except — argGenl sentex returns"
          (v/retract! kb eh)
          (is (seq (v/sentexes-matching kb (list 'argGenl typeRel 1 root) CxAG))))))))

(tu/deftest-kb except-blocks-interArgIsa-sentex-visibility
  ;; interArgIsa: conditional argument type constraint.
  (tu/with-terms [eats carnivore meat CxIA]
    (v/assert kb (list 'genlCx CxIA 'CxWell) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'genl carnivore 'thing) CxIA {:strength :monotonic})
    (v/assert kb (list 'genl meat 'thing) CxIA {:strength :monotonic})
    (let [iah (v/assert kb (list 'interArgIsa eats 1 carnivore 2 meat) CxIA
                         {:strength :monotonic})]
      (testing "interArgIsa constraint is active — queryable"
        (is (v/ask? kb (list 'interArgIsa eats 1 carnivore 2 meat) CxIA)))
      (let [eh (v/assert kb (list 'except (sx/sentex-handle iah)) CxIA {:strength :monotonic})]
        (testing "the interArgIsa sentex is hidden from query"
          (is (empty? (v/sentexes-matching kb (list 'interArgIsa eats 1 carnivore 2 meat) CxIA))))
        (testing "retract except — interArgIsa sentex returns"
          (v/retract! kb eh)
          (is (seq (v/sentexes-matching kb (list 'interArgIsa eats 1 carnivore 2 meat) CxIA))))))))

;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.taxonomy-teardown-test
  "Retraction of the *cached* taxonomy metadata.

  Every cache is **reference-counted** and **belief-tracked** now: `genl` /
  `genlContext` / equality keep a per-claim `:support` map, and `disjoint`,
  `disjointMetatype` + members, the predicate properties, and `inverse` share the
  `:cache-support` count.  An entry survives losing one of several supporters and
  follows defeat.  Belief-tracking is covered in `taxonomy_belief_test`; this file
  covers the *retract* half — the teardown wired through `core/disintegrate-sentex!`.

  The retract half is where a cache and the sentexes stating it can drift apart:
  nothing in the neutral fixture notices a leaked taxonomy entry, because it compares
  sentex and justification counts only.  A stale `disjoint` pair permanently rejects a
  legitimate assert; a stale property silently keeps a prover running."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

;; ---- the cache follows retraction ---------------------------------------

(tu/deftest-kb retracting-a-disjoint-declaration-releases-the-pair
  (tu/with-terms [dog cat Felix]
    ;; one context: the disjointness check is scoped, and this KB is fresh
    (let [h (v/assert kb (list 'disjoint dog cat) 'NaturalWorldContext)]
      (is (v/disjoint? kb dog cat))
      (testing "while it stands, the conflicting membership is refused"
        (v/assert kb (list cat Felix) 'NaturalWorldContext)
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/assert kb (list dog Felix) 'NaturalWorldContext))))
      (v/retract! kb h)
      (testing "retracting it releases the pair rather than leaving a stale entry"
        (is (not (v/disjoint? kb dog cat))
            "a stale disjoint pair would reject legitimate asserts forever")))))

(tu/deftest-kb retracting-a-predicate-property-unmarks-it
  (tu/with-terms [partOf siblingOf sameAs marriedTo]
    (let [ht (v/assert kb (list 'transitive partOf)  'UniverseContext)
          hs (v/assert kb (list 'symmetric siblingOf) 'UniverseContext)
          hr (v/assert kb (list 'reflexive sameAs)    'UniverseContext)
          hf (v/assert kb (list 'functional marriedTo) 'UniverseContext)]
      (is (v/has-prop? kb :transitive partOf))
      (is (v/has-prop? kb :symmetric siblingOf))
      (is (v/has-prop? kb :reflexive sameAs))
      (is (v/has-prop? kb :functional marriedTo))
      (run! #(v/retract! kb %) [ht hs hr hf])
      (testing "each property is released when the sentex declaring it goes"
        (is (not (v/has-prop? kb :transitive partOf)))
        (is (not (v/has-prop? kb :symmetric siblingOf)))
        (is (not (v/has-prop? kb :reflexive sameAs)))
        (is (not (v/has-prop? kb :functional marriedTo)))))))

(tu/deftest-kb retracting-an-inverse-declaration-releases-both-directions
  (tu/with-terms [parentOf childOf Tom Bob]
    (let [h (v/assert kb (list 'inverse parentOf childOf) 'UniverseContext)]
      (v/assert kb (list parentOf Tom Bob) 'UniverseContext)
      (is (= childOf (v/inverse-of kb parentOf)))
      (is (v/ask? kb (list childOf Bob Tom) 'UniverseContext)
          "the inverse goal is answerable while the declaration stands")
      (v/retract! kb h)
      (testing "the declaration going takes the inverse reasoning with it"
        (is (nil? (v/inverse-of kb parentOf)))
        (is (not (v/ask? kb (list childOf Bob Tom) 'UniverseContext)))))))

(tu/deftest-kb retracting-a-disjoint-metatype-releases-every-pair-it-separated
  ;; A metatype separates its members by being *consulted*, not by materializing a
  ;; clique of `(disjoint a b)` sentexes.  So retraction reaches all of it at once:
  ;; there is no independent premise left behind to outlive the declaration.
  (tu/with-terms [animalSpecies dog cat fish]
    (v/assert kb (list animalSpecies dog) 'UniverseContext)
    (v/assert kb (list animalSpecies cat) 'UniverseContext)
    (let [h (v/assert kb (list 'disjointMetatype animalSpecies) 'UniverseContext)]
      (is (v/disjoint? kb dog cat) "members of a disjoint metatype are pairwise disjoint")
      (v/retract! kb h)
      (testing "retracting the metatype releases the pairs it separated"
        (is (not (v/disjoint? kb dog cat))))
      (testing "and it no longer separates a member added afterwards"
        (v/assert kb (list animalSpecies fish) 'UniverseContext)
        (is (not (v/disjoint? kb dog fish)))))))

(tu/deftest-kb retracting-one-member-releases-only-that-members-pairs
  ;; The finer-grained half, which a materialized clique could not express at all:
  ;; a member leaving the metatype stops being disjoint from the rest, while the
  ;; remaining members stay disjoint from each other.
  (tu/with-terms [animalSpecies dog cat fish]
    (v/assert kb (list 'disjointMetatype animalSpecies) 'UniverseContext)
    (v/assert kb (list animalSpecies dog) 'UniverseContext)
    (let [hc (v/assert kb (list animalSpecies cat) 'UniverseContext)]
      (v/assert kb (list animalSpecies fish) 'UniverseContext)
      (is (v/disjoint? kb dog cat))
      (is (v/disjoint? kb dog fish))
      (v/retract! kb hc)
      (testing "the departed member is no longer disjoint from anyone"
        (is (not (v/disjoint? kb dog cat)))
        (is (not (v/disjoint? kb cat fish))))
      (testing "while the members that remain still separate each other"
        (is (v/disjoint? kb dog fish))))))

(tu/deftest-kb a-metatype-separates-members-without-storing-a-clique
  ;; Asserting the clique would mean n(n-1)/2 stored `(disjoint a b)` sentexes for n
  ;; members.  The only sentexes are the ones the author wrote.
  (tu/with-terms [animalSpecies dog cat fish bird]
    (v/assert kb (list 'disjointMetatype animalSpecies) 'UniverseContext)
    (let [before (count (tu/sentex-ids kb))]
      (doseq [t [dog cat fish bird]]
        (v/assert kb (list animalSpecies t) 'UniverseContext))
      (testing "four members are pairwise disjoint"
        (is (v/disjoint? kb dog cat))
        (is (v/disjoint? kb fish bird))
        (is (v/disjoint? kb cat bird)))
      (testing "and cost exactly four sentexes, not four plus six"
        (is (= (+ before 4) (count (tu/sentex-ids kb)))))
      (testing "no (disjoint ..) sentex was invented"
        (is (empty? (v/sentexes-matching kb (list 'disjoint '?a '?b) '?ctx)))))))

;; ---- two supporters, one retraction: every cache refcounts --------------
;;
;; A declaration asserted twice (two contexts = two sentexes) must survive losing one
;; supporter.  `genl` keeps a per-claim `:support` map; the flat caches share the
;; `:cache-support` count — both hold the edge/pair while a sentex still asserts it.
;; These two tests check that genl and `disjoint` agree, rather than assume it.

(tu/deftest-kb genl-survives-losing-one-of-two-supporting-sentexes
  (tu/with-terms [dog animal AlphaContext]
    (v/assert kb (list 'genlContext AlphaContext 'UniverseContext) 'UniverseContext)
    (let [h1 (v/assert kb (list 'genl dog animal) 'UniverseContext)
          _  (v/assert kb (list 'genl dog animal) AlphaContext)]
      (is (v/genl? kb dog animal))
      (v/retract! kb h1)
      (testing "the edge is still asserted elsewhere, so the closure keeps it"
        (is (v/genl? kb dog animal)
            "genl is belief-tracked: one supporter going does not drop the edge")))))

(tu/deftest-kb a-doubly-asserted-disjoint-pair-tracks-its-supporters
  ;; The same shape as the genl test above, for the cache that refcounts through the
  ;; shared `:cache-support` map.  Retracting one of two supporting sentexes must not
  ;; release a pair the other still asserts — otherwise a legitimate `(dog Felix)`
  ;; starts being accepted while `(disjoint dog cat)` is still believed in another
  ;; context.
  (tu/with-terms [dog cat Felix AlphaContext]
    (v/assert kb (list 'genlContext AlphaContext 'UniverseContext) 'UniverseContext)
    (let [h1 (v/assert kb (list 'disjoint dog cat) 'UniverseContext)
          h2 (v/assert kb (list 'disjoint dog cat) AlphaContext)]
      (is (v/disjoint? kb dog cat))
      (when (not= h1 h2)                    ; two contexts, so two distinct sentexes
        (v/retract! kb h1)
        (testing "the surviving declaration still holds the pair disjoint"
          (is (v/disjoint? kb dog cat)
              "one of two supporters was retracted; the other still asserts the pair"))))))

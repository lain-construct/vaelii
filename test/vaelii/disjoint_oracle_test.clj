;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.disjoint-oracle-test
  "The disjointness prover's enumeration against a brute-force scan of the vocabulary.

  An open `disjoint` goal has an answer whose size is a function of the
  **declarations**: `(disjoint x y)` separates two subtrees and convicts
  `specs(x) × specs(y)`, and nothing reaches a candidate any other way.  So the prover
  enumerates from the declarations, and what it never looks at is most of the KB —
  which is the point, and also the failure mode: a candidate it does not reach is an
  answer that silently stops existing, and an empty result set reads exactly like a
  correct negative.

  The oracle here is the enumeration the prover no longer runs: every type the
  taxonomy holds, filtered by `tax/disjoint?`.  Written as a scan on purpose.  An
  oracle that walked the declarations would be the implementation restated in the
  test — it would inherit whatever the implementation cannot reach, and agree with it
  for the wrong reason.  `disjoint?` is the predicate on both sides, because the claim
  under test is about *what is fed to it*, not about what it decides.

  The corpus is a large vocabulary with a handful of separations, since that is the
  ratio the enumeration is about: six independent hierarchies of forty types apiece,
  three declared pairs between them and one metatype.  Two of the pairs overlap, so
  some candidate is convicted twice and the deduplication is under test rather than
  assumed.  Random within a fixed seed, so a failure reproduces.

  Four shapes are checked beside the answer set, each a way for a declaration-driven
  enumeration to be wrong that a random corpus does not produce on its own:

  * **a declaration the goal's context cannot see.**  `:disjoint-index` is not
    context-scoped — it is the adjacency of the whole KB's declarations — so the
    visibility filter is the enumeration's own to apply, and a driver that trusted the
    index would globalize every microtheory's separations.
  * **a retracted declaration.**  Belief filtering: assert, query, retract, query.
  * **a metatype.**  Its clique is consulted rather than stored, and its members need
    not be in the taxonomy's node set at all, so it is reached by no genl walk.
  * **a type below both sides of one separation**, which is disjoint from *itself* and
    is what the one-variable-twice goal `(disjoint ?x ?x)` asks for."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

;; ---- the corpus ---------------------------------------------------------

(def ^:private trees
  "Independent hierarchies.  Independent because `wff` refuses to separate two types
  one of which already subsumes the other, so a declaration has to cross trees."
  6)

(def ^:private per-tree 40)

(defn- build-forest!
  "`trees` random hierarchies of `per-tree` types each, rooted at the first name of
  each block: every type after the root takes an earlier one in its own block as its
  supertype, so each block is a tree of real depth rather than a star.  Returns the
  blocks."
  [kb ctx ^java.util.Random rng]
  (let [blocks (mapv vec (partition per-tree (repeatedly (* trees per-tree) tu/tmp-type)))]
    (doseq [b blocks, i (range 1 (count b))]
      (v/assert kb (list 'genl (b i) (b (.nextInt rng i))) ctx))
    blocks))

;; ---- the oracles --------------------------------------------------------

(defn- scan
  "Every type the taxonomy knows, filtered by `disjoint?` — the answer to
  `(disjoint a ?t)` computed the way the prover does not."
  [kb a ctx]
  (let [tx (:taxonomy kb)]
    (into #{} (filter #(tax/disjoint? tx a % ctx)) (tax/types tx))))

(defn- scan-pairs
  "The same scan for both arguments open: every ordered pair of types the predicate
  convicts."
  [kb ctx]
  (let [tx (:taxonomy kb)
        ts (tax/types tx)]
    (into #{} (for [x ts, y ts :when (tax/disjoint? tx x y ctx)] [x y]))))

(defn- answers
  "The bindings of `var*` in an open goal's solutions, as a set."
  [kb goal var* ctx]
  (into #{} (map #(get % var*)) (v/ask kb goal ctx)))

(defn- pairs-of [kb goal ctx]
  (into #{} (map (juxt #(get % '?a) #(get % '?b))) (v/ask kb goal ctx)))

;; ---- the answer set -----------------------------------------------------

(tu/deftest-kb an-open-disjointness-goal-answers-what-a-vocabulary-scan-answers
  (tu/with-terms [OracleContext kind]
    (v/assert kb (list 'genlContext OracleContext 'UniverseContext) 'UniverseContext)
    (let [rng    (java.util.Random. 20260804)
          blocks (build-forest! kb OracleContext rng)
          root   (fn [i] (get-in blocks [i 0]))
          node   (fn [i j] (get-in blocks [i j]))]
      ;; four separations over 240 types: three declared pairs, one metatype.  The
      ;; second overlaps the first — one type separated from a partner *and* from one
      ;; of that partner's own subtypes, so two declarations convict one candidate
      (v/assert kb (list 'disjoint (root 0) (root 1)) OracleContext)
      (v/assert kb (list 'disjoint (root 0) (node 1 5)) OracleContext)
      (v/assert kb (list 'disjoint (node 2 7) (root 3)) OracleContext)
      (v/assert kb (list kind (root 4)) OracleContext)
      (v/assert kb (list kind (root 5)) OracleContext)
      (v/assert kb (list 'disjointMetatype kind) OracleContext)

      (testing "every type's answer is the scan's, with either argument bound"
        (doseq [t (concat (map root (range trees))
                          [(node 0 13) (node 1 39) (node 2 7) (node 2 9)
                           (node 3 21) (node 4 5) (node 5 31)])]
          (let [want (scan kb t OracleContext)]
            (is (= want (answers kb (list 'disjoint t '?t) '?t OracleContext))
                (str "first argument bound: " t))
            (is (= want (answers kb (list 'disjoint '?t t) '?t OracleContext))
                (str "second argument bound: " t)))))

      (testing "and the corpus is one where that says something"
        (is (= per-tree (count (scan kb (root 0) OracleContext)))
            "a declaration convicts a whole subtree, or the comparison is vacuous")
        (is (empty? (scan kb (node 2 9) OracleContext))
            "and a type under no declaration is convicted by nothing"))

      (testing "both arguments open: the same pairs, and no others"
        (is (= (scan-pairs kb OracleContext)
               (pairs-of kb (list 'disjoint '?a '?b) OracleContext))))

      (testing "the unscoped read agrees with its own scan too"
        (is (= (scan kb (root 0) '?ctx)
               (answers kb (list 'disjoint (root 0) '?t) '?t '?ctx))))

      (testing "no answer is repeated, though two declarations convict some of them"
        ;; asked of the prover rather than of `ask`, which dedups on the way out: the
        ;; enumeration walks one closure per partner and they overlap here by
        ;; construction, so this is the prover's own `distinct` and nothing else
        (let [sols (provers/solve (provers/->DisjointnessProver)
                                  kb (list 'disjoint (root 0) '?t) OracleContext)]
          (is (seq sols))
          (is (= (count sols) (count (set sols)))))))))

;; ---- the shapes a random corpus does not produce -------------------------

(tu/deftest-kb a-declaration-the-goal-cannot-see-enumerates-nothing
  ;; The case a `disjoint-index`-driven enumeration is likeliest to get wrong: the
  ;; index is the adjacency of every declaration in the KB and carries no context, so
  ;; the visibility filter has to be applied where the enumeration is, not left to the
  ;; lookup.  Two microtheories that cannot see each other, the separation in one.
  (tu/with-terms [a_place an_agent a_city PhysicalGeographyContext GeographyContext]
    (v/assert kb (list 'genl a_place 'thing) 'UniverseContext)
    (v/assert kb (list 'genl an_agent 'thing) 'UniverseContext)
    (v/assert kb (list 'genl a_city a_place) 'UniverseContext)
    (v/assert kb (list 'genlContext PhysicalGeographyContext 'UniverseContext) 'UniverseContext)
    (v/assert kb (list 'genlContext GeographyContext 'UniverseContext) 'UniverseContext)
    (v/assert kb (list 'disjoint a_place an_agent) PhysicalGeographyContext)

    (testing "where the declaration is visible, the subtree is convicted"
      (is (= #{an_agent}
             (answers kb (list 'disjoint a_place '?t) '?t PhysicalGeographyContext)))
      (is (= #{a_place a_city}
             (answers kb (list 'disjoint an_agent '?t) '?t PhysicalGeographyContext))))

    (testing "in the sibling that never said it and cannot see it, nothing is"
      (is (empty? (answers kb (list 'disjoint a_place '?t) '?t GeographyContext)))
      (is (empty? (answers kb (list 'disjoint an_agent '?t) '?t GeographyContext)))
      (is (empty? (pairs-of kb (list 'disjoint '?a '?b) GeographyContext))))

    (testing "while the unscoped read still reports every declaration in the KB"
      (is (= #{an_agent} (answers kb (list 'disjoint a_place '?t) '?t '?ctx))))

    (testing "the scan agrees on all three readings, which is what makes them checkable"
      (is (= (scan kb a_place PhysicalGeographyContext)
             (answers kb (list 'disjoint a_place '?t) '?t PhysicalGeographyContext)))
      (is (= (scan kb a_place GeographyContext)
             (answers kb (list 'disjoint a_place '?t) '?t GeographyContext))))))

(tu/deftest-kb a-retracted-declaration-stops-being-enumerated
  ;; Belief filtering, asked of the enumeration rather than of the predicate: the
  ;; declarations are read through the caches, which follow belief, so a retraction
  ;; empties the answer with nothing else to maintain.
  (tu/with-terms [dog cat terrier RetractContext]
    (v/assert kb (list 'genlContext RetractContext 'UniverseContext) 'UniverseContext)
    (v/assert kb (list 'genl terrier dog) RetractContext)
    (v/assert kb (list 'disjoint dog cat) RetractContext)
    (testing "asserted: the pair and the subtype below it"
      (is (= #{cat} (answers kb (list 'disjoint dog '?t) '?t RetractContext)))
      (is (= #{dog terrier} (answers kb (list 'disjoint cat '?t) '?t RetractContext))))
    (v/retract! kb (v/handle-of kb (list 'disjoint dog cat) RetractContext))
    (testing "retracted: nothing convicts anything"
      (is (empty? (answers kb (list 'disjoint dog '?t) '?t RetractContext)))
      (is (empty? (answers kb (list 'disjoint cat '?t) '?t RetractContext)))
      (is (empty? (pairs-of kb (list 'disjoint '?a '?b) RetractContext)))
      (is (empty? (scan kb dog RetractContext)) "and the scan says the same"))))

(tu/deftest-kb a-metatype-member-is-enumerated-though-no-genl-edge-reaches-it
  ;; A metatype's clique is consulted, never stored, and a member need not participate
  ;; in `genl` at all — so it is in no closure and in no declared pair.  The open goal
  ;; answers what the ground goal answers, which is the property that ties the two
  ;; arms of `solve` to one predicate.
  (tu/with-terms [species dog cat fish MetaContext]
    (v/assert kb (list 'genlContext MetaContext 'UniverseContext) 'UniverseContext)
    (v/assert kb (list species dog) MetaContext)
    (v/assert kb (list species cat) MetaContext)
    (v/assert kb (list species fish) MetaContext)
    (v/assert kb (list 'disjointMetatype species) MetaContext)
    (testing "the ground goal convicts each pair"
      (is (v/ask? kb (list 'disjoint dog cat) MetaContext))
      (is (v/ask? kb (list 'disjoint dog fish) MetaContext)))
    (testing "so the open goal binds them"
      (is (= #{cat fish} (answers kb (list 'disjoint dog '?t) '?t MetaContext)))
      (is (= #{dog fish} (answers kb (list 'disjoint '?t cat) '?t MetaContext))))
    (testing "and the pairs come out both ways round, disjoint being symmetric"
      (is (= #{[dog cat] [cat dog] [dog fish] [fish dog] [cat fish] [fish cat]}
             (pairs-of kb (list 'disjoint '?a '?b) MetaContext))))
    (testing "unmarking the metatype releases every pair at once"
      (v/retract! kb (v/handle-of kb (list 'disjointMetatype species) MetaContext))
      (is (empty? (answers kb (list 'disjoint dog '?t) '?t MetaContext)))
      (is (empty? (pairs-of kb (list 'disjoint '?a '?b) MetaContext))))))

(tu/deftest-kb a-type-below-both-sides-of-a-separation-is-disjoint-from-itself
  ;; `(disjoint ?x ?x)` — one variable in both places, so one binding rather than two.
  ;; A type below both sides of one declaration can have no instances, and that is
  ;; what the goal asks for; nothing else answers it.
  (tu/with-terms [feathered scaled griffin sparrow SelfContext]
    (v/assert kb (list 'genlContext SelfContext 'UniverseContext) 'UniverseContext)
    (v/assert kb (list 'genl griffin feathered) SelfContext)
    (v/assert kb (list 'genl griffin scaled) SelfContext)
    (v/assert kb (list 'genl sparrow feathered) SelfContext)
    (v/assert kb (list 'disjoint feathered scaled) SelfContext)
    (testing "the empty type is bound, and only it"
      (is (= #{griffin} (answers kb (list 'disjoint '?x '?x) '?x SelfContext))))
    (testing "which is what the predicate says of it"
      (is (v/ask? kb (list 'disjoint griffin griffin) SelfContext))
      (is (not (v/ask? kb (list 'disjoint sparrow sparrow) SelfContext))))))

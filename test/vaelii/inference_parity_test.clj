;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.inference-parity-test
  "The criterion that decides whether the node engine is right: for every query here,
  `:inference` returns exactly what `:dfs` returns.

  Deduped and projected on **both** sides.  Dedup is the point of a claimed-key set, and
  the DFS can return one solution twice by two derivations; it also returns the rule
  variables its expansions bound, which name nothing the asker knows.  So the comparison
  is `(distinct (map #(select-keys % query-vars) …))`, which is the shape `ask` already
  hands back.

  **Within the depth bound.**  The node engine terminates on `inference/*max-depth*` and
  the DFS terminates on the data, so a derivation deeper than the bound is found by one
  and not the other.  That is a real difference and not a bug to be tested away: every
  shape here is given a bound that covers it, and `deeper-than-the-bound-is-not-found`
  pins the divergence itself rather than pretending it is absent."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.inference :as inf]
            [vaelii.impl.resolution :as res]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- projected
  "`sols` deduped and projected onto the query's variables."
  [goal sols]
  (let [qvars (res/form-variables (if (vector? goal) goal [goal]))]
    (set (map #(select-keys (res/resolve-bindings %) qvars) sols))))

(defn- parity
  "Both engines' answers for `goal`, asserted equal.  Returns the set, so a caller can
  go on to say what it should contain."
  ([kb goal context] (parity kb goal context 8))
  ([kb goal context depth]
   (binding [inf/*max-depth* depth]
     (let [dfs  (projected goal (v/prove kb goal context))
           node (projected goal (binding [v/*query-engine* :inference, inf/*max-depth* 8]
                                  (v/prove kb goal context)))]
       (is (= dfs node) (str "the engines disagree on " (pr-str goal)))
       dfs))))

;; ---- a corpus of shapes, built once per test ------------------------------

(defn- kinship!
  "`parentOf` over `n` generations, plus the textbook ancestor pair."
  [kb parentOf anc context n]
  (doseq [i (range n)]
    (v/assert kb (list parentOf (symbol (str "TmpKin" i "Node"))
                       (symbol (str "TmpKin" (inc i) "Node")))
              context))
  (v/assert-rule kb [(list parentOf '?x '?z)] (list anc '?x '?z) context
                 {:direction :backward})
  (v/assert-rule kb [(list parentOf '?x '?y) (list anc '?y '?z)] (list anc '?x '?z)
                 context {:direction :backward}))

(tu/deftest-kb facts-alone-agree
  (tu/with-terms [parentOf ownerOf CxPlain]
    (tu/with-terms [PlA PlB PlC]
      (v/assert kb (list parentOf PlA PlB) CxPlain)
      (v/assert kb (list parentOf PlB PlC) CxPlain)
      (v/assert kb (list ownerOf PlA PlC) CxPlain)
      (is (= #{{'?y PlB}} (parity kb (list parentOf PlA '?y) CxPlain)))
      (parity kb (list parentOf '?x '?y) CxPlain)
      (parity kb (list parentOf PlA PlB) CxPlain)
      (parity kb (list parentOf PlB PlA) CxPlain)
      (parity kb [(list parentOf '?x '?y) (list ownerOf '?x '?z)] CxPlain))))

(tu/deftest-kb recursion-over-a-chain-agrees
  (tu/with-terms [parentOf anc CxKin]
    (kinship! kb parentOf anc CxKin 4)
    (testing "open, bound at the head, bound at the tail, and both"
      (is (= 10 (count (parity kb (list anc '?x '?z) CxKin))))
      (parity kb (list anc 'TmpKin0Node '?z) CxKin)
      (parity kb (list anc '?x 'TmpKin4Node) CxKin)
      (parity kb (list anc 'TmpKin0Node 'TmpKin4Node) CxKin)
      (parity kb (list anc 'TmpKin4Node '?z) CxKin))
    (testing "a conjunction over the derived relation"
      (parity kb [(list anc '?x '?y) (list parentOf '?y '?z)] CxKin))))

(tu/deftest-kb a-converging-dag-agrees
  (tu/with-terms [parentOf anc CxDag]
    (let [n (fn [l i] (symbol (str "TmpDag" l "x" i "Node")))]
      (doseq [[lvl cnt] [[0 8] [1 2]] i (range cnt)]
        (v/assert kb (list parentOf (n lvl i) (n (inc lvl) (quot i 4))) CxDag))
      (v/assert-rule kb [(list parentOf '?x '?z)] (list anc '?x '?z) CxDag
                     {:direction :backward})
      (v/assert-rule kb [(list parentOf '?x '?y) (list anc '?y '?z)] (list anc '?x '?z)
                     CxDag {:direction :backward})
      (is (= 18 (count (parity kb (list anc '?x '?z) CxDag 4))))
      (parity kb (list anc (n 0 0) '?z) CxDag 4))))

(tu/deftest-kb a-cyclic-graph-agrees
  (tu/with-terms [edgeOf pathOf CxCyc]
    (let [n (mapv #(symbol (str "TmpCyc" % "Node")) (range 5))]
      (doseq [[a b] [[0 1] [1 2] [2 0] [2 3] [3 4] [1 4]]]
        (v/assert kb (list edgeOf (n a) (n b)) CxCyc))
      (v/assert-rule kb [(list edgeOf '?x '?z)] (list pathOf '?x '?z) CxCyc
                     {:direction :backward})
      (v/assert-rule kb [(list edgeOf '?x '?y) (list pathOf '?y '?z)] (list pathOf '?x '?z)
                     CxCyc {:direction :backward})
      (parity kb (list pathOf (n 0) '?z) CxCyc 5)
      (parity kb (list pathOf '?x '?z) CxCyc 5))))

(tu/deftest-kb a-diamond-agrees-and-neither-engine-answers-twice
  (tu/with-terms [base mid1 mid2 top CxDm]
    (tu/with-terms [DmX DmY]
      (v/assert kb (list base DmX) CxDm)
      (v/assert kb (list base DmY) CxDm)
      (v/assert-rule kb [(list base '?x)] (list mid1 '?x) CxDm {:direction :backward})
      (v/assert-rule kb [(list base '?x)] (list mid2 '?x) CxDm {:direction :backward})
      (v/assert-rule kb [(list mid1 '?x)] (list top '?x) CxDm {:direction :backward})
      (v/assert-rule kb [(list mid2 '?x)] (list top '?x) CxDm {:direction :backward})
      (is (= #{{'?x DmX} {'?x DmY}} (parity kb (list top '?x) CxDm 3))))))

(tu/deftest-kb exceptions-block-the-same-bindings-in-both
  (tu/with-terms [wings flies odd grounded CxEx]
    (tu/with-terms [ExBird ExPenguin ExOstrich]
      (doseq [i [ExBird ExPenguin ExOstrich]] (v/assert kb (list wings i) CxEx))
      (v/assert kb (list odd ExPenguin) CxEx)
      (v/assert kb (list grounded ExOstrich) CxEx)
      (v/assert kb (list 'exceptWhen (list odd '?x)
                         (list 'set/defaultRule
                               (list 'implies (list wings '?x) (list flies '?x))))
                CxEx)
      (v/assert kb (list 'exceptWhen (list grounded '?x)
                         (list 'set/defaultRule
                               (list 'implies (list wings '?x) (list flies '?x))))
                CxEx)
      (is (= #{{'?x ExBird}} (parity kb (list flies '?x) CxEx)))
      (parity kb (list flies ExPenguin) CxEx)
      (parity kb (list flies ExBird) CxEx))))

(tu/deftest-kb two-guarded-rules-to-one-residual-both-answer
  ;; two *distinct* rules, each carrying its own exceptWhen, rewrite one goal to the
  ;; same canonical residual through the genl fan.  The claimed-key must read the
  ;; guards' identities, not their count: counted, the two children are one key, the
  ;; second is dropped before it is enqueued, and every answer only its exception
  ;; admits is lost — while prove (DFS) answers in full.
  (tu/with-terms [dog_t cat_t animal_t qq aa bb CxGd]
    (tu/with-terms [GdT1 GdT2]
      (v/assert kb (list 'genl dog_t animal_t) CxGd)
      (v/assert kb (list 'genl cat_t animal_t) CxGd)
      (v/assert kb (list qq GdT1) CxGd)
      (v/assert kb (list qq GdT2) CxGd)
      (v/assert kb (list aa GdT1) CxGd)
      (v/assert kb (list bb GdT2) CxGd)
      ;; backward-only, so no firing pre-stores the conclusions: the node engine has
      ;; to expand both rules, which is where a counted key drops one
      (v/assert kb (list 'exceptWhen (list aa '?x)
                         (list 'set/defaultRule
                               (list 'set/backwardRule
                                     (list 'implies (list qq '?x) (list dog_t '?x)))))
                CxGd)
      (v/assert kb (list 'exceptWhen (list bb '?x)
                         (list 'set/defaultRule
                               (list 'set/backwardRule
                                     (list 'implies (list qq '?x) (list cat_t '?x)))))
                CxGd)
      (is (= #{{'?y GdT1} {'?y GdT2}}
             (parity kb (list animal_t '?y) CxGd 3))))))

(tu/deftest-kb a-deferred-antecedent-agrees
  (tu/with-terms [pairOf distinctPair CxDf]
    (tu/with-terms [DfA DfB]
      (v/assert kb (list pairOf DfA DfB) CxDf)
      (v/assert kb (list pairOf DfB DfA) CxDf)
      (v/assert kb (list pairOf DfA DfA) CxDf)
      (v/assert-rule kb [(list pairOf '?x '?y) (list 'different '?x '?y)]
                     (list distinctPair '?x '?y) CxDf {:direction :backward})
      (is (= 2 (count (parity kb (list distinctPair '?x '?y) CxDf)))))))

(tu/deftest-kb predicate-and-type-subsumption-agree
  (tu/with-terms [fatherOf parentOf anc CxSub]
    (tu/with-terms [SbA SbB]
      (v/assert kb (list 'genl fatherOf parentOf) CxSub)
      (v/assert kb (list fatherOf SbA SbB) CxSub)
      (v/assert-rule kb [(list parentOf '?x '?z)] (list anc '?x '?z) CxSub
                     {:direction :backward})
      (testing "a fact under a sub-predicate answers the supertype antecedent"
        (is (= #{{'?x SbA '?z SbB}} (parity kb (list anc '?x '?z) CxSub))))))
  (tu/with-terms [dog animal barks CxType]
    (tu/with-terms [TyMuffet]
      (v/assert kb (list 'genl dog animal) CxType)
      (v/assert kb (list dog TyMuffet) CxType)
      (v/assert-rule kb [(list animal '?x)] (list barks '?x) CxType
                     {:direction :backward})
      (is (= #{{'?x TyMuffet}} (parity kb (list barks '?x) CxType))))))

(tu/deftest-kb context-scoping-agrees
  (tu/with-terms [parentOf anc CxOuter CxInner]
    (tu/with-terms [CsA CsB CsC]
      (v/assert kb (list 'genlCx CxInner CxOuter) 'CxUniverse)
      (v/assert kb (list parentOf CsA CsB) CxOuter)
      (v/assert kb (list parentOf CsB CsC) CxInner)
      (v/assert-rule kb [(list parentOf '?x '?z)] (list anc '?x '?z) CxOuter
                     {:direction :backward})
      (testing "the inner context sees both, the outer only its own"
        (is (= 2 (count (parity kb (list anc '?x '?z) CxInner))))
        (is (= 1 (count (parity kb (list anc '?x '?z) CxOuter))))))))

(tu/deftest-kb a-multi-antecedent-rule-with-a-join-agrees
  (tu/with-terms [worksAt livesIn commutesTo CxJn]
    (tu/with-terms [JnAnn JnBob JnOffice JnTown JnCity]
      (v/assert kb (list worksAt JnAnn JnOffice) CxJn)
      (v/assert kb (list worksAt JnBob JnOffice) CxJn)
      (v/assert kb (list livesIn JnAnn JnTown) CxJn)
      (v/assert kb (list livesIn JnBob JnCity) CxJn)
      (v/assert-rule kb [(list worksAt '?p '?w) (list livesIn '?p '?h)]
                     (list commutesTo '?h '?w) CxJn {:direction :backward})
      (is (= #{{'?h JnTown '?w JnOffice} {'?h JnCity '?w JnOffice}}
             (parity kb (list commutesTo '?h '?w) CxJn)))
      (parity kb (list commutesTo JnTown '?w) CxJn)
      (parity kb [(list commutesTo '?h '?w) (list worksAt '?p '?w)] CxJn))))

(tu/deftest-kb a-rule-used-twice-on-one-path-agrees
  ;; the structure that made the DFS disagree with itself: every rule in the KB is spelled
  ;; from one pool of canonical variable names, and a node merges many instances into
  ;; one substitution
  (tu/with-terms [parentOf anc CxRn]
    (kinship! kb parentOf anc CxRn 3)
    (is (= 3 (count (parity kb (list anc 'TmpKin0Node '?z) CxRn))))))

;; ---- the divergence, stated rather than hidden ----------------------------

(tu/deftest-kb deeper-than-the-bound-is-not-found
  (tu/with-terms [parentOf anc CxDeep]
    (kinship! kb parentOf anc CxDeep 5)
    (let [goal (list anc 'TmpKin0Node '?z)
          dfs  (projected goal (v/prove kb goal CxDeep))
          shy  (projected goal (binding [v/*query-engine* :inference, inf/*max-depth* 2]
                                 (v/prove kb goal CxDeep)))]
      (is (= 5 (count dfs)) "the DFS terminates on the data, so it finds the chain")
      (is (= 2 (count shy)) "the node engine terminates on the bound, so it finds two")
      (is (every? dfs shy) "what it does find must still be right")
      (testing "and a bound that covers the chain closes the gap"
        (is (= dfs (projected goal (binding [v/*query-engine* :inference, inf/*max-depth* 5]
                                     (v/prove kb goal CxDeep)))))))))

;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.inference-canonical-test
  "Every node of the node engine is a **canonicalized conjunction**, and what that buys.

  Two things follow from numbering each node's variables `?var0 ?var1 …`, and this
  namespace is about both.  Identity becomes structural: two conjunctions that differ
  only in what their variables are called are one value, so the claimed-key set
  recognizes a node the search already built without any renaming heuristic laid over
  it.  And the rule-collision problem stops being a problem: a stored rule is spelled
  `?var0 ?var1 …` and so is a node, so a rule is numbered *past* the node's variables
  before unification and the namespaces are disjoint by construction.

  The price is that nothing crosses between two namespaces for free — a solution is
  renamed back through `:to-query`, an inherited guard is lifted through `:to-parent` —
  and most of what is here is about those maps being right.  A wrong one costs an
  answer, not time, which is why `inference_parity_test` sits beside this."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.inference :as inf]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- answers
  ([kb goals context] (answers kb goals context 5))
  ([kb goals context depth]
   (set (inf/solutions kb goals context {:max-depth depth}))))

(defn- nodes-of
  "Every node a search over `goals` builds, driven dry."
  ([kb goals context] (nodes-of kb goals context 5))
  ([kb goals context depth]
   (let [sess (inf/session kb goals context {:max-depth depth})]
     (doall (inf/search-seq sess))
     (vals @(:nodes sess)))))

(defn- chain-kb!
  "`(edgeOf …)` down a path, with a one-hop and a recursive rule concluding `anc`."
  [kb edgeOf anc context inds]
  (doseq [[a b] (partition 2 1 inds)]
    (v/assert kb (list edgeOf a b) context))
  (v/assert-rule kb [(list edgeOf '?x '?z)] (list anc '?x '?z) context
                 {:direction :backward})
  (v/assert-rule kb [(list edgeOf '?x '?y) (list anc '?y '?z)] (list anc '?x '?z) context
                 {:direction :backward}))

;; ---- every node is canonical ---------------------------------------------

(tu/deftest-kb every-node-the-search-builds-is-a-canonical-conjunction
  (tu/with-terms [edgeOf anc CxCan]
    (tu/with-terms [CnA CnB CnC]
      (chain-kb! kb edgeOf anc CxCan [CnA CnB CnC])
      (let [ns' (nodes-of kb [(list anc '?who '?whom)] CxCan)]
        (is (< 1 (count ns')) "nothing was rewritten, so this proves nothing")
        (doseq [n ns']
          (let [lits (mapv :sentence (:literals n))]
            (is (= lits (first (sx/canonical-conjunction lits)))
                (str "a node is not in canonical form: " (pr-str lits)))))
        (testing "so no node mentions a decorated or primed name"
          (is (not-any? (fn [n] (some #(re-find #"'" (name %))
                                      (res/form-variables (mapv :sentence (:literals n)))))
                        ns')))))))

(tu/deftest-kb alpha-variant-queries-build-the-same-nodes
  ;; The identity claim, end to end: what the asker calls their variables cannot change
  ;; the shape of the search, only the names the answers come back under.
  (tu/with-terms [edgeOf anc CxAlpha]
    (tu/with-terms [AlA AlB AlC]
      (chain-kb! kb edgeOf anc CxAlpha [AlA AlB AlC])
      (let [shape (fn [goals] (set (map (fn [n] [(mapv :sentence (:literals n))
                                                 (mapv :depth (:literals n))])
                                        (nodes-of kb goals CxAlpha))))]
        (is (= (shape [(list anc '?x '?z)])
               (shape [(list anc '?who '?whom)])
               (shape [(list anc '?var0 '?var1)]))
            "the asker's spelling changed the search")
        (testing "and the answers come back under whichever names were used"
          (is (= #{'?who '?whom}
                 (set (mapcat keys (answers kb [(list anc '?who '?whom)] CxAlpha)))))
          (is (= #{'?x '?z}
                 (set (mapcat keys (answers kb [(list anc '?x '?z)] CxAlpha))))))))))

;; ---- the maps back -------------------------------------------------------

(tu/deftest-kb answer-terms-still-name-the-askers-variables-at-every-depth
  ;; `:answer-terms` is the whole chain of rewrites folded into one map: the asker's
  ;; variables, each pointing at the term that stands for it *here*.  Three things have
  ;; to hold of it at every node, and a rewrite that broke any of them would lose an
  ;; answer rather than slow anything down.
  (tu/with-terms [edgeOf anc CxCompose]
    (tu/with-terms [CoA CoB CoC]
      (chain-kb! kb edgeOf anc CxCompose [CoA CoB CoC])
      (let [sess (inf/session kb [(list anc '?x '?z)] CxCompose {:max-depth 3})
            _    (doall (inf/search-seq sess))
            all  (vals @(:nodes sess))]
        (is (< 2 (count all)) "too few nodes for the chain to mean anything")
        (doseq [n all]
          (let [terms (:answer-terms n)
                own   (res/form-variables (mapv :sentence (:literals n)))]
            (testing "the asker's variables are never lost, however deep the rewriting goes"
              (is (= '#{?x ?z} (set (keys terms)))
                  (str "node " (:id n) " forgot what it was asked")))
            (testing "and each stands for something this node can actually resolve"
              (doseq [[q t] terms]
                (is (every? own (res/form-variables t))
                    (str "node " (:id n) "'s term for " q
                         " mentions a variable it does not name: " (pr-str t)))))))
        (testing "at the root each is simply the canonical variable that replaced it"
          (is (= '{?x ?var0, ?z ?var1} (:answer-terms (first (filter #(nil? (:parent-id %))
                                                                     all))))))))))

(tu/deftest-kb a-rewrite-that-grounds-a-query-variable-keeps-it
  ;; The case a variable-to-variable map cannot survive: the rule head carries a constant
  ;; where the query had a variable, so after the rewrite the child names nothing for it.
  ;; `:answer-terms` maps to a *term*, so the constant is what it maps to.
  (tu/with-terms [litOf fixedOf CxGround]
    (tu/with-terms [GdOnly GdOther]
      (v/assert kb (list litOf GdOnly) CxGround)
      (v/assert kb (list litOf GdOther) CxGround)
      ;; the consequent pins its first argument, so proving (fixedOf ?a ?b) fixes ?a
      (v/assert-rule kb [(list litOf '?y)] (list fixedOf GdOnly '?y) CxGround
                     {:direction :backward})
      (is (= #{{'?a GdOnly '?b GdOnly} {'?a GdOnly '?b GdOther}}
             (answers kb [(list fixedOf '?a '?b)] CxGround 2))
          "the variable the rewrite grounded was dropped from the answer"))))

(tu/deftest-kb a-rules-own-variables-never-reach-an-answer
  ;; They are named by nothing above the rewrite that made them, so `rename-solution`
  ;; drops them — no projection basis has to be carried to exclude them by name.
  (tu/with-terms [edgeOf anc CxScratch]
    (tu/with-terms [ScA ScB ScC ScD]
      (chain-kb! kb edgeOf anc CxScratch [ScA ScB ScC ScD])
      (let [sols (answers kb [(list anc ScA '?z)] CxScratch)]
        (is (seq sols))
        (is (every? #(= #{'?z} (set (keys %))) sols)
            (str "a scratch variable escaped: " (pr-str sols)))))))

(tu/deftest-kb a-query-spelled-in-the-engines-own-canonical-names-is-answered
  ;; Canonicalizing `[(anc ?var1 ?var0)]` produces the varmap `{?var0 ?var1, ?var1
  ;; ?var0}` — a permutation, and the reason the map back is applied in one pass.  A
  ;; chasing substitution does not terminate on it.
  (tu/with-terms [edgeOf anc CxSwap]
    (tu/with-terms [SwA SwB SwC]
      (chain-kb! kb edgeOf anc CxSwap [SwA SwB SwC])
      (let [[canon vm] (sx/canonical-conjunction [(list anc '?var1 '?var0)])]
        (is (= [(list anc '?var0 '?var1)] canon))
        (is (= '{?var0 ?var1, ?var1 ?var0} vm) "the varmap here is the swap"))
      (testing "and the crossed query answers the crossed relation"
        (let [straight (answers kb [(list anc '?var0 '?var1)] CxSwap)
              crossed  (answers kb [(list anc '?var1 '?var0)] CxSwap)]
          (is (seq straight))
          (is (= straight (set (map (fn [s] {'?var0 (get s '?var1) '?var1 (get s '?var0)})
                                    crossed)))
              "the crossed query did not come back crossed"))))))

;; ---- collisions the namespaces make impossible ---------------------------

(tu/deftest-kb one-rule-used-twice-on-a-path-does-not-meet-itself
  ;; The collision that needed renaming apart when one namespace was shared by the whole
  ;; derivation.  Under a namespace per node there is nothing to rename: the rule is
  ;; numbered past whatever the node already names, every time.
  (tu/with-terms [edgeOf anc CxTwice]
    (tu/with-terms [TwA TwB TwC TwD]
      (chain-kb! kb edgeOf anc CxTwice [TwA TwB TwC TwD])
      (is (= #{TwB TwC TwD}
             (set (map #(get % '?z) (answers kb [(list anc TwA '?z)] CxTwice 6))))
          "the recursive rule's second use lost the branch under it"))))

(tu/deftest-kb two-different-rules-spelled-alike-do-not-meet-each-other
  ;; Every stored rule is `?var0 ?var1 …`, so two rules in one derivation are the normal
  ;; collision, not the unlucky one.
  (tu/with-terms [linkOf midOf topOf CxTwoRule]
    (tu/with-terms [TrA TrB]
      (v/assert kb (list linkOf TrA TrB) CxTwoRule)
      (v/assert-rule kb [(list linkOf '?x '?y)] (list midOf '?x '?y) CxTwoRule
                     {:direction :backward})
      (v/assert-rule kb [(list midOf '?x '?y)] (list topOf '?x '?y) CxTwoRule
                     {:direction :backward})
      (is (= #{{'?a TrA '?b TrB}}
             (answers kb [(list topOf '?a '?b)] CxTwoRule 3))))))

(tu/deftest-kb a-rule-whose-head-crosses-its-own-arguments-still-binds-the-right-way-round
  ;; The unifier binds *our* variable to the rule's, so the rule's variable is left
  ;; carrying our identity — `unifier-aliases` is the only record of it.  A rule that
  ;; swaps its arguments is where getting that backwards shows up as a wrong answer
  ;; rather than a missing one.
  (tu/with-terms [fromTo toFrom CxInv]
    (tu/with-terms [IvA IvB]
      (v/assert kb (list fromTo IvA IvB) CxInv)
      (v/assert-rule kb [(list fromTo '?x '?y)] (list toFrom '?y '?x) CxInv
                     {:direction :backward})
      (is (= #{{'?p IvB '?q IvA}} (answers kb [(list toFrom '?p '?q)] CxInv 2))
          "the arguments came back the wrong way round")
      (testing "and with the head bound, both ways"
        (is (= #{{'?q IvA}} (answers kb [(list toFrom IvB '?q)] CxInv 2)))
        (is (empty? (answers kb [(list toFrom IvA '?q)] CxInv 2)))))))

;; ---- guards across a renaming --------------------------------------------

(tu/deftest-kb a-guard-survives-being-lifted-through-two-renamings
  ;; An `exceptWhen` closure is written over its own rule's variable names.  Two rewrites
  ;; later the node that finally solves the conjunction has renamed everything twice, so
  ;; the guard is asked through the composed map or it is asked about nothing.
  (tu/with-terms [wings flies odd airborne CxLift]
    (tu/with-terms [LfBird LfPenguin]
      (doseq [i [LfBird LfPenguin]] (v/assert kb (list wings i) CxLift))
      (v/assert kb (list odd LfPenguin) CxLift)
      (v/assert kb (list 'exceptWhen (list odd '?x)
                         (list 'set/defaultRule
                               (list 'implies (list wings '?x) (list flies '?x))))
                CxLift)
      ;; a second rule above it, so the guarded rule is reached by a rewrite rather than
      ;; sitting at the root
      (v/assert-rule kb [(list flies '?y)] (list airborne '?y) CxLift
                     {:direction :backward})
      (testing "the exception still names the individual it was written about"
        (is (= #{LfBird} (set (map #(get % '?w)
                                   (answers kb [(list airborne '?w)] CxLift 3)))))
        (is (empty? (answers kb [(list airborne LfPenguin)] CxLift 3)))
        (is (= #{{}} (answers kb [(list airborne LfBird)] CxLift 3)))))))

;; ---- dedup -------------------------------------------------------------

(tu/deftest-kb one-conjunction-asked-for-two-different-answers-is-two-nodes
  ;; Structural identity alone would collapse these, and one of the two answer sets
  ;; would be lost.  `:to-query` is in the key for exactly this.
  (tu/with-terms [pairOf bothOf CxSplit]
    (tu/with-terms [SpA SpB]
      (v/assert kb (list pairOf SpA SpB) CxSplit)
      (v/assert-rule kb [(list pairOf '?x '?y)] (list bothOf '?x '?y) CxSplit
                     {:direction :backward})
      (let [fwd (answers kb [(list bothOf '?m '?n)] CxSplit 2)
            rev (answers kb [(list bothOf '?n '?m)] CxSplit 2)]
        (is (= #{{'?m SpA '?n SpB}} fwd))
        (is (= #{{'?n SpA '?m SpB}} rev))
        (is (not= fwd rev) "the two spellings must not have collapsed into one")))))

(tu/deftest-kb the-same-question-twice-builds-the-same-search
  ;; Canonical numbering is by first occurrence and nothing else, so it cannot depend on
  ;; hash order or on how many queries ran before this one.
  (tu/with-terms [edgeOf anc CxDet]
    (tu/with-terms [DtA DtB DtC]
      (chain-kb! kb edgeOf anc CxDet [DtA DtB DtC])
      (let [lits (fn [n] (mapv :sentence (:literals n)))
            run  (fn []
                   (let [s (inf/session kb [(list anc '?x '?z)] CxDet {:max-depth 3})]
                     [(set (doall (inf/search-seq s)))
                      (set (map lits (vals @(:nodes s))))]))
            [a1 n1] (run)
            [a2 n2] (run)]
        (is (= a1 a2))
        (is (= n1 n2))))))

;; ---- the rest of the contract still holds --------------------------------

(tu/deftest-kb a-deferred-antecedent-is-still-computed-across-the-renaming
  (tu/with-terms [pairOf distinctPair CxDefCan]
    (tu/with-terms [DcA DcB]
      (v/assert kb (list pairOf DcA DcB) CxDefCan)
      (v/assert kb (list pairOf DcA DcA) CxDefCan)
      (v/assert-rule kb [(list pairOf '?x '?y) (list 'different '?x '?y)]
                     (list distinctPair '?x '?y) CxDefCan {:direction :backward})
      (is (= #{{'?p DcA '?q DcB}}
             (answers kb [(list distinctPair '?p '?q)] CxDefCan 2))))))

(tu/deftest-kb a-cyclic-rule-set-still-drains
  (tu/with-terms [pingOf pongOf CxCycCan]
    (tu/with-terms [CcInd]
      (v/assert-rule kb [(list pongOf '?x)] (list pingOf '?x) CxCycCan
                     {:direction :backward})
      (v/assert-rule kb [(list pingOf '?x)] (list pongOf '?x) CxCycCan
                     {:direction :backward})
      (let [sess (inf/session kb [(list pingOf CcInd)] CxCycCan {:max-depth 6})]
        (is (empty? (doall (inf/search-seq sess))))
        (is (zero? (:frontier (inf/tree-stats sess))) "the search did not terminate")))))

;; ---- the leaf-solver seam ------------------------------------------------

(tu/deftest-kb a-leaf-solver-answers-what-the-search-will-not-rewrite
  ;; The seam that lets one engine serve two leaf semantics.  Correctness only: routing
  ;; `ask` through here is measured and rejected (see `inf/backchain`'s docstring), so
  ;; what this pins is that the mechanism is right, not that it is a good idea.
  (tu/with-terms [edgeOf anc CxLeaf]
    (tu/with-terms [LfA LfB LfC]
      (chain-kb! kb edgeOf anc CxLeaf [LfA LfB LfC])
      (let [facts-only (set (inf/solutions kb [(list anc '?x '?z)] CxLeaf {:max-depth 4}))
            registry   (set (inf/backchain kb (list anc '?x '?z) CxLeaf
                                           provers/solve-goal {:max-depth 4}))]
        (is (seq facts-only))
        (is (= facts-only registry)
            "the registry as leaf must answer what the index does, on a fact-only KB"))
      (testing "and a leaf only a prover can answer is reached through it"
        ;; `different` is computed, never stored: the index cannot answer it at all.
        (tu/with-terms [pairOf distinctOf]
          (v/assert kb (list pairOf LfA LfB) CxLeaf)
          (v/assert kb (list pairOf LfA LfA) CxLeaf)
          (v/assert-rule kb [(list pairOf '?x '?y) (list 'different '?x '?y)]
                         (list distinctOf '?x '?y) CxLeaf {:direction :backward})
          (is (= #{{'?m LfA '?n LfB}}
                 (set (inf/backchain kb (list distinctOf '?m '?n) CxLeaf
                                     provers/solve-goal {:max-depth 2})))))))))

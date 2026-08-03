;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.converging-rules-test
  "A converging rule graph — one subgoal reached from many branches — answered the same
  whether or not the caches under the search are on.

  The shape that repeats is a subgoal which survives substitution with an **open
  argument**: `(anc <parent> ?z)`, reached once per child of that parent.  A rule whose
  antecedents are unary over a single variable has no such residual — it substitutes to
  a ground literal, distinct per binding — so the graphs here are relational, with a
  join variable that is not the head's.

  The node engine answers these by *rewriting* rather than re-asking: the residual stays
  symbolic, so `(anc ?y ?z)` becomes one node however many bindings reach it.  What is
  under test is not that saving but the thing it must never cost — the answer set, which
  has to be identical with the literal cache on and off."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.literal-cache :as lc]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(def ^:private depth
  "Deep enough for every graph below, and named once so a failure is never a question
  about which number a particular test picked."
  8)

(defn- answers [kb goal context]
  (set (doall (v/query kb goal context {:max-depth depth}))))

(defn- both-ways
  "The goal's answers with the literal cache on and off — they must be the same set, and
  that is the whole contract: a cost decision, never an answer-set change."
  [kb goal context]
  (let [off (binding [lc/*enabled* false] (answers kb goal context))
        on  (binding [lc/*enabled* true]  (answers kb goal context))]
    (is (= off on) (str "cached and uncached disagree on " (pr-str goal)))
    on))

(tu/deftest-kb converging-dag-shares-a-residual-subgoal
  ;; 16 -> 4 -> 1: four children per parent, so (anc <parent> ?z) is reached from four
  ;; branches.  The answer must be the full ancestor relation either way.
  (tu/with-terms [parentOf anc KinContext]
    (let [n (fn [lvl i] (symbol (str "Kin" lvl "n" i)))]
      (doseq [[lvl cnt] [[0 16] [1 4]]]
        (doseq [i (range cnt)]
          (v/assert kb (list parentOf (n lvl i) (n (inc lvl) (quot i 4))) KinContext)))
      (v/assert-rule kb [(list parentOf '?x '?z)] (list anc '?x '?z) KinContext
                     {:direction :backward})
      (v/assert-rule kb [(list parentOf '?x '?y) (list anc '?y '?z)] (list anc '?x '?z)
                     KinContext {:direction :backward})
      (testing "every leaf reaches its parent, grandparent and the root"
        (let [sols (both-ways kb (list anc (n 0 0) '?z) KinContext)]
          (is (= #{(n 1 0) (n 2 0)} (set (map #(get % '?z) sols))))))
      (testing "the open query agrees with the uncached engine, answer for answer"
        (let [sols (both-ways kb (list anc '?x '?z) KinContext)]
          (is (= 36 (count sols))
              "16 leaves reach a parent and the root, 4 parents reach the root")))
      (testing "a bound second argument is the same relation read the other way"
        (both-ways kb (list anc '?x (n 2 0)) KinContext)))))

(tu/deftest-kb same-generation-agrees-with-the-uncached-engine
  ;; sg(?x,?y) :- up(?x,?a), sg(?a,?b), down(?b,?y) — the recursive subgoal keeps BOTH
  ;; arguments open, and many (?x,?y) pairs route through the same (?a,?b)
  (tu/with-terms [up down flat sg SgContext]
    (doseq [i (range 12)]
      (v/assert kb (list up (symbol (str "SgA" i)) (symbol (str "SgM" (quot i 4)))) SgContext)
      (v/assert kb (list down (symbol (str "SgM" (quot i 4))) (symbol (str "SgB" i))) SgContext))
    (doseq [i (range 3)]
      (v/assert kb (list flat (symbol (str "SgM" i)) (symbol (str "SgM" i))) SgContext))
    (v/assert-rule kb [(list flat '?x '?y)] (list sg '?x '?y) SgContext {:direction :backward})
    (v/assert-rule kb [(list up '?x '?a) (list sg '?a '?b) (list down '?b '?y)]
                   (list sg '?x '?y) SgContext {:direction :backward})
    (testing "open"  (is (seq (both-ways kb (list sg '?x '?y) SgContext))))
    (testing "bound" (both-ways kb (list sg 'SgA0 '?y) SgContext))))

(tu/deftest-kb a-cyclic-rule-graph-is-answered-the-same-either-way
  ;; a cycle in the rule graph, where a path-structured search would re-enter itself:
  ;; the depth bound is what ends it here, and the answer must not depend on the cache
  (tu/with-terms [edge path CycContext]
    (let [nodes (mapv #(symbol (str "Cyc" %)) (range 5))]
      (doseq [[a b] [[0 1] [1 2] [2 0] [2 3] [3 4] [1 4]]]
        (v/assert kb (list edge (nodes a) (nodes b)) CycContext))
      (v/assert-rule kb [(list edge '?x '?z)] (list path '?x '?z) CycContext
                     {:direction :backward})
      (v/assert-rule kb [(list edge '?x '?y) (list path '?y '?z)] (list path '?x '?z)
                     CycContext {:direction :backward})
      (testing "from a node inside the cycle"
        (let [sols (both-ways kb (list path (nodes 0) '?z) CycContext)]
          (is (= (set nodes) (set (map #(get % '?z) sols)))
              "Cyc0 reaches every node — itself included, back around the cycle")))
      (testing "open, over the whole graph"
        (both-ways kb (list path '?x '?z) CycContext)))))

(tu/deftest-kb an-exception-is-honoured-through-the-cache
  ;; a guarded rule's firing depends on `exceptWhen`, evaluated per completed binding —
  ;; a cached expansion must not carry a firing the exception blocks
  (tu/with-terms [parentOf anc estranged KinContext]
    (v/assert kb (list 'exceptWhen (list estranged '?x)
                       (list 'set/defaultRule
                             (list 'implies (list parentOf '?x '?z) (list anc '?x '?z))))
              KinContext)
    (v/assert kb (list parentOf 'MemoKidA 'MemoParentA) KinContext)
    (v/assert kb (list parentOf 'MemoKidB 'MemoParentA) KinContext)
    (v/assert kb (list estranged 'MemoKidB) KinContext)
    (testing "the excepted child concludes nothing, the other still does"
      (is (= #{'MemoParentA} (set (map #(get % '?z)
                                       (both-ways kb (list anc 'MemoKidA '?z) KinContext)))))
      (is (empty? (both-ways kb (list anc 'MemoKidB '?z) KinContext))))))

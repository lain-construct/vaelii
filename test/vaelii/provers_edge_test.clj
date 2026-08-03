;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.provers-edge-test
  "Prover branches the happy-path tests never reach.

  `provers_test` asks each built-in prover the question it was written for, which
  means every reasoner is exercised in exactly one argument mode — usually
  ground/ground, sometimes with the *first* argument bound.  The other modes are
  separate branches with their own binding maps, and a swapped key there yields
  *wrong answers* rather than an error: an empty result set reads as \"nothing
  matches\", which is indistinguishable from a correct negative.

  Also here: the two recursion/exception guards that `ask` and `backward` own
  privately, which the `prove`-based tests cannot cover."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.rules :as vr]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- bwd [antes conseq]
  (list 'set/backwardRule (vr/rule-sentence antes conseq)))

(defn- binds [sols var] (set (map #(get % var) sols)))

;; ---- the node engine over a cycle ---------------------------------------

(tu/deftest-kb the-node-engine-terminates-on-a-recursive-rule-over-a-cyclic-graph
  ;; `res/prove` terminates on a per-path `seen` guard; the node engine terminates on
  ;; its depth bound, which is a different mechanism reaching the same place.  The
  ;; graph below is cyclic (a→b→a), so an unguarded backward chainer recurses until
  ;; the stack goes.
  (tu/with-terms [edge path A B GraphContext]
    (v/assert kb (list 'genlContext GraphContext 'UniverseContext) 'UniverseContext)
    (v/assert kb (bwd [(list edge '?x '?y)] (list path '?x '?y)) GraphContext)
    (v/assert kb (bwd [(list edge '?x '?y) (list path '?y '?z)]
                      (list path '?x '?z)) GraphContext)
    (v/assert kb (list edge A B) GraphContext)
    (v/assert kb (list edge B A) GraphContext)          ; the cycle
    (testing "it returns rather than looping"
      (let [reached (binds (v/query kb (list path A '?z) GraphContext {:max-depth 4})
                           '?z)]
        (is (contains? reached B) "the direct edge")
        (is (contains? reached A) "and back around the cycle")))
    (testing "and the boolean form terminates too"
      (is (v/query? kb (list path A B) GraphContext {:max-depth 4})))))

;; ---- backward's exceptWhen guard ----------------------------------------

(tu/deftest-kb backward-honours-a-rule-exception-like-the-other-two-chainers
  ;; Both chainers must agree about an exception, or a conclusion's truth depends on
  ;; which one you asked.  `prove`'s guard is a separate `:when` clause from the node
  ;; engine's, so each is checked here.
  (tu/with-terms [bird penguin flies Robin Opus StoryContext]
    (v/assert kb (list 'genlContext StoryContext 'UniverseContext) 'UniverseContext)
    (v/assert kb (list 'genl penguin bird) 'UniverseContext)
    (v/assert kb (list 'exceptWhen (list penguin '?x)
                       (list 'set/backwardRule
                             (vr/rule-sentence [(list bird '?x)] (list flies '?x))))
              StoryContext)
    (v/assert kb (list bird Robin) StoryContext)
    (v/assert kb (list penguin Opus) StoryContext)
    (testing "the ordinary bird flies, by both chainers"
      (is (seq (v/prove kb (list flies Robin) StoryContext)))
      (is (v/provable? kb (list flies Robin) StoryContext))
      (is (v/query? kb (list flies Robin) StoryContext {:max-depth 2})))
    (testing "the penguin does not — each must block it"
      (is (empty? (v/prove kb (list flies Opus) StoryContext))
          "the recursive chainer ignored the exception the node engine honours")
      (is (not (v/provable? kb (list flies Opus) StoryContext)))
      (is (not (v/query? kb (list flies Opus) StoryContext {:max-depth 2}))))))

;; ---- generic relation reasoners, in every argument mode ----------------

(tu/deftest-kb a-transitive-predicate-answers-in-both-argument-directions
  (tu/with-terms [partOf wheel axle machine]
    (v/assert kb (list 'transitive partOf) 'UniverseContext)
    (v/assert kb (list partOf wheel axle) 'UniverseContext)
    (v/assert kb (list partOf axle machine) 'UniverseContext)
    (testing "forward: what is this part of? (the covered direction)"
      (is (contains? (binds (v/ask kb (list partOf wheel '?w) 'UniverseContext) '?w)
                     machine)))
    (testing "reverse: what are the parts of this? (reads the *predecessor* closure)"
      (let [parts (binds (v/ask kb (list partOf '?p machine) 'UniverseContext) '?p)]
        (is (contains? parts axle)  "the direct part")
        (is (contains? parts wheel) "and the transitively reachable one")))
    (testing "ground both ways"
      (is (v/ask? kb (list partOf wheel machine) 'UniverseContext))
      (is (not (v/ask? kb (list partOf machine wheel) 'UniverseContext))))))

(tu/deftest-kb a-reflexive-predicate-binds-either-open-argument-to-the-ground-one
  (tu/with-terms [sameRegionAs Paris Lyon]
    (v/assert kb (list 'reflexive sameRegionAs) 'UniverseContext)
    (testing "ground/ground, both the reflexive case and a non-instance"
      (is (v/ask? kb (list sameRegionAs Paris Paris) 'UniverseContext))
      (is (not (v/ask? kb (list sameRegionAs Paris Lyon) 'UniverseContext))))
    (testing "the open argument binds to the ground one — in whichever slot it sits"
      (is (= #{Paris} (binds (v/ask kb (list sameRegionAs '?x Paris) 'UniverseContext) '?x)))
      (is (= #{Paris} (binds (v/ask kb (list sameRegionAs Paris '?y) 'UniverseContext) '?y))))
    (testing "and a wholly open reflexive goal does not enumerate the universe"
      (is (empty? (v/ask kb (list sameRegionAs '?x '?y) 'UniverseContext))))))

(tu/deftest-kb a-symmetric-predicate-answers-with-either-argument-bound
  (tu/with-terms [siblingOf Ann Bob]
    (v/assert kb (list 'symmetric siblingOf) 'UniverseContext)
    (v/assert kb (list siblingOf Ann Bob) 'UniverseContext)
    (is (v/ask? kb (list siblingOf Bob Ann) 'UniverseContext) "the mirror is provable")
    (is (contains? (binds (v/ask kb (list siblingOf '?s Bob) 'UniverseContext) '?s) Ann))
    (is (contains? (binds (v/ask kb (list siblingOf Bob '?s) 'UniverseContext) '?s) Ann))))

(tu/deftest-kb an-inverse-predicate-answers-through-its-partner
  (tu/with-terms [parentOf childOf Tom Bob]
    (v/assert kb (list 'inverse parentOf childOf) 'UniverseContext)
    (v/assert kb (list parentOf Tom Bob) 'UniverseContext)
    (testing "the inverse goal is answered from the stored direction"
      (is (v/ask? kb (list childOf Bob Tom) 'UniverseContext))
      (is (contains? (binds (v/ask kb (list childOf Bob '?p) 'UniverseContext) '?p) Tom))
      (is (contains? (binds (v/ask kb (list childOf '?c Tom) 'UniverseContext) '?c) Bob)))))

(tu/deftest-kb an-inverse-composes-with-its-partner's-transitivity
  ;; InverseProver delegates the swapped goal to the engine (minus itself and
  ;; backchaining), which is what reaches the closure prover.  Mapping it through raw
  ;; fact matching instead would answer only direct links for a *transitive* partner —
  ;; general to any (inverse P Q) with transitive Q.
  (tu/with-terms [beforeEv afterEv EvA EvB EvC]
    (v/assert kb (list 'transitive beforeEv) 'UniverseContext)
    (v/assert kb (list 'inverse beforeEv afterEv) 'UniverseContext)
    (v/assert kb (list beforeEv EvA EvB) 'UniverseContext)
    (v/assert kb (list beforeEv EvB EvC) 'UniverseContext)
    (testing "the direct inverse still answers"
      (is (v/ask? kb (list afterEv EvB EvA) 'UniverseContext)))
    (testing "and so does the transitively-derived one"
      (is (v/ask? kb (list afterEv EvC EvA) 'UniverseContext))
      (is (contains? (binds (v/ask kb (list afterEv EvC '?e) 'UniverseContext) '?e) EvA)))))

(tu/deftest-kb mutual-inverse-declarations-terminate
  ;; (inverse P Q) and (inverse Q P) both stored: the delegate excludes
  ;; InverseProver itself, so P-via-Q cannot re-enter Q-via-P.
  (tu/with-terms [northOf southOf TownA TownB]
    (v/assert kb (list 'inverse northOf southOf) 'UniverseContext)
    (v/assert kb (list 'inverse southOf northOf) 'UniverseContext)
    (v/assert kb (list northOf TownA TownB) 'UniverseContext)
    (is (v/ask? kb (list southOf TownB TownA) 'UniverseContext))
    (is (not (v/ask? kb (list southOf TownA TownB) 'UniverseContext)))))

;; ---- the taxonomy provers, fully open ----------------------------------

(tu/deftest-kb a-wholly-open-genl-goal-enumerates-pairs-the-right-way-round
  ;; `(genl ?x ?y)` is the both-variable branch: a cross product of every type with
  ;; its own up-closure.  Swapping the two binding keys inverts every answer, and
  ;; nothing else in the suite would notice.
  (tu/with-terms [dog mammal]
    (v/assert kb (list 'genl dog mammal) 'UniverseContext)
    (let [pairs (set (map (juxt #(get % '?x) #(get % '?y))
                          (v/ask kb (list 'genl '?x '?y) 'UniverseContext)))]
      (is (contains? pairs [dog mammal]) "sub before super")
      (is (not (contains? pairs [mammal dog])) "and never the reverse"))))

(tu/deftest-kb disjointness-answers-with-either-argument-bound-or-neither
  (tu/with-terms [dog cat]
    (v/assert kb (list 'disjoint dog cat) 'UniverseContext)
    (testing "the second argument bound — the mirror of the covered case"
      (is (contains? (binds (v/ask kb (list 'disjoint '?t cat) 'UniverseContext) '?t) dog)))
    (testing "both open: the pair is enumerated, in both orders since disjoint is symmetric"
      (let [pairs (set (map (juxt #(get % '?a) #(get % '?b))
                            (v/ask kb (list 'disjoint '?a '?b) 'UniverseContext)))]
        (is (or (contains? pairs [dog cat]) (contains? pairs [cat dog]))
            "the declared pair is reachable with nothing bound")))))

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

;; ---- the transitive walk's step relation --------------------------------
;; The hops a closure walks are the *believed facts* — subsumption and the symmetric
;; mirror included, because `matches-visible` reads those, and the declared inverse,
;; because `(P x y)` and `(Q y x)` are one edge.  Nothing else: a rule's conclusion and
;; a calculus entailment are not on this graph, and `docs/taxonomy.md` says why.

(tu/deftest-kb a-transitive-walk-crosses-a-hop-recorded-on-the-inverse
  ;; `(before a b)` stored, `(after c b)` stored, and `(inverse before after)` makes the
  ;; second one the edge b→c.  Without the partner probe the walk stops at `b` with no
  ;; diagnostic — the path exists and the answer is silently negative.
  (tu/with-terms [beforeEv afterEv EvA EvB EvC]
    (v/assert kb (list 'transitive beforeEv) 'UniverseContext)
    (v/assert kb (list 'inverse beforeEv afterEv) 'UniverseContext)
    (v/assert kb (list beforeEv EvA EvB) 'UniverseContext)
    (v/assert kb (list afterEv EvC EvB) 'UniverseContext)      ; i.e. (beforeEv EvB EvC)
    (is (v/ask? kb (list beforeEv EvA EvC) 'UniverseContext)
        "the chain crosses the hop its middle was written on the partner")
    (is (contains? (binds (v/ask kb (list beforeEv EvA '?y) 'UniverseContext) '?y) EvC)
        "and the open-argument arm reaches it too")
    (is (contains? (binds (v/ask kb (list beforeEv '?x EvC) 'UniverseContext) '?x) EvA)
        "and so does the backward arm")
    (is (contains? (binds (v/ask kb (list afterEv '?x EvA) 'UniverseContext) '?x) EvC)
        "and the partner goal reaches it through the existing delegation")))

(tu/deftest-kb an-alternating-inverse-chain-is-walked-end-to-end
  ;; Five hops, spelling alternating between the predicate and its partner, so a fix
  ;; that crosses one partner hop and stops cannot pass.
  (tu/with-terms [beforeEv afterEv]
    (let [ev (fn [i] (tu/fresh-term :individual (str "Ev" i)))
          es (mapv ev (range 6))]
      (v/assert kb (list 'transitive beforeEv) 'UniverseContext)
      (v/assert kb (list 'inverse beforeEv afterEv) 'UniverseContext)
      (doseq [i (range 1 6)]
        (if (odd? i)
          (v/assert kb (list beforeEv (es (dec i)) (es i)) 'UniverseContext)
          (v/assert kb (list afterEv (es i) (es (dec i))) 'UniverseContext)))
      (is (v/ask? kb (list beforeEv (es 0) (es 5)) 'UniverseContext))
      (is (= (set (rest es))
             (binds (v/ask kb (list beforeEv (es 0) '?y) 'UniverseContext) '?y))
          "the whole reach, whichever spelling each hop was written in")
      (is (not (v/ask? kb (list beforeEv (es 5) (es 0)) 'UniverseContext))
          "and the walk is still directed"))))

(tu/deftest-kb the-mirror-and-the-inverse-do-not-double-count
  ;; A predicate declared symmetric *and* its own inverse is a real shape: both probes
  ;; are the same edge read twice.  Neighbours are collected as a set of terms, so the
  ;; reach is a set and the answer count is one per node.
  (tu/with-terms [nearTo]
    (let [pt (fn [i] (tu/fresh-term :individual (str "Pt" i)))
          ps (mapv pt (range 4))]
      (v/assert kb (list 'symmetric nearTo) 'UniverseContext)
      (v/assert kb (list 'transitive nearTo) 'UniverseContext)
      (v/assert kb (list 'inverse nearTo nearTo) 'UniverseContext)
      (doseq [i (range 1 4)]
        (v/assert kb (list nearTo (ps (dec i)) (ps i)) 'UniverseContext))
      (let [sols (v/ask kb (list nearTo (ps 0) '?y) 'UniverseContext)]
        (is (= (set ps) (binds sols '?y)) "the whole class, both directions")
        (is (= (count (set sols)) (count sols)) "and each member once")))))

;; ---- two declared inverses, and the order they arrived in ----------------
;; Nothing refuses a second `(inverse P R)` beside a standing `(inverse P Q)`, so the
;; taxonomy holds a *set* per predicate and the walk probes every member.  A single-valued
;; entry would answer whichever landed last, which puts a hop's visibility — and so an
;; `ask`'s answer — at the mercy of declaration order, against the order independence the
;; README states as an invariant.

(defn- two-inverse-chain!
  "`(transitive beforeEv)`, both partners declared **in the order given**, and a two-hop
  chain whose middle hop is written on `afterEv`.  Answers whether the chain closes.

  Fresh temporaries per call, so two orderings run in one KB without either seeing the
  other's declarations."
  [kb partner-order]
  (let [before (tu/fresh-term :predicate  "beforeEv")
        after  (tu/fresh-term :predicate  "afterEv")
        subseq (tu/fresh-term :predicate  "subsequentToEv")
        [a b c] (mapv #(tu/fresh-term :individual (str "Ev" %)) ["A" "B" "C"])]
    (v/assert kb (list 'transitive before) 'UniverseContext)
    (doseq [q (case partner-order
                :partner-first  [after subseq]
                :partner-second [subseq after])]
      (v/assert kb (list 'inverse before q) 'UniverseContext))
    (v/assert kb (list before a b) 'UniverseContext)
    (v/assert kb (list after c b) 'UniverseContext)          ; i.e. (before b c)
    (boolean (v/ask? kb (list before a c) 'UniverseContext))))

(tu/deftest-kb a-second-declared-inverse-does-not-hide-the-first
  (let [first-decl  (two-inverse-chain! kb :partner-first)
        second-decl (two-inverse-chain! kb :partner-second)]
    (is (true? first-decl)
        "the hop written on the partner is on the graph with the partner declared first")
    (is (= first-decl second-decl)
        (str "and with it declared second — the same knowledge in either order answers "
             "the same, which is what a set per predicate buys and a last-writer-wins "
             "entry cannot"))))

(tu/deftest-kb retracting-one-inverse-declaration-leaves-the-other-honoured
  ;; Dropping `(inverse P R)` must leave `P → #{Q}` rather than clearing `P`: the
  ;; remaining declaration is still believed, and a reader that stopped seeing it would
  ;; have one prover honouring a declaration another ignores.
  (tu/with-terms [beforeEv afterEv subsequentToEv EvA EvB EvC]
    (v/assert kb (list 'transitive beforeEv) 'UniverseContext)
    (let [h1 (v/assert kb (list 'inverse beforeEv afterEv) 'UniverseContext)
          h2 (v/assert kb (list 'inverse beforeEv subsequentToEv) 'UniverseContext)]
      (v/assert kb (list beforeEv EvA EvB) 'UniverseContext)
      (v/assert kb (list afterEv EvC EvB) 'UniverseContext)
      (is (v/ask? kb (list beforeEv EvA EvC) 'UniverseContext) "both declared")
      (v/retract! kb h2)
      (is (v/in? kb h1) "the other declaration is untouched")
      (is (= afterEv (v/inverse-of kb beforeEv))
          "and the taxonomy still reports it, rather than having cleared the entry")
      (is (= beforeEv (v/inverse-of kb afterEv))
          "in both directions, so no reader sees a half-declared pair")
      (is (v/ask? kb (list beforeEv EvA EvC) 'UniverseContext)
          "so the hop it licenses is still a hop"))))

;; ---- the one-variable closure goal --------------------------------------

(tu/deftest-kb a-both-slots-one-variable-goal-asks-which-nodes-lie-on-a-cycle
  (tu/with-terms [reachesEv]
    (let [ev (fn [i] (tu/fresh-term :individual (str "Cy" i)))
          es (mapv ev (range 5))]
      (v/assert kb (list 'transitive reachesEv) 'UniverseContext)
      ;; 0→1→2→0 is a cycle; 3→4 is a tail hanging off nothing
      (v/assert kb (list reachesEv (es 0) (es 1)) 'UniverseContext)
      (v/assert kb (list reachesEv (es 1) (es 2)) 'UniverseContext)
      (v/assert kb (list reachesEv (es 2) (es 0)) 'UniverseContext)
      (v/assert kb (list reachesEv (es 3) (es 4)) 'UniverseContext)
      (is (= #{(es 0) (es 1) (es 2)}
             (binds (v/ask kb (list reachesEv '?x '?x) 'UniverseContext) '?x))
          "the component's members, and nothing off it"))))

(tu/deftest-kb an-acyclic-chain-answers-the-one-variable-goal-with-nothing
  ;; The shape the condensation exists for: asking each source whether it reaches itself
  ;; walks that source's whole reach to fail, so a chain would cost O(n²) to answer
  ;; nothing.  One pass over the graph answers every source at once.
  (tu/with-terms [reachesEv]
    (let [ev (fn [i] (tu/fresh-term :individual (str "Ac" i)))
          es (mapv ev (range 40))]
      (v/assert kb (list 'transitive reachesEv) 'UniverseContext)
      (doseq [i (range 1 40)]
        (v/assert kb (list reachesEv (es (dec i)) (es i)) 'UniverseContext))
      (is (empty? (v/ask kb (list reachesEv '?x '?x) 'UniverseContext))
          "no node on an acyclic chain reaches itself"))))

(tu/deftest-kb the-cycle-goal-ranks-terms-that-are-not-comparable
  ;; The bindings a walk yields are **terms**, and a term need not be `Comparable`: an
  ;; unreifiable function application stays structural in argument position, so a binding
  ;; can be a list.  Ranking them with a bare `sort` throws `ClassCastException` — printed
  ;; form is the key, which every term has.
  (tu/with-terms [sameSizeAs quantityOf Meter Centimeter]
    (v/assert kb (list 'unreifiableFunction quantityOf) 'UniverseContext)
    (v/assert kb (list 'transitive sameSizeAs) 'UniverseContext)
    (let [a (list quantityOf 5 Meter)
          b (list quantityOf 500 Centimeter)]
      ;; a two-member cycle, so the ranking is actually exercised — a one-element sort
      ;; never calls `compare` and would pass whatever the key
      (v/assert kb (list sameSizeAs a b) 'UniverseContext)
      (v/assert kb (list sameSizeAs b a) 'UniverseContext)
      (is (= #{a b} (binds (v/ask kb (list sameSizeAs '?x '?x) 'UniverseContext) '?x))
          "both members of the cycle come back, and ranking them does not throw"))))

(tu/deftest-kb a-self-edge-is-its-own-cycle
  ;; A singleton component is cyclic only through a self-edge, which a condensation does
  ;; not report — so it is tested at the source rather than left to the components.
  (tu/with-terms [reachesEv Loop Other]
    (v/assert kb (list 'transitive reachesEv) 'UniverseContext)
    (v/assert kb (list reachesEv Loop Loop) 'UniverseContext)
    (v/assert kb (list reachesEv Other Loop) 'UniverseContext)
    (is (= #{Loop} (binds (v/ask kb (list reachesEv '?x '?x) 'UniverseContext) '?x)))))

(tu/deftest-kb a-symmetric-transitive-class-needs-only-one-direction-of-each-edge
  ;; The equivalence-class shape: one direction of each edge asserted, `symmetric` and
  ;; `transitive` declared, and the class read from any member.  Asserting both
  ;; directions must not change the answer — the composition is what computes the class,
  ;; not the data being written twice.
  (tu/with-terms [wqEq]
    (let [m  (fn [i] (tu/fresh-term :individual (str "M" i)))
          ms (mapv m (range 5))
          class-from (fn [probe]
                       (conj (binds (v/ask kb (list wqEq probe '?y) 'UniverseContext) '?y)
                             probe))]
      (v/assert kb (list 'symmetric wqEq) 'UniverseContext)
      (v/assert kb (list 'transitive wqEq) 'UniverseContext)
      (doseq [i (range 1 5)]
        (v/assert kb (list wqEq (ms (dec i)) (ms i)) 'UniverseContext))
      (is (= (set ms) (class-from (ms 0))) "from one end")
      (is (= (set ms) (class-from (ms 2))) "and from the middle")
      (doseq [i (range 1 5)]                                   ; now the other direction too
        (v/assert kb (list wqEq (ms i) (ms (dec i))) 'UniverseContext))
      (is (= (set ms) (class-from (ms 2))) "and materializing the mirror changes nothing"))))

(tu/deftest-kb a-backward-rule-hop-is-not-on-the-transitive-graph
  ;; The step relation reads believed facts, never the registry: nothing may start an
  ;; unbounded proof search from inside a walk that a relabel loop can reach.  So a
  ;; `backwardRule` concluding the middle hop leaves the chain broken, and that is the
  ;; documented contract rather than a bug (`docs/taxonomy.md`, "the step relation").
  (tu/with-terms [beforeEv precedes EvA EvB EvC]
    (v/assert kb (list 'transitive beforeEv) 'UniverseContext)
    (v/assert kb (list beforeEv EvA EvB) 'UniverseContext)
    (v/assert kb (list precedes EvB EvC) 'UniverseContext)
    (v/assert kb (bwd [(list precedes '?x '?y)] (list beforeEv '?x '?y)) 'UniverseContext)
    (is (seq (v/prove kb (list beforeEv EvB EvC) 'UniverseContext))
        "a backward search answers the hop as a goal")
    (is (not (v/ask? kb (list beforeEv EvA EvC) 'UniverseContext))
        "and the walk does not chain through it")))

;; ---- the transitive walk with nothing bound ----------------------------

(tu/deftest-kb a-wholly-open-transitive-goal-is-the-extent-and-not-the-closure
  ;; `(P ?x ?y)` asks what the relation holds, and the answer is the same one every other
  ;; predicate gives: the stored facts and those of `P`'s sub-predicates.  The closure is
  ;; **not** enumerated, and the asymmetry with the one-bound-end arms is the point — a
  ;; closure is quadratic in a chain's length, so a fully-open ask that returned it would
  ;; offer half a trillion pairs on a 1M-node chain instead of coming back.
  (tu/with-terms [largerThan hugelyLargerThan]
    (let [r  (fn [i] (tu/fresh-term :individual (str "R" i)))
          rs (mapv r (range 4))]
      (v/assert kb (list 'transitive largerThan) 'UniverseContext)
      (v/assert kb (list 'genl hugelyLargerThan largerThan) 'UniverseContext)
      (doseq [i (range 1 4)]
        (v/assert kb (list largerThan (rs (dec i)) (rs i)) 'UniverseContext))
      ;; one fact of a sub-predicate, which the extent must reach and the chain must not
      (v/assert kb (list hugelyLargerThan (rs 0) (rs 3)) 'UniverseContext)
      (let [mine (fn [goal]
                   (->> (v/ask kb goal 'UniverseContext)
                        (map (juxt #(get % '?x) #(get % '?y)))
                        (filter (fn [[x y]] (and (some #{x} rs) (some #{y} rs))))
                        set))]
        (testing "the asserted links, plus the asserted sub-predicate's, and nothing derived"
          (is (= #{[(rs 0) (rs 1)] [(rs 1) (rs 2)] [(rs 2) (rs 3)]   ; stored largerThan
                   [(rs 0) (rs 3)]}                                  ; stored spec-pred
                 (mine (list largerThan '?x '?y)))))
        (testing "and the derived pairs are still there for a caller who binds an end"
          ;; the same knowledge, asked the bounded way: R0 reaches everything downstream
          (is (= #{(rs 1) (rs 2) (rs 3)}
                 (set (filter (set rs)
                              (binds (v/ask kb (list largerThan (rs 0) '?y) 'UniverseContext)
                                     '?y)))))
          (is (v/ask? kb (list largerThan (rs 0) (rs 2)) 'UniverseContext)
              "a two-hop pair no fact records"))
        (testing "a sub-predicate's own extent does not gain the parent's links"
          (is (= #{[(rs 0) (rs 3)]} (mine (list hugelyLargerThan '?x '?y)))))))))

(tu/deftest-kb a-transitive-goal-with-one-variable-twice-asks-which-nodes-are-cyclic
  ;; `(P ?x ?x)` binds one variable, not two — the `Duplicate key` shape.  A transitive
  ;; relation does entail reflexivity around a loop, so the answer is the cycle.
  (tu/with-terms [nextTo A B C D]
    (v/assert kb (list 'transitive nextTo) 'UniverseContext)
    (v/assert kb (list nextTo A B) 'UniverseContext)
    (v/assert kb (list nextTo B C) 'UniverseContext)
    (v/assert kb (list nextTo C A) 'UniverseContext)               ; the cycle
    (v/assert kb (list nextTo C D) 'UniverseContext)               ; and a tail off it
    (let [xs (binds (v/ask kb (list nextTo '?x '?x) 'UniverseContext) '?x)]
      (is (= #{A B C} (set (filter #{A B C D} xs))) "the loop, and not the tail"))))

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

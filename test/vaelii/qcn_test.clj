;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.qcn-test
  "The generic qualitative-constraint-network engine (`vaelii.impl.qcn`), tested
  against a **hand-built** algebra and network — no KB, no context, no belief.  That
  is the point of the namespace: path consistency is data in, data out, and the
  relation algebra is a parameter, so an algebra invented for a test exercises the
  engine exactly as RCC-8 does.

  The toy algebra here is the order relation on points — `#{:lt :eq :gt}` — whose
  composition table is small enough to read: `lt∘lt = lt`, `lt∘gt` is unconstrained,
  `eq` is the identity."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.impl.projection :as proj]
            [vaelii.impl.qcn :as qcn]))

;; ---- a toy point algebra ------------------------------------------------

(def ^:private universe #{:lt :eq :gt})

(def ^:private converse-rel {:lt :gt, :eq :eq, :gt :lt})

(def ^:private composition
  "`(get-in composition [r1 r2])` — what can hold between x and z given r1(x,y) and
  r2(y,z).  Composing opposite strict orders says nothing."
  {:lt {:lt #{:lt}    :eq #{:lt}    :gt universe}
   :eq {:lt #{:lt}    :eq #{:eq}    :gt #{:gt}}
   :gt {:lt universe  :eq #{:gt}    :gt #{:gt}}})

(defn- compose-sets [s1 s2]
  (into #{} (mapcat (fn [a] (mapcat (fn [b] (get-in composition [a b])) s2))) s1))

(defn- converse-set [rels] (into #{} (map converse-rel) rels))

(def ^:private point-algebra
  {:universe universe
   :identity #{:eq}
   :compose  compose-sets
   :converse converse-set})

(defn- net
  "Build a network from `[i j rels]` triples, storing both directions the way an
  algebra's reader does."
  [& entries]
  (reduce (fn [n [i j rels]]
            (assoc n [i j] rels [j i] (converse-set rels)))
          {}
          entries))

(defn- permutations [coll]
  (if (seq (rest coll))
    (for [i (range (count coll))
          p (permutations (concat (take i coll) (drop (inc i) coll)))]
      (cons (nth coll i) p))
    [coll]))

;; ---- constraint ---------------------------------------------------------

(deftest constraint-reads-diagonal-recorded-and-unknown
  (let [n (net ['A 'B #{:lt}])]
    (testing "the diagonal is the algebra's identity, recorded or not"
      (is (= #{:eq} (qcn/constraint n point-algebra 'A 'A)))
      (is (= #{:eq} (qcn/constraint n point-algebra 'Z 'Z))
          "even for a node the network never mentions"))
    (testing "a recorded pair reads back, in both directions"
      (is (= #{:lt} (qcn/constraint n point-algebra 'A 'B)))
      (is (= #{:gt} (qcn/constraint n point-algebra 'B 'A))))
    (testing "an unrecorded pair is the universe — unknown, not empty"
      (is (= universe (qcn/constraint n point-algebra 'A 'Q))))))

;; ---- tightening ---------------------------------------------------------

(deftest path-consistency-tightens-a-chain
  (testing "A<B and B<C pins A?C to lt, which nothing asserted"
    (let [n  (net ['A 'B #{:lt}] ['B 'C #{:lt}])
          pc (qcn/path-consistent n '[A B C] point-algebra)]
      (is (not= :inconsistent pc))
      (is (= #{:lt} (qcn/constraint pc point-algebra 'A 'C)))
      (is (= #{:gt} (qcn/constraint pc point-algebra 'C 'A))
          "the converse is written on every tightening, so it needs no second pass"))))

(deftest path-consistency-tightens-a-disjunction
  (testing "a disjunctive constraint narrows to what composition permits"
    ;; A <|= B, B < C  ⇒  A < C  (both disjuncts compose to lt)
    (let [n  (net ['A 'B #{:lt :eq}] ['B 'C #{:lt}])
          pc (qcn/path-consistent n '[A B C] point-algebra)]
      (is (= #{:lt} (qcn/constraint pc point-algebra 'A 'C)))
      (is (= #{:lt :eq} (qcn/constraint pc point-algebra 'A 'B))
          "the asserted constraint itself is not narrowed by this network"))))

(deftest path-consistency-propagates-across-a-longer-chain
  (testing "the fixpoint carries a tightening derived in one pass into the next"
    (let [n  (net ['A 'B #{:lt}] ['B 'C #{:lt}] ['C 'D #{:lt}] ['D 'E #{:lt}])
          pc (qcn/path-consistent n '[A B C D E] point-algebra)]
      (is (= #{:lt} (qcn/constraint pc point-algebra 'A 'E))
          "A<E is four compositions away, so only iterating to a fixpoint finds it"))))

(deftest the-result-does-not-depend-on-the-order-of-the-nodes
  ;; the engine's share of the KB-wide order-independence invariant.  Tightening only
  ;; narrows and composition is monotone, so the loop lands on the unique greatest
  ;; fixpoint below the network it was handed; node order decides how many passes that
  ;; takes and nothing else.
  (let [n       (net ['A 'B #{:lt}] ['B 'C #{:lt :eq}] ['C 'D #{:lt}])
        results (set (for [order (permutations '[A B C D])]
                       (qcn/path-consistent n order point-algebra)))]
    (is (= 1 (count results)) "all 24 orders agree, constraint for constraint")
    (is (= #{:lt} (qcn/constraint (first results) point-algebra 'A 'D))))
  (testing "and neither does the inconsistency verdict"
    (let [n (net ['A 'B #{:lt}] ['B 'C #{:lt}] ['C 'A #{:lt}])]
      (is (every? #(= :inconsistent (qcn/path-consistent n % point-algebra))
                  (permutations '[A B C]))))))

(deftest only-the-nodes-it-is-given-are-tightened-through
  ;; `nodes` is where the triples come from, so a node the network mentions but the
  ;; caller leaves out is a composition left unmade.  Both algebras therefore pass the
  ;; network's own nodes plus whatever the goal names; this is the contract that makes
  ;; that mandatory rather than habitual.
  (let [n (net ['A 'B #{:lt}] ['B 'C #{:lt}])]
    (is (= #{:lt} (qcn/constraint (qcn/path-consistent n '[A B C] point-algebra)
                                  point-algebra 'A 'C))
        "with B passed, the chain composes")
    (is (= universe (qcn/constraint (qcn/path-consistent n '[A C] point-algebra)
                                    point-algebra 'A 'C))
        "without it, A?C is never visited and stays unknown — silently weaker, not wrong")))

(deftest an-unrelated-node-changes-nothing
  (testing "an isolated node has universe constraints, and the universe composes to itself"
    (let [n     (net ['A 'B #{:lt}] ['B 'C #{:lt}])
          with  (qcn/path-consistent n '[A B C Z] point-algebra)
          alone (qcn/path-consistent n '[A B C] point-algebra)]
      (is (= alone with)
          "so memoizing the pass on the network alone, ignoring extra nodes, is sound")
      (is (= universe (qcn/constraint with point-algebra 'A 'Z))))))

;; ---- inconsistency ------------------------------------------------------

(deftest an-emptied-constraint-is-inconsistent
  (testing "A<B, B<C, and C<A cannot all hold: the cycle empties a constraint"
    (let [n (net ['A 'B #{:lt}] ['B 'C #{:lt}] ['C 'A #{:lt}])]
      (is (= :inconsistent (qcn/path-consistent n '[A B C] point-algebra)))))
  (testing "a constraint handed in already empty is inconsistent on its own"
    ;; the reader intersects two facts about one pair into #{} before the pass runs;
    ;; nothing can tighten it further, so only the up-front check reports it — and it
    ;; must report it whether or not a third node happens to route through the pair
    (let [two (assoc (net ['A 'B #{:lt}]) [:x :y] #{} [:y :x] #{})]
      (is (= :inconsistent (qcn/path-consistent two '[:x :y] point-algebra))
          "two nodes generate no triple at all"))
    (let [many (assoc (net ['A 'B #{:lt}] ['B 'C #{:lt}]) [:x :y] #{} [:y :x] #{})]
      (is (= :inconsistent (qcn/path-consistent many '[A B C :x :y] point-algebra))))))

(deftest an-empty-constraint-is-caught-whatever-nodes-are-passed
  ;; the emptiness scan reads the network, not the node list — an unsatisfiable pair is
  ;; unsatisfiable whether or not the caller asked about it
  (let [n (assoc (net ['A 'B #{:lt}]) [:x :y] #{} [:y :x] #{})]
    (is (= :inconsistent (qcn/path-consistent n '[A B] point-algebra))
        ":x and :y are not in the node list, and it still reports the contradiction")))

(deftest a-diagonal-claim-that-excludes-the-identity-is-inconsistent
  ;; no triple ever visits a diagonal (every triple has i ≠ k) and `constraint` answers
  ;; the identity there whatever is recorded, so a self-assertion the algebra forbids
  ;; would be silently dropped rather than reported.  A reader produces one whenever an
  ;; asserted (P a a) survives intersection with its own converse — which is exactly when
  ;; P is symmetric, e.g. RCC-8's DC: no region is disconnected from itself.
  (testing "a node cannot stand to itself in a relation the identity excludes"
    (is (= :inconsistent (qcn/path-consistent {['A 'A] #{:lt}} '[A] point-algebra)))
    (is (= :inconsistent (qcn/path-consistent {['A 'A] #{:lt :gt}} '[A] point-algebra))))
  (testing "but a diagonal claim that admits the identity is satisfiable, and the
            identity is what reads back"
    (let [n  {['A 'A] #{:lt :eq}}
          pc (qcn/path-consistent n '[A] point-algebra)]
      (is (not= :inconsistent pc))
      (is (= #{:eq} (qcn/constraint pc point-algebra 'A 'A))
          "the diagonal is the identity, not the wider set recorded on it"))))

(deftest a-network-with-nothing-to-do-comes-back-unchanged
  (testing "an empty network over no nodes is its own fixpoint"
    (is (= {} (qcn/path-consistent {} [] point-algebra))))
  (testing "a single constraint has no triple to tighten it"
    (let [n (net ['A 'B #{:lt}])]
      (is (= n (qcn/path-consistent n '[A B] point-algebra))))))

(deftest the-identity-relation-composes-transparently
  (testing "an eq edge passes a constraint through unchanged"
    (let [n  (net ['A 'B #{:eq}] ['B 'C #{:lt}])
          pc (qcn/path-consistent n '[A B C] point-algebra)]
      (is (= #{:lt} (qcn/constraint pc point-algebra 'A 'C))))))

;; ---- an algebra derived from two axes rather than written out -----------
;;
;; The algebra above is a parameter, and `vaelii.impl.projection/algebra` is the other
;; way to obtain one: give it each relation's `[x y]` projection onto two independent
;; point axes and it derives the composition and converse a nine-relation table would
;; otherwise state in 81 cells.  The derivation is total only while the projection is a
;; **bijection** onto the nine pairs, so that is checked where the algebra is built —
;; the engine here would otherwise store a composed `nil` as though it were a relation.

(deftest a-projection-that-is-not-a-bijection-is-refused-where-the-algebra-is-built
  (let [relations [:r1 :r2 :r3 :r4 :r5 :r6 :r7 :r8 :r9]
        pairs     (for [x [:lt :eq :gt] y [:lt :eq :gt]] [x y])
        bijection (zipmap relations pairs)]
    (testing "a bijection derives an algebra this engine runs"
      (let [alg (proj/algebra bijection)]
        (is (= (set relations) (:universe alg)))
        (is (= #{:r5} (:identity alg)) "the relation projecting to [:eq :eq]")
        ;; `:r1` is [:lt :lt] and `:r9` is its converse [:gt :gt]; `:r5` is the identity,
        ;; so composing A-r1-B with B-r5-C has to leave A?C at r1
        (let [n  {['A 'B] #{:r1} ['B 'A] #{:r9} ['B 'C] #{:r5} ['C 'B] #{:r5}}
              pc (qcn/path-consistent n '[A B C] alg)]
          (is (= #{:r1} (qcn/constraint pc alg 'A 'C))
              "composing through the identity leaves the relation as it was"))))
    (testing "a repeated pair still covers all nine, and is refused on the count"
      (let [e (is (thrown? clojure.lang.ExceptionInfo
                           (proj/algebra (assoc bijection :r10 [:lt :lt]))))]
        (is (= :bad-algebra (:type (ex-data e))))
        (is (= [[:lt :lt]] (:repeated (ex-data e)))
            "naming the pair two relations share, which map-invert would drop one of")))
    (testing "and a pair nothing projects to is refused on the coverage"
      (let [e (is (thrown? clojure.lang.ExceptionInfo
                           (proj/algebra (dissoc bijection :r1))))]
        (is (= :bad-algebra (:type (ex-data e))))
        (is (= [[:lt :lt]] (:missing (ex-data e)))
            "naming the pair a composition would have answered nil for")))))

;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.stp-incremental-test
  "The warm-started metric closure against the pass it replaces — a parity oracle, not a
  behaviour test.

  `stp/close` runs Floyd–Warshall over the whole distance graph.  `stp/close-state-from`
  takes a closed state for a network the new one **tightens** and relaxes in only the
  constraints that moved.  They must agree on **every** input: the same closed network,
  bound for bound, and
  the same inconsistency verdict — because the closure is the least-weight path between
  every pair, which is a property of the constraint *set* and not of the order the
  constraints were read in.  That is [order independence](../../docs/nmtms.md) as the metric
  layer states it, and it is the whole licence for warm-starting at all: a KB loading one
  fact at a time closes incrementally, and a KB recovered from a dump closes from nothing,
  and the two must answer the same thing.

  So the property is stated over **orders**: one generated constraint set, three
  permutations of it, each folded in one constraint at a time with every step warm-started
  off the last, all checked against a single run from nothing.  The networks are small and
  the magnitudes are tight, so a good share of them are unsatisfiable and the verdict path
  is exercised as hard as the fixpoint — `both-verdicts-are-generated` is what holds that
  claim to account rather than assuming it.

  **Magnitudes are integers**, and that is a claim about what is being tested rather than a
  convenience.  Min-plus is associative and the two routes sum the same path in different
  bracketings, so with arbitrary doubles they can disagree in the last bit of a figure they
  agree about mathematically.  Integers inside 2⁵³ add exactly, so a difference here is a
  difference in the *algorithm*.  What covers the rest is the engine's own tolerance band:
  every verdict `close` reads is read to `provers/*quantity-tolerance*`, and every stated
  magnitude is snapped to a grid before it arrives ([stp.md](../../docs/stp.md), \"Both
  verdicts are read to the tolerance\")."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.test.check.clojure-test :refer [defspec]]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [vaelii.impl.stp :as stp]))

;; ---- generated networks --------------------------------------------------

(defn- instant [i] (symbol (str "Ti" i)))

(defn- gen-constraint
  "A bound on the gap between two distinct instants of an `n`-instant network.  The range is
  deliberately narrow — a handful of constraints drawn from ±6 contradict each other often,
  which is what puts the inconsistency verdict under the same load as the fixpoint."
  [n]
  (gen/let [p  (gen/choose 0 (dec n))
            d  (gen/choose 1 (dec n))
            a  (gen/choose -6 6)
            b  (gen/choose -6 6)]
    [(instant p) (instant (mod (+ p d) n)) (min a b) (max a b)]))

(def ^:private gen-network
  (gen/let [n           (gen/choose 3 8)
            constraints (gen/vector-distinct-by identity (gen-constraint n)
                                                {:min-elements 1 :max-elements 16})
            orders      (gen/vector (gen/shuffle constraints) 3)]
    {:nodes       (into #{} (map instant) (range n))
     :constraints constraints
     :orders      orders}))

;; ---- the two routes ------------------------------------------------------

(defn- net-of
  "The stated network `constraints` describe, whatever order they arrive in."
  [constraints]
  (reduce (fn [net [p q lo hi]] (stp/narrow net p q lo hi)) {} constraints))

(defn- close-incrementally
  "Close `constraints` one at a time, every step warm-started off the last — the shape a KB
  reaches when facts arrive one by one.

  A step that comes back `:inconsistent` ends the fold, and that is the answer: constraints
  only ever tighten, so a set that cannot be satisfied stays unsatisfiable however much is
  added to it, and there is no closed prior for a further step to start from."
  [constraints nodes]
  (loop [net {}, state (stp/close-state {} nodes), [c & more] constraints]
    (if (nil? c)
      (:net state)
      (let [[p q lo hi] c
            net'        (stp/narrow net p q lo hi)
            state'      (stp/close-state-from net' state nodes)]
        (if (= :inconsistent state')
          :inconsistent
          (recur net' state' more))))))

(defn- close-in-batches
  "Close `constraints` in batches — several relaxed into the last closure at *once*, the
  shape a KB reaches when a bulk load lands many facts before the next query.  This is the
  multi-edge warm-start `close-incrementally` never reaches (it folds one edge a step, so
  `moved` is never more than two), and it is the only route that exercises
  `close-state-from`'s many-edge relaxation and its `(>= (count moved) n)` full-recompute
  fallback.  An `:inconsistent` batch ends the fold and is the answer, for the reason a
  single inconsistent constraint is."
  [constraints nodes]
  (let [size (max 2 (quot (inc (count constraints)) 2))]     ; ~two batches, never singletons
    (loop [net {}, state (stp/close-state {} nodes), cs (vec constraints)]
      (if (empty? cs)
        (:net state)
        (let [[batch more] (split-at size cs)
              net'   (reduce (fn [n [p q lo hi]] (stp/narrow n p q lo hi)) net batch)
              state' (stp/close-state-from net' state nodes)]
          (if (= :inconsistent state')
            :inconsistent
            (recur net' state' (vec more))))))))

(defn- orders-agree-with-one-pass?
  "Every permutation reaching what one pass from nothing reaches — the closed network and
  the verdict alike, and the stated network on the way — folded both one constraint at a
  time and in multi-edge batches, so the single- and many-edge warm-start paths are held to
  the same from-scratch answer."
  [{:keys [nodes constraints orders]}]
  (let [net      (net-of constraints)
        expected (stp/close net nodes)]
    (every? (fn [order]
              (and (= net (net-of order))
                   (= expected (close-incrementally order nodes))
                   (= expected (close-in-batches order nodes))))
            orders)))

;; ---- the property --------------------------------------------------------

;; The seed is fixed, so the four hundred networks drawn here are the same four hundred on
;; every machine and every run: a red is reproducible from the failure alone, which is what
;; makes this a check to run before landing rather than a source of flakes.  What a fixed
;; seed cannot do is find a shape nobody has drawn yet, so the `^:slow` run below leaves it
;; to the clock.  A counterexample from either shrinks to the same minimal constraint list.
(defspec incremental-closure-equals-one-pass-in-every-order
  {:num-tests 400 :seed 20260824}
  (prop/for-all [network gen-network]
                (orders-agree-with-one-pass? network)))

(defspec ^:slow incremental-closure-equals-one-pass-over-a-wider-search
  2000
  (prop/for-all [network gen-network]
                (orders-agree-with-one-pass? network)))

;; ---- the generator is asked to account for itself ------------------------

(deftest both-verdicts-are-generated
  (testing "the draw really does produce satisfiable and unsatisfiable networks — a
            property that only ever saw one of the two would pass without testing the other"
    (let [verdicts (frequencies
                    (for [{:keys [nodes constraints]} (gen/sample gen-network 200)]
                      (if (= :inconsistent (stp/close (net-of constraints) nodes))
                        :inconsistent
                        :closed)))]
      (is (pos? (get verdicts :closed 0)))
      (is (pos? (get verdicts :inconsistent 0))))))

(deftest a-widening-is-not-a-tightening
  (testing "the precondition refuses the direction that has no warm start"
    (let [tight (-> {} (stp/narrow 'Ta 'Tb 5 10))
          loose (-> {} (stp/narrow 'Ta 'Tb 0 20))]
      (is (stp/tightening-of? tight loose))
      (is (not (stp/tightening-of? loose tight)))))
  (testing "a pair the new network does not record at all is unbounded there, so it tightens
            nothing"
    (is (not (stp/tightening-of? {} (-> {} (stp/narrow 'Ta 'Tb 5 10)))))
    (is (stp/tightening-of? (-> {} (stp/narrow 'Ta 'Tb 5 10)) {}))))

(deftest an-instant-the-prior-never-saw-joins-the-network
  (testing "a constraint naming an instant the prior state's matrix has no row for is
            relaxed into a matrix laid out afresh, and composes with what was there"
    (let [net-1   (-> {} (stp/narrow 'Ta 'Tb 10 10))
          state1  (stp/close-state net-1 (stp/nodes net-1))
          net-2   (stp/narrow net-1 'Tb 'Tc 5 5)
          nodes   (stp/nodes net-2)
          warm    (stp/close-state-from net-2 state1 nodes)]
      (is (= '[Ta Tb Tc] (:node-vec warm)))
      (is (= (stp/close net-2 nodes) (:net warm)))
      (is (= [15 15] (stp/constraint (:net warm) 'Ta 'Tc))))))

;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.stp-incremental-test
  "`stp/close-state-from` against `stp/close` over generated networks: three orders of each
  constraint set, folded one constraint and one batch at a time with every step
  warm-started off the last, must reach the one-pass closure and verdict (docs/stp.md,
  \"Warm-starting\").

  Magnitudes are integers because the two routes sum one path in different bracketings,
  and only integers inside 2⁵³ make that sum exact."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.test.check.clojure-test :refer [defspec]]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [vaelii.impl.stp :as stp]))

;; ---- generated networks --------------------------------------------------

(defn- instant [i] (symbol (str "Ti" i)))

(defn- gen-constraint
  "A bound on the gap between two distinct instants of an `n`-instant network, drawn from
  ±6 so that a handful of them contradict each other often."
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
  "Close `constraints` one at a time, each step warm-started off the last over the instants
  named so far, so an arriving instant re-lays the matrix.  An `:inconsistent` step ends
  the fold: a tightening never makes an unsatisfiable set satisfiable."
  [constraints]
  (loop [net {}, state (stp/close-state {} #{}), [c & more] constraints]
    (if (nil? c)
      (:net state)
      (let [[p q lo hi] c
            net'        (stp/narrow net p q lo hi)
            state'      (stp/close-state-from net' state (stp/nodes net'))]
        (if (= :inconsistent state')
          :inconsistent
          (recur net' state' more))))))

(defn- close-in-batches
  "`close-incrementally` over batches of about half the constraints, which reaches
  `close-state-from`'s many-edge relaxation and its full-pass fallback."
  [constraints]
  (let [size (max 2 (quot (inc (count constraints)) 2))]     ; ~two batches, never singletons
    (loop [net {}, state (stp/close-state {} #{}), cs (vec constraints)]
      (if (empty? cs)
        (:net state)
        (let [[batch more] (split-at size cs)
              net'   (reduce (fn [n [p q lo hi]] (stp/narrow n p q lo hi)) net batch)
              state' (stp/close-state-from net' state (stp/nodes net'))]
          (if (= :inconsistent state')
            :inconsistent
            (recur net' state' (vec more))))))))

(defn- orders-agree-with-one-pass?
  "Does every order reach the one-pass stated network, closure and verdict, folded both
  ways?"
  [{:keys [nodes constraints orders]}]
  (let [net      (net-of constraints)
        expected (stp/close net nodes)]
    (every? (fn [order]
              (and (= net (net-of order))
                   (= expected (close-incrementally order))
                   (= expected (close-in-batches order))))
            orders)))

;; ---- the property --------------------------------------------------------

;; A fixed seed makes a red reproducible; the `^:slow` twin draws unseeded.
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
  (testing "the draw produces satisfiable and unsatisfiable networks"
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
  (testing "a pair the new network does not record is unbounded there"
    (is (not (stp/tightening-of? {} (-> {} (stp/narrow 'Ta 'Tb 5 10)))))
    (is (stp/tightening-of? (-> {} (stp/narrow 'Ta 'Tb 5 10)) {}))))

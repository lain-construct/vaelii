;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.guard-moves-test
  "The guarded rules a settle's moves reach (`res/guard-moves`) read the rules watching a
  predicate once per predicate.

  A handle whose label moved selects the rules watching its functor or a predicate above
  it.  A `recover` moves every record's label, and reading the functor's genls and the
  rules watching each of them per handle costs a `genl` read per handle in
  `finish-settle`.  The rules selected must be the ones the
  per-handle read selects."
  (:require [clojure.test :refer [deftest is]]
            [vaelii.core :as v]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(defn- by-handle
  "The rules of `all` watching each moved handle's functor or a predicate above it, read
  per handle."
  [kb all touched]
  (let [tms (reasoning/tms kb)
        was (jtms/touched-in tms)
        tax (reasoning/taxonomy kb)]
    (into #{}
          (mapcat (fn [h]
                    (when (not= (contains? was h) (boolean (jtms/in? tms h)))
                      (when-let [f (some-> (p/get-sentex (:records kb) h) :sentence nm/functor)]
                        (filter #(contains? all %)
                                (mapcat #(reads/watched-rules-on (:index kb) %)
                                        (tax/genls-global tax f)))))))
          touched)))

(defn- world!
  "Six predicates in a chain, three tuples of each, and the predicates two rules watch."
  [kb]
  (let [ps (vec (repeatedly 6 #(tu/fresh-term :predicate 'gmRel)))]
    (doseq [[a b] (partition 2 1 ps)] (v/assert kb (list 'genl a b) 'CxUniverse))
    [ps (into [] (for [p ps, _ (range 3)]
                   (v/assert kb (list p (tu/fresh-term :individual 'Thing)) 'CxUniverse)))]))

(deftest a-settle-s-moves-select-the-rules-a-per-handle-read-selects
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (let [[ps hs]  (world! kb)
          watching {(ps 2) [:r2] (ps 4) [:r4 :r5]}
          all      #{:r2 :r4}]
      (with-redefs [reads/watched-rules-on (fn [_ pred] (get watching pred))]
        ;; every pair of functors' tuples, so a functor whose watchers differ from the
        ;; other's is read in the same call
        (doseq [touched (concat [(set hs) #{}]
                                (for [i (range 6), j (range i 6)]
                                  (set (concat (subvec hs (* 3 i) (* 3 (inc i)))
                                               (subvec hs (* 3 j) (* 3 (inc j)))))))]
          (is (= (by-handle kb all touched)
                 (:rules (res/guard-moves kb all #{} touched)))
              (str (count touched) " handles")))))))

(deftest a-settle-s-moves-read-each-predicate-s-watchers-once
  ;; eighteen moved handles over a chain of six functors read each predicate's postings
  ;; once and build no closure, where a read per handle reads the chain above each
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (let [[ps hs] (world! kb)
          tms     (reasoning/tms kb)
          moved   (into #{} (filter #(not= (contains? (jtms/touched-in tms) %) (boolean (jtms/in? tms %))))
                        hs)
          reads   (atom 0)
          genls   (atom 0)
          real    tax/genls-global]
      (is (= 18 (count moved)) "every tuple's label moved in the window")
      (with-redefs [reads/watched-rules-on (fn [_ pred] (swap! reads inc) (when (= pred (ps 3)) [:r3]))
                    tax/genls-global       (fn [& a] (swap! genls inc) (apply real a))]
        (is (= #{:r3} (:rules (res/guard-moves kb #{:r3} #{} (set hs))))))
      (is (zero? @genls) "no functor's closure is built")
      (is (<= @reads 7) (str @reads " posting reads for six predicates and thing")))))

;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.converse-candidates-test
  "The converse half of the candidate index (`:converse`, `:self`) as a rebuild finds it.

  A live store reads a tuple's converses off the index, one trie read per converse
  functor (`tuple/stored-converses`).  `rebuild-candidates!` keeps the tuples by their
  arguments instead and joins them once the replay has seen every record
  (`tuple/converse-pairs`).  The two must agree: the rebuilt index equals the one live
  stores built, and equals a rebuild that reads each tuple's converses off the index as
  a live store does."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.decide :as decide]
            [vaelii.impl.decide.tuple :as tuple]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(defn- converse-half
  "The converse and self entries of `kb`'s candidate index."
  [kb]
  (let [c @(reasoning/nogood-candidates kb)]
    {:converse (set (:converse c)) :self (set (:self c))}))

(defn- random-stream
  "A seeded shuffle of predicate `genl` edges, `anti_symmetric` marks, and binary tuples
  over symbols, strings and numbers: many converse pairs across related predicates, self
  tuples, and a share stored inert."
  [^java.util.Random rnd]
  (let [pick  (fn [v] (v (.nextInt rnd (count v))))
        preds (vec (repeatedly 6 #(tu/fresh-term :predicate 'rel)))
        args  (into (vec (repeatedly 4 #(tu/fresh-term :individual 'Thing))) ["one" "two" 3 4])
        edge  (fn [] (let [i (.nextInt rnd (count preds))
                           j (+ i (.nextInt rnd (- (count preds) i)))]
                       (when (not= i j) [:assert (list 'genl (preds i) (preds j))])))
        tuple (fn [] (let [q (pick preds), a (pick args), b (pick args)]
                       [(if (< (.nextInt rnd 5) 1) :inert :assert) (list q a b)]))
        conv  (fn [[k [_ a b]]] [k (list (pick preds) b a)])
        ts    (vec (repeatedly 30 tuple))]
    (->> (concat (keep (fn [_] (edge)) (range 5))
                 (repeatedly (.nextInt rnd 3) (fn [] [:assert (list 'anti_symmetric (pick preds))]))
                 ts
                 ;; a converse under a random functor for half the tuples, so pairs are common
                 (map conv (filter (fn [_] (< (.nextInt rnd 2) 1)) ts)))
         (sort-by (fn [_] (.nextInt rnd))))))

(defn- store-all! [kb stream]
  (doseq [[k s] stream]
    ;; a refused sentence is simply not stored
    (try (if (= :inert k)
           (v/assert-inert kb s 'CxUniverse)
           (v/assert kb s 'CxUniverse))
         (catch clojure.lang.ExceptionInfo _))))

(defn- trie-converse-pairs
  "`converse-pairs` as a live store answers it: each kept tuple reads its converses off
  the index (`stored-converses`)."
  [kb w tuples]
  (let [stored (deref #'tuple/stored-converses)]
    (into #{}
          (mapcat (fn [[[a b] es]]
                    (mapcat (fn [[q h]] (map #(hash-set h %) (stored kb w h q a b))) es)))
          tuples)))

(deftest a-rebuild-joins-the-converses-a-live-store-reads
  (let [rnd  (java.util.Random. 1729)
        seen (atom {:converse 0 :self 0 :marked 0})]
    (doseq [deferred? [false true], trial (range 12)]
      (tu/with-neutral-kb [kb tu/isolated-fresh]
        (let [stream (random-stream rnd)
              where  (str (if deferred? "deferred" "plain") " trial " trial)]
          (if deferred?
            (v/with-deferred-settle kb (store-all! kb stream))
            (store-all! kb stream))
          (let [live (converse-half kb)]
            (swap! seen #(merge-with + % {:converse (count (:converse live))
                                          :self     (count (:self live))
                                          :marked   (if (some (fn [[_ s]] (= 'anti_symmetric (first s))) stream) 1 0)}))
            (decide/rebuild-candidates! kb)
            (let [rebuilt @(reasoning/nogood-candidates kb)]
              (testing "the rebuild finds what live stores built"
                (is (= live (converse-half kb)) where))
              (testing "and what a rebuild reading each tuple's converses off the index finds"
                (with-redefs [tuple/converse-pairs (partial trie-converse-pairs kb)]
                  (decide/rebuild-candidates! kb))
                (is (= rebuilt @(reasoning/nogood-candidates kb)) where)))))))
    (is (every? pos? (vals @seen)) (str "the streams reach pairs, self tuples and marks: " @seen))))

(deftest a-rebuild-reads-no-converse-off-the-index
  ;; A converse read is a sentence and a trie lookup per converse functor, for every
  ;; ground binary tuple: half of a large KB's recover before the join.
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (let [[p q]   (repeatedly 2 #(tu/fresh-term :predicate 'rel))
          [a b c] (repeatedly 3 #(tu/fresh-term :individual 'Thing))]
      (v/assert kb (list 'anti_symmetric p) 'CxUniverse)
      (v/assert kb (list 'genl q p) 'CxUniverse)
      (v/assert kb (list p a b) 'CxUniverse)
      (v/assert kb (list q b a) 'CxUniverse)
      (v/assert kb (list p a c) 'CxUniverse)
      (v/assert kb (list p "x" c) 'CxUniverse)
      (let [before (converse-half kb)
            reads  (atom 0)
            real   (deref #'tuple/converse-handles)]
        (with-redefs [tuple/converse-handles (fn [& xs] (swap! reads inc) (apply real xs))]
          (decide/rebuild-candidates! kb))
        (is (zero? @reads) "no converse is read off the index")
        (is (= before (converse-half kb)) "and the index is the one live stores built")
        (is (= #{(v/handle-of kb (list p a b) 'CxUniverse) (v/handle-of kb (list q b a) 'CxUniverse)}
               (:converse before))
            "which holds the pair across the predicate edge and nothing else")))))

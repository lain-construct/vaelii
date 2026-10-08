;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.converse-candidates-test
  "The converse half of the candidate index (`:converse`) as a rebuild finds it.

  A live store reads a tuple's converses off the index, one trie read per converse
  functor (`tuple/stored-converses`), and `rebuild-candidates!` offers the stored facts
  of the predicates under a converse mark the same way.  The rebuilt index equals the one
  live stores built."
  (:require [clojure.test :refer [deftest is]]
            [vaelii.core :as v]
            [vaelii.impl.decide :as decide]
            [vaelii.impl.decide.tuple :as tuple]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(defn- converse-half
  "The converse entries of `kb`'s candidate index."
  [kb]
  {:converse (set (:converse @(reasoning/nogood-candidates kb)))})

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

(deftest a-rebuild-reads-the-converses-a-live-store-reads
  (let [rnd  (java.util.Random. 1729)
        seen (atom {:converse 0 :marked 0})]
    (doseq [deferred? [false true], trial (range 12)]
      (tu/with-neutral-kb [kb tu/isolated-fresh]
        (let [stream (random-stream rnd)
              where  (str (if deferred? "deferred" "plain") " trial " trial)]
          (if deferred?
            (v/with-deferred-settle kb (store-all! kb stream))
            (store-all! kb stream))
          (let [live (converse-half kb)]
            (swap! seen #(merge-with + % {:converse (count (:converse live))
                                          :marked   (if (some (fn [[_ s]] (= 'anti_symmetric (first s))) stream) 1 0)}))
            (decide/rebuild-candidates! kb)
            (is (= live (converse-half kb)) where)))))
    (is (every? pos? (vals @seen)) (str "the streams reach pairs and marks: " @seen))))

(deftest a-rebuild-reads-the-converses-of-the-tuples-under-a-mark-only
  ;; recover offers the facts of the predicates under a converse mark, one converse read
  ;; per tuple, and reads no tuple of an unmarked predicate
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (let [[p q r] (repeatedly 3 #(tu/fresh-term :predicate 'rel))
          [a b c] (repeatedly 3 #(tu/fresh-term :individual 'Thing))]
      (v/assert kb (list 'anti_symmetric p) 'CxUniverse)
      (v/assert kb (list 'genl q p) 'CxUniverse)
      (v/assert kb (list p a b) 'CxUniverse)
      (v/assert kb (list q b a) 'CxUniverse)
      (v/assert kb (list p a c) 'CxUniverse)
      (v/assert kb (list p "x" c) 'CxUniverse)
      (v/assert kb (list r a b) 'CxUniverse)
      (v/assert kb (list r b a) 'CxUniverse)
      (let [before (converse-half kb)
            reads  (atom 0)
            real   (deref #'tuple/converse-handles)]
        (with-redefs [tuple/converse-handles (fn [& xs] (swap! reads inc) (apply real xs))]
          (decide/rebuild-candidates! kb))
        (is (= 4 @reads) "one read for each tuple of the marked predicate and the one below it")
        (is (= before (converse-half kb)) "and the index is the one live stores built")
        (is (= #{(v/handle-of kb (list p a b) 'CxUniverse) (v/handle-of kb (list q b a) 'CxUniverse)}
               (:converse before))
            "which holds the pair across the predicate edge and nothing else")))))

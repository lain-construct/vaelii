;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.mint-candidates-test
  "The mints a moved `genlCx` edge can have made redundant are the ones stated in a
  context under its `sub` that sees it.

  `special/withdrawal-candidates` reads them off whichever of the mint roster's contexts
  and `sub`'s descendants is fewer.  A `recover` moves every `genlCx` edge, and filtering
  every descendant of every edge by what it sees costs a `sees?` walk per descendant even
  when the roster names a handful of contexts.  The candidates must
  be the ones `tax/context-down` gives."
  (:require [clojure.test :refer [deftest is]]
            [vaelii.core :as v]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.special :as special]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(defn- by-definition
  "The candidates a `genlCx` record `sx` names, read off `tax/context-down` of its `sub`."
  [kb sx]
  (let [by (:by-context @(reasoning/minted kb))]
    (set (for [c (tax/context-down (reasoning/taxonomy kb) (second (:sentence sx)))
               h (get by c)]
           [h nil]))))

(defn- context-edges [kb]
  (into [] (comp (keep #(p/get-sentex (:records kb) %))
                 (filter #(and (nil? (:antecedent %)) (seq? (:sentence %))
                               (= 'genlCx (first (:sentence %))))))
        (p/sentex-ids (:records kb))))

(defn- world!
  "Contexts in a random lattice under CxUniverse, an `except` on one `genlCx` edge in
  some worlds so a context's view is filtered, and a mint in some contexts: `(arg rel 1
  kind)` with a `rel` fact there mints `(kind x)`."
  [kb ^java.util.Random rnd]
  (let [ctxs (vec (repeatedly 9 #(tu/fresh-term :context 'CxMc)))
        kind (tu/fresh-term :type 'mc_t)
        rel  (tu/fresh-term :predicate 'mcRel)
        try! (fn [s c] (try (v/assert kb s c) (catch clojure.lang.ExceptionInfo _)))]
    (try! (list 'genl kind 'thing) 'CxUniverse)
    (try! (list 'arg rel 1 kind) 'CxUniverse)
    (doseq [i (range (count ctxs))]
      (try! (list 'genlCx (ctxs i) (if (zero? i) 'CxUniverse (ctxs (.nextInt rnd i)))) 'CxUniverse)
      (when (and (pos? i) (< (.nextInt rnd 3) 1))
        (try! (list 'genlCx (ctxs i) (ctxs (.nextInt rnd i))) 'CxUniverse)))
    (when (zero? (.nextInt rnd 2))
      (let [i (inc (.nextInt rnd (dec (count ctxs))))
            e (first (filter #(= (ctxs i) (second (:sentence %))) (context-edges kb)))]
        (when e (try! (list 'except (list 'sentexHandle (:id e))) (ctxs (.nextInt rnd (count ctxs)))))))
    (dotimes [_ 4]
      (try! (list rel (tu/fresh-term :individual 'Thing) (tu/fresh-term :individual 'Thing))
            (ctxs (.nextInt rnd (count ctxs)))))
    ctxs))

(deftest a-moved-context-edge-names-the-mints-context-down-reaches
  (let [rnd  (java.util.Random. 8821)
        seen (atom 0)]
    (dotimes [trial 12]
      (tu/with-neutral-kb [kb tu/isolated-fresh]
        (binding [checks/*assertive-arg-types?* true
                  checks/*prune-subsumed-mints?* true]
          (world! kb rnd)
          (doseq [sx (context-edges kb)
                  :let [want (by-definition kb sx)]]
            (swap! seen + (count want))
            (is (= want (set (@#'special/withdrawal-candidates kb sx)))
                (str "trial " trial " " (:sentence sx)))))))
    (is (pos? @seen) "the worlds hold mints under some moved edge")))

(deftest a-moved-context-edge-asks-only-the-contexts-holding-a-mint
  ;; thirty contexts under CxMcTop and a mint in one of them, and an `except` on an
  ;; unrelated `genlCx` edge, so a context's view is filtered: the edge into CxMcTop asks
  ;; what that one context sees, not what every descendant does
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (binding [checks/*assertive-arg-types?* true
              checks/*prune-subsumed-mints?* true]
      (let [top  (tu/fresh-term :context 'CxMcTop)
            subs (vec (repeatedly 30 #(tu/fresh-term :context 'CxMc)))
            kind (tu/fresh-term :type 'mc_t)
            rel  (tu/fresh-term :predicate 'mcRel)]
        (v/assert kb (list 'genlCx top 'CxUniverse) 'CxUniverse)
        (doseq [c subs] (v/assert kb (list 'genlCx c top) 'CxUniverse))
        (let [[a b] (repeatedly 2 #(tu/fresh-term :context 'CxMcAside))
              e     (v/assert kb (list 'genlCx a 'CxUniverse) 'CxUniverse)]
          (v/assert kb (list 'genlCx b a) 'CxUniverse)
          (v/assert kb (list 'except (list 'sentexHandle e)) b))
        (v/assert kb (list 'genl kind 'thing) 'CxUniverse)
        (v/assert kb (list 'arg rel 1 kind) 'CxUniverse)
        (v/assert kb (list rel 'McFred 'McMary) (first subs))
        (is (seq (:by-context @(reasoning/minted kb))) "the fact mints a membership")
        (let [sx    (first (filter #(= top (second (:sentence %))) (context-edges kb)))
              asks  (atom 0)
              real  tax/sees?
              ;; read before the definition, whose `context-down` would fill the memo
              got   (with-redefs [tax/sees? (fn [& a] (swap! asks inc) (apply real a))]
                      (set (@#'special/withdrawal-candidates kb sx)))
              want  (by-definition kb sx)]
          (is (= 1 (count want)) "the edge reaches the one mint")
          (is (= want got))
          (is (<= @asks 2) (str @asks " visibility asks for one mint context")))))))

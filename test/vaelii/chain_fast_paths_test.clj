;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.chain-fast-paths-test
  "The placement fast paths against their reference paths (`observe/*chain-fast-paths*`).

  Forward chaining leans on three fast paths — the justification dedup index
  (`jtms/*dedup-cache*`), the `ensure-node` no-op skip, and the single-context
  placement answer in `taxonomy/maximal-common-descendant-contexts` — and each claims
  to compute exactly what its reference path computes.  This pins that claim the way
  `arg_root_retrieval_test` pins retrieval: the same knowledge chained under both
  bindings must reach the identical fixpoint, compared on **content** (sentence,
  context, truth, strength, belief; a justification's consequence, informant and
  antecedents as content), never on handles.

  The load is a miniature join pyramid shaped to exercise what the fast paths skip:
  a conclusion re-derived through several witnesses (the dedup index's case), firings
  whose ingredients sit in one context (the placement fast exit) and firings that
  span two (the general path beside it), and placements at more than one depth (the
  `ensure-node` skip)."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.rules :as vr]
            [vaelii.test-util :as tu]))

(defn- fwd [antes conseq]
  (list 'set/forwardRule (vr/rule-sentence antes conseq)))

(defn- fixpoint-content
  "The KB's whole derived state, handle-free and sorted: every stored sentex as
  [sentence context truth strength believed?], every justification with its
  consequence, informant and antecedents mapped from handles to [sentence context]."
  [kb]
  (let [recs (:records kb)
        tms  (:tms kb)
        sent (fn [h] (let [s (p/get-sentex recs h)] [(:sentence s) (:context s)]))]
    {:sentexes
     (sort-by pr-str
              (map (fn [id]
                     (let [s (p/get-sentex recs id)]
                       [(:sentence s) (:context s) (:truth s) (:strength s)
                        (boolean (jtms/in? tms id))]))
                   (p/sentex-ids recs)))
     :justifications
     (sort-by pr-str
              (map (fn [j]
                     [(sent (:consequence j))
                      (if (integer? (:informant j)) (sent (:informant j)) (:informant j))
                      (set (map sent (:antecedents j)))
                      (:strength j)])
                   (jtms/justifications tms)))}))

(deftest the-fast-paths-and-the-reference-derive-the-identical-fixpoint
  (tu/with-terms [pa qa ra sa CxTopStory CxSubStory X Y Z1 Z2 Z3 W]
    (let [load! (fn [kb]
                  ;; the sub-context sees the top one, so a firing whose ingredients
                  ;; span both takes the general placement path while an all-in-one
                  ;; firing takes the single-context fast exit
                  (v/assert kb (list 'genlCx CxSubStory CxTopStory)
                            'CxUniverse {:strength :monotonic})
                  (v/assert kb (fwd [(list pa '?x '?z) (list qa '?z '?y)]
                                    (list ra '?x '?y))
                            CxTopStory {:chain? false})
                  (v/assert kb (fwd [(list ra '?x '?y) (list qa '?y '?w)]
                                    (list sa '?x '?w))
                            CxTopStory {:chain? false})
                  ;; ra(X,Y) through three witnesses — pa in the top context, qa in
                  ;; the sub, so each of these firings spans the two contexts
                  (doseq [z [Z1 Z2 Z3]]
                    (v/assert kb (list pa X z) CxTopStory {:chain? false})
                    (v/assert kb (list qa z Y) CxSubStory {:chain? false}))
                  ;; a second-level firing, and a pair wholly inside the top context
                  (v/assert kb (list qa Y W) CxTopStory {:chain? false})
                  (v/assert kb (list pa Y Z3) CxTopStory {:chain? false})
                  (v/assert kb (list qa Z3 W) CxTopStory {:chain? false}))
          run   (fn [fast?]
                  (tu/with-cleared-kb [kb tu/fresh]
                    (load! kb)
                    (binding [observe/*chain-fast-paths* fast?]
                      (v/forward-chain kb {}))
                    (fixpoint-content kb)))
          fast  (run true)
          slow  (run false)]
      (testing "sentex content"
        (is (= (:sentexes fast) (:sentexes slow))))
      (testing "justification content"
        (is (= (:justifications fast) (:justifications slow))))
      (testing "the load re-derives through several witnesses"
        (is (= 3 (count (filter (fn [[[sentence _] _ _ _]]
                                  (= sentence (list ra X Y)))
                                (:justifications fast))))
            "ra(X,Y) is justified once per witness, never more")))))

;; ---- the dedup index's coherence transitions ----------------------------
;; Bare TMSes, no KB: the transitions under test are jtms-internal, and handle
;; numbers can be spelled directly.

(deftest a-removal-clears-a-bound-dedup-index
  (let [tms (jtms/create-tms)]
    (jtms/add-premise tms 1 :monotonic)
    (jtms/add-premise tms 2 :monotonic)
    (jtms/ensure-node tms 3 1)
    (jtms/with-dedup-cache tms
      (is (false? (jtms/has-justification? tms 9 [1 2] 3))
          "the first ask builds the entry, empty")
      (jtms/add-justification tms (jtms/->just 100 9 [1 2] 3 {} :monotonic))
      (is (true? (jtms/has-justification? tms 9 [1 2] 3))
          "the add extends the built entry")
      (jtms/retract! tms 1)
      (is (false? (jtms/has-justification? tms 9 [1 2] 3))
          "the retraction cleared the index, and the rebuild reads the supports that remain"))))

(deftest a-dedup-index-answers-only-its-own-tms
  ;; two TMSes allocate the same small handle numbers, so an index reused across
  ;; them would answer one's dedup question from the other's supports
  (let [t1 (jtms/create-tms)
        t2 (jtms/create-tms)]
    (doseq [t [t1 t2]]
      (jtms/add-premise t 1 :monotonic)
      (jtms/add-premise t 2 :monotonic)
      (jtms/ensure-node t 3 1))
    (jtms/with-dedup-cache t1
      (is (false? (jtms/has-justification? t1 9 [1 2] 3))
          "t1's entry for consequence 3 is built, empty")
      (jtms/with-dedup-cache t2
        (jtms/add-justification t2 (jtms/->just 100 9 [1 2] 3 {} :monotonic))
        (is (true? (jtms/has-justification? t2 9 [1 2] 3))
            "t2's answer comes from t2's supports, not t1's cached emptiness"))
      (is (false? (jtms/has-justification? t1 9 [1 2] 3))
          "and t1's view is untouched by t2's traffic"))))

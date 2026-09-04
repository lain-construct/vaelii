;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.target-following-meta-test
  "`target_following_predicate`: a meta-sentex that names a sentex by handle and is torn
  down when that sentex is retracted — the cascade koinii's reply edges ride, and the
  reason retracting a claim collapses the replies about it, which a message bus cannot do.

  The mark is **opt-in**, so the engine's own meta-sentexes (`except` / `exceptWhen`,
  `meta_sentex_test`) are untouched: a predicate that does not carry it orphans harmlessly
  on retraction exactly as before."
  (:require [clojure.test :refer [is use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.sentex :as sx]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- ctx!
  "A fresh context lifted under CxWell, the way `meta_sentex_test` sets one up."
  [kb]
  (let [c (tu/tmp-ctx "K")]
    (v/assert kb (list 'genlCx c 'CxWell) 'CxUniverse {:strength :monotonic})
    c))

(defn- mark-following!
  "Declare `pred` a target-following meta predicate; return the mark's handle."
  [kb pred]
  (v/assert kb (list 'target_following_predicate pred) 'CxUniverse))

;; ---- the declaration marks the property ---------------------------------

(tu/deftest-kb the-declaration-marks-the-predicate
  (is (not (v/has-prop? kb :target-following 'endorses)) "undeclared: not target-following")
  (mark-following! kb 'endorses)
  (is (v/has-prop? kb :target-following 'endorses) "declared: the property is marked")
  (is (contains? (v/props kb :target-following) 'endorses) "and it shows in the roster"))

;; ---- the cascade: a reply edge does not outlive its target --------------

(tu/deftest-kb a-target-following-meta-is-torn-down-with-its-target
  (let [c (ctx! kb)]
    (mark-following! kb 'endorses)
    (let [p  (v/assert kb (list 'trusts 'AgentAtlas 'Oracle) c)
          eh (v/assert kb (list 'endorses 'AgentBoreas (sx/sentex-handle p)) c)]
      (is (some? (v/sentex kb eh)) "the endorsement is stored, naming the claim by handle")
      (v/retract! kb p)
      (is (nil? (v/sentex kb p))  "the target claim is gone")
      (is (nil? (v/sentex kb eh)) "and the endorsement cascaded with it — no dangling edge"))))

(tu/deftest-kb every-endorsement-of-one-claim-cascades
  (let [c (ctx! kb)]
    (mark-following! kb 'endorses)
    (let [p  (v/assert kb (list 'trusts 'AgentAtlas 'Oracle) c)
          e1 (v/assert kb (list 'endorses 'AgentBoreas (sx/sentex-handle p)) c)
          e2 (v/assert kb (list 'endorses 'AgentCiel   (sx/sentex-handle p)) c)]
      (is (not= e1 e2) "two endorsers are two distinct meta-sentexes (first-writer-wins clears)")
      (v/retract! kb p)
      (is (nil? (v/sentex kb e1)))
      (is (nil? (v/sentex kb e2)) "both endorsements went with the claim"))))

;; ---- opt-in: an unmarked meta predicate still orphans harmlessly --------

(tu/deftest-kb an-unmarked-meta-predicate-orphans-harmlessly
  ;; `mentions` is deliberately NOT declared target_following_predicate — this is the
  ;; property that keeps `except` / `exceptWhen` behaviour unchanged by construction.
  (let [c (ctx! kb)]
    (let [p  (v/assert kb (list 'trusts 'AgentAtlas 'Oracle) c)
          mh (v/assert kb (list 'mentions 'AgentBoreas (sx/sentex-handle p)) c)]
      (v/retract! kb p)
      (is (nil?  (v/sentex kb p))  "the target is gone")
      (is (some? (v/sentex kb mh)) "an unmarked meta survives as a harmless orphan"))))

;; ---- the cascade is recursive: an endorsement of an endorsement ---------

(tu/deftest-kb the-cascade-is-recursive
  (let [c (ctx! kb)]
    (mark-following! kb 'endorses)
    (let [p  (v/assert kb (list 'trusts 'AgentAtlas 'Oracle) c)
          e1 (v/assert kb (list 'endorses 'AgentBoreas (sx/sentex-handle p))  c)
          e2 (v/assert kb (list 'endorses 'AgentCiel   (sx/sentex-handle e1)) c)]
      (v/retract! kb p)
      (is (nil? (v/sentex kb e1)) "the endorsement cascaded")
      (is (nil? (v/sentex kb e2)) "and the endorsement-of-the-endorsement cascaded too"))))

;; ---- isolation: only the retracted claim's edges go --------------------

(tu/deftest-kb an-endorsement-of-another-claim-is-untouched
  (let [c (ctx! kb)]
    (mark-following! kb 'endorses)
    (let [p  (v/assert kb (list 'trusts 'AgentAtlas 'Oracle) c)
          q  (v/assert kb (list 'trusts 'AgentAtlas 'Sage)   c)
          ep (v/assert kb (list 'endorses 'AgentBoreas (sx/sentex-handle p)) c)
          eq (v/assert kb (list 'endorses 'AgentBoreas (sx/sentex-handle q)) c)]
      (v/retract! kb p)
      (is (nil?  (v/sentex kb ep)) "the endorsement of the retracted claim is gone")
      (is (some? (v/sentex kb q))  "a different claim is untouched")
      (is (some? (v/sentex kb eq)) "and its endorsement survives"))))

;; ---- the mark is belief-following: lift it and the cascade stops --------

(tu/deftest-kb unmarking-the-predicate-lifts-the-cascade
  (let [c (ctx! kb)]
    (let [mh (mark-following! kb 'endorses)
          p  (v/assert kb (list 'trusts 'AgentAtlas 'Oracle) c)
          eh (v/assert kb (list 'endorses 'AgentBoreas (sx/sentex-handle p)) c)]
      (is (v/has-prop? kb :target-following 'endorses))
      (v/retract! kb mh)
      (is (not (v/has-prop? kb :target-following 'endorses)) "the mark is belief-following")
      (v/retract! kb p)
      (is (some? (v/sentex kb eh)) "with the mark lifted, the endorsement no longer cascades"))))

;; ---- durability: the cascade and the mark survive a recover ------------

(tu/deftest-kb the-cascade-and-the-mark-survive-recover
  (let [c (ctx! kb)]
    (mark-following! kb 'endorses)
    (let [p  (v/assert kb (list 'trusts 'AgentAtlas 'Oracle) c)
          eh (v/assert kb (list 'endorses 'AgentBoreas (sx/sentex-handle p)) c)]
      (v/retract! kb p)
      (is (nil? (v/sentex kb eh)))
      (v/recover kb)
      (is (nil? (v/sentex kb eh)) "recover does not resurrect the cascaded endorsement")
      (is (v/has-prop? kb :target-following 'endorses) "and the mark itself survives recover"))))

;; ---- the batch entry point cascades too ---------------------------------------

(tu/deftest-kb the-cascade-fires-through-edit!
  (let [c (ctx! kb)]
    (mark-following! kb 'endorses)
    (let [p  (v/assert kb (list 'trusts 'AgentAtlas 'Oracle) c)
          eh (v/assert kb (list 'endorses 'AgentBoreas (sx/sentex-handle p)) c)]
      (v/edit! kb {:remove [p]})
      (is (nil? (v/sentex kb p)))
      (is (nil? (v/sentex kb eh)) "a batch retract cascades the endorsement too"))))

;; ---- a reply follows its claim through a merge --------------------------
;; A target-following meta names a claim by handle, so a merge that restates the claim as
;; a twin must carry the reply onto the twin — in both arrival orders — the same way an
;; `except` or `exceptWhen` does (docs/equality.md, round two).  Belief-following: the
;; reply twin rests on the merge and collapses with it.

(tu/deftest-kb a-reply-follows-its-claim-when-the-claim-migrates-first
  (let [c (ctx! kb)]
    (mark-following! kb 'endorses)
    (let [near (tu/tmp-pred) home (tu/tmp-ind) oldp (tu/tmp-ind) newp (tu/tmp-ind)
          p    (v/assert kb (list near home oldp) c)]
      (v/assert kb (list 'endorses 'AgentBoreas (sx/sentex-handle p)) c)
      (v/assert kb (list 'rewriteOf newp oldp) c {:strength :monotonic})  ; claim migrates
      (let [twin (kb/find-sentex-handle kb (list near home newp) c)]
        (is (some? twin) "the claim migrated to a twin under the representative")
        (is (some? (kb/find-sentex-handle kb (list 'endorses 'AgentBoreas (sx/sentex-handle twin)) c))
            "the endorsement was carried onto the twin claim")))))

(tu/deftest-kb a-reply-asserted-after-the-merge-lands-on-the-twin
  (let [c (ctx! kb)]
    (mark-following! kb 'endorses)
    (let [near (tu/tmp-pred) home (tu/tmp-ind) oldp (tu/tmp-ind) newp (tu/tmp-ind)
          p    (v/assert kb (list near home oldp) c)]
      (v/assert kb (list 'rewriteOf newp oldp) c {:strength :monotonic})  ; migrate FIRST
      (v/assert kb (list 'endorses 'AgentBoreas (sx/sentex-handle p)) c)            ; endorse the dead original
      (let [twin (kb/find-sentex-handle kb (list near home newp) c)]
        (is (some? twin) "the claim has a live twin")
        (is (some? (kb/find-sentex-handle kb (list 'endorses 'AgentBoreas (sx/sentex-handle twin)) c))
            "the late endorsement re-points onto the live twin claim")))))

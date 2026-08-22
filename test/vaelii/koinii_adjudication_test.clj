;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.koinii-adjudication-test
  "Koinii adjudication: the default leave-open-and-notify policy, the
  open->notified->resolved(+stale) lifecycle with a timeout sweep, and reversible arbiter
  escalation.  A client wrapper over the dispute reads — it changes belief only through ordinary
  asserts/retracts and never touches settle."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.core-context :as core-context]
            [vaelii.impl.koinii.adjudication :as adj]
            [vaelii.impl.koinii.dispute :as d]
            [vaelii.impl.koinii.identity :as id]
            [vaelii.impl.koinii.speech-acts :as sa]
            [vaelii.impl.sentex :as sx]
            [vaelii.test-util :as tu]))

(defn- adj-kb [] (doto (tu/fresh) (core-context/load-into)))
(use-fixtures :each (tu/neutral-fresh adj-kb))

(def P '(reliable ProdCluster))
(def not-P '(not (reliable ProdCluster)))
(def t0 1750000000000)

(defn- holds!
  ([kb agent claim] (holds! kb agent claim :default))
  ([kb agent claim strength]
   (v/assert kb claim (id/context-for agent) {:creator agent :strength strength})))

(defn- clash!
  "Atlas holds P and Boreas holds ¬P (both :default), stamped at `t0`; channel CxDeploy
  sees both — the canonical open dispute.  Returns the dispute id."
  [kb]
  (binding [v/*clock* (constantly t0)]
    (holds! kb 'AgentAtlas P)
    (holds! kb 'AgentBoreas not-P)
    (doseq [a '[AgentAtlas AgentBoreas]]
      (v/assert kb (list 'genlCx 'CxDeploy (id/context-for a)) 'CxUniverse {:strength :monotonic})))
  (:dispute-id (first (d/disputes-in kb 'CxDeploy))))

;; ---- the default: a dispute opens and the KB stays honest ----------------

(tu/deftest-kb notify-records-the-dispute-and-changes-no-belief
  (clash! kb)
  (let [before-contras (count (v/contradictions kb))
        pushed (atom [])]
    (testing "the open dispute is a real, paraconsistent contradiction"
      (is (d/disputed? kb P 'CxDeploy))
      (is (= :contradiction (:verdict (v/argue kb P 'CxDeploy))))
      (is (v/ask? kb P 'CxDeploy))
      (is (v/ask? kb not-P 'CxDeploy)))
    (binding [adj/*notify-sink* #(swap! pushed conj %)]
      (let [notified (adj/notify-disputes kb 'CxDeploy)]
        (testing "notify pushes it and records notified — touching no belief"
          (is (= 1 (count notified)))
          (is (= 1 (count @pushed)) "the sink received the dispute")
          (is (= (:dispute-id (first notified)) (:dispute-id (first @pushed))))
          (is (v/ask? kb P 'CxDeploy) "P still believed")
          (is (v/ask? kb not-P 'CxDeploy) "¬P still believed")
          (is (= before-contras (count (v/contradictions kb))) "the clash is untouched")
          (is (= :contradiction (:verdict (v/argue kb P 'CxDeploy)))))))))

(tu/deftest-kb notify-fires-once-across-a-redelivery
  (clash! kb)
  (let [pushed (atom [])]
    (binding [adj/*notify-sink* #(swap! pushed conj %)]
      (adj/notify-disputes kb 'CxDeploy)                 ; first delivery
      (adj/notify-disputes kb 'CxDeploy)                 ; a catch-up / redelivery
      (adj/notify-disputes kb 'CxDeploy))
    (testing "the stored notified mark dedupes: the subscriber hears it exactly once"
      (is (= 1 (count @pushed))))))

(tu/deftest-kb poll-notifies-then-sweeps-in-one-tick
  (clash! kb)                                              ; opened at t0
  (let [pushed (atom []) swept (atom [])]
    (binding [adj/*timeout-ms* 1000
              adj/*notify-sink* #(swap! pushed conj %)
              adj/*stale-sink*  #(swap! swept conj %)
              v/*clock* (constantly (+ t0 2000))]
      (let [{:keys [notified stale]} (adj/poll kb 'CxDeploy)]
        (testing "one tick both announces the fresh dispute and sweeps it stale"
          (is (= 1 (count notified)))
          (is (= 1 (count stale)))
          (is (= 1 (count @pushed)))
          (is (= 1 (count @swept))))))))

;; ---- the lifecycle is real, bounded, and a plain KB query ----------------

(tu/deftest-kb the-state-is-a-plain-kb-query-through-the-transitions
  (let [did (clash! kb)]
    (is (= :open (d/dispute-state kb did)) "fresh: open, derived")
    (adj/notify-disputes kb 'CxDeploy)
    (is (= :notified (d/dispute-state kb did)) "pushed: notified, stored")
    (is (some? (v/why kb (:id (first (v/sentexes-matching
                                      kb (list 'disputeNotified (d/dispute-term did) '?at)
                                      d/state-context)))))
        "the transition is why-explainable knowledge, not client bookkeeping")))

(tu/deftest-kb a-dispute-left-past-the-timeout-is-swept-stale-and-resurfaced
  (clash! kb)                                              ; opened at t0
  (let [did   (:dispute-id (first (d/disputes-in kb 'CxDeploy)))
        swept (atom [])]
    (binding [adj/*timeout-ms* 1000 adj/*stale-sink* #(swap! swept conj %)]
      (testing "not yet past the timeout: nothing swept"
        (binding [v/*clock* (constantly (+ t0 500))]
          (is (empty? (adj/sweep-stale kb 'CxDeploy)))
          (is (= :open (d/dispute-state kb did)))))
      (testing "past the timeout: swept to :stale and pushed to the operator sink"
        (binding [v/*clock* (constantly (+ t0 2000))]
          (let [s (adj/sweep-stale kb 'CxDeploy)]
            (is (= 1 (count s)))
            (is (= 1 (count @swept)) "re-surfaced to a human, not silently dropped")
            (is (= :stale (d/dispute-state kb did))))))
      (testing "stale still coexists — belief unchanged, the clash still stands"
        (is (= :contradiction (:verdict (v/argue kb P 'CxDeploy))))
        (is (seq (d/disputes-in kb 'CxDeploy))))
      (testing "and the sweep is idempotent — a second pass re-flags nothing"
        (binding [v/*clock* (constantly (+ t0 3000))]
          (is (empty? (adj/sweep-stale kb 'CxDeploy))))))))

;; ---- arbiter escalation: explained, and reversible -----------------------

(tu/deftest-kb an-arbiter-ruling-resolves-the-dispute-and-explains-itself
  (let [did (clash! kb)
        t-rule (+ t0 5000)
        rh  (binding [v/*clock* (constantly t-rule)]
              (adj/rule kb 'AgentArbiter did P 'CxDeploy))]
    (testing "the monotonic ruling defeats the losing side — the dispute resolves"
      (is (empty? (v/contradictions kb)))
      (is (= :resolved (d/dispute-state kb did)))
      (is (not (d/disputed? kb P 'CxDeploy)))
      (is (= :true (:verdict (v/argue kb P 'CxDeploy))))
      (is (not (v/ask? kb not-P 'CxDeploy)) "the losing side is defeated, not deleted"))
    (testing "why explains the adjudication, and who-ruled reads it off the ruling's provenance"
      (let [w (v/why kb rh)]
        (is (:believed? w))
        (is (= :monotonic (:defeat-class w))))
      ;; `:dispute-ids` is a set: one sentex is the standing ruling of every dispute
      ;; whose ruling dedups onto it, and a single-valued tag kept only the last
      (is (= {:arbiter 'AgentArbiter :dispute-ids #{(adj/dispute-key did)} :at t-rule}
             (adj/who-ruled kb rh))))))

(tu/deftest-kb an-arbiter-can-rule-for-the-negative-side
  (let [did (clash! kb)]
    (adj/rule kb 'AgentArbiter did not-P 'CxDeploy)
    (testing "ruling ¬P upholds the negative side symmetrically"
      (is (= :resolved (d/dispute-state kb did)))
      (is (= :false (:verdict (v/argue kb P 'CxDeploy))))
      (is (v/ask? kb not-P 'CxDeploy))
      (is (not (v/ask? kb P 'CxDeploy))))))

(tu/deftest-kb retracting-the-ruling-reopens-the-dispute-cascading
  (let [did (clash! kb)
        rh  (adj/rule kb 'AgentArbiter did P 'CxDeploy)]
    (is (= :resolved (d/dispute-state kb did)))
    (testing "retract the ruling: the loser is no longer defeated, the clash returns"
      (v/retract! kb rh)
      (is (d/disputed? kb P 'CxDeploy))
      (is (= :contradiction (:verdict (v/argue kb P 'CxDeploy))))
      (is (v/ask? kb P 'CxDeploy))
      (is (v/ask? kb not-P 'CxDeploy) "both sides believed again, no orphaned belief"))
    (testing "the marks were cleared at ruling time, so the reopen starts fresh at :open"
      (is (= :open (d/dispute-state kb did)))
      (is (nil? (adj/who-ruled kb rh)) "the ruling's provenance is gone with it"))))

(tu/deftest-kb a-reopened-dispute-re-notifies
  (let [did (clash! kb)
        pushed (atom [])]
    (binding [adj/*notify-sink* #(swap! pushed conj %)]
      (adj/notify-disputes kb 'CxDeploy)                 ; notified once
      (let [rh (adj/rule kb 'AgentArbiter did P 'CxDeploy)]  ; resolved (marks cleared)
        (v/retract! kb rh)                                ; reopened at :open
        (adj/notify-disputes kb 'CxDeploy))              ; a genuinely new episode -> re-push
      (testing "the subscriber is told twice: once per open episode"
        (is (= 2 (count @pushed)))))))

;; ---- an open dispute does not block reasoning — but it is made visible ----

(def deployable '(deployable ProdCluster))
(def shippable '(shippable ProdCluster))

(tu/deftest-kb reasoning-keeps-deriving-on-a-contested-premise-and-says-so
  (v/assert kb '(implies (reliable ?x) (deployable ?x)) 'CxDeploy)
  (v/assert kb '(implies (deployable ?x) (shippable ?x)) 'CxDeploy)   ; a second hop
  (clash! kb)                                              ; reliable ProdCluster is now contested
  (v/assert kb '(fast ProdCluster) 'CxDeploy)             ; an uncontested fact
  (testing "the paraconsistent default: the KB keeps deriving through the dispute"
    (is (v/ask? kb deployable 'CxDeploy) "deployable still fires from the contested reliable")
    (is (v/ask? kb shippable 'CxDeploy) "and the second hop fires too")
    (is (= :contradiction (:verdict (v/argue kb P 'CxDeploy))) "the dispute is unchanged"))
  (testing "a conclusion resting on a contested premise is visible as such — even two hops out"
    (is (adj/rests-on-contested? kb deployable 'CxDeploy))
    (is (adj/rests-on-contested? kb shippable 'CxDeploy) "the transitive support walk finds it")
    (is (seq (adj/contested-premises kb deployable 'CxDeploy)))
    (is (not (adj/rests-on-contested? kb '(fast ProdCluster) 'CxDeploy))
        "an uncontested fact rests on nothing disputed")))

;; ---- quarantine: the option, off by default ------------------------------

(tu/deftest-kb quarantine-excludes-a-contested-claim-from-one-channel-reversibly
  (v/assert kb '(implies (reliable ?x) (deployable ?x)) 'CxDeploy)
  (clash! kb)
  (let [ph (v/handle-of kb P 'CxAtlas)]
    (is (v/ask? kb deployable 'CxDeploy) "before: the derivation rests on the contested claim")
    (let [qh (adj/quarantine kb 'CxDeploy ph)]
      (testing "quarantine hides the claim from the channel only — the author keeps it"
        (is (= [ph] (adj/quarantined kb 'CxDeploy)))
        (is (not (v/ask? kb P 'CxDeploy)) "masked from the channel")
        (is (v/ask? kb P 'CxAtlas) "but Atlas still holds it — scoped to the channel")
        (is (not (v/ask? kb deployable 'CxDeploy)) "so the derivation no longer fires here"))
      (testing "the documented over-suppression: the channel can no longer see the dispute"
        (is (not= :contradiction (:verdict (v/argue kb P 'CxDeploy)))))
      (testing "reversible: unquarantine restores the claim and its derivations"
        (adj/unquarantine! kb qh)
        (is (empty? (adj/quarantined kb 'CxDeploy)))
        (is (v/ask? kb P 'CxDeploy))
        (is (v/ask? kb deployable 'CxDeploy))
        (is (= :contradiction (:verdict (v/argue kb P 'CxDeploy))) "the dispute is visible again")))))

;; ---- integration: a speech-act dispute drives the whole loop -------------

(tu/deftest-kb a-disputes-speech-act-opens-a-dispute-the-policy-then-drives
  (sa/load-speech-acts kb)
  (sa/speaker-context kb 'CxDeploy 'AgentAtlas)
  (sa/speaker-context kb 'CxDeploy 'AgentBoreas)
  (let [claim (sa/assert-claim kb 'AgentAtlas P)]
    (sa/dispute kb 'AgentBoreas claim)                   ; Boreas rebuts -> opens the dispute
    (let [pushed (atom [])
          did    (:dispute-id (first (d/disputes-in kb 'CxDeploy)))]
      (is (d/disputed? kb P 'CxDeploy) "the speech-act rebuttal is a real dispute")
      (binding [adj/*notify-sink* #(swap! pushed conj %)]
        (adj/notify-disputes kb 'CxDeploy))
      (is (= 1 (count @pushed)))
      (adj/rule kb 'AgentArbiter did P 'CxDeploy)
      (is (= :resolved (d/dispute-state kb did)) "and the arbiter can settle it"))))

;; ---- a second resolution policy: majority vote ---------------------------

(defn- ballot!
  "Cast a `stance` (`:for`/`:against`) ballot on the claim at `claim-h`, in `agent`'s own
  context — the shape `channel/vote` writes, asserted here without the channel dep."
  [kb agent claim-h stance]
  (v/assert kb (list (case stance :for 'votesFor :against 'votesAgainst)
                     agent (sx/sentex-handle claim-h))
            (id/context-for agent) {:creator agent}))

(tu/deftest-kb resolve-by-majority-leaves-a-tie-open-then-a-majority-carries
  (let [ph (holds! kb 'AgentAtlas P)]
    (holds! kb 'AgentBoreas not-P)
    (doseq [a '[AgentAtlas AgentBoreas AgentCiel]]
      (v/assert kb (list 'genlCx 'CxDeploy (id/context-for a)) 'CxUniverse {:strength :monotonic}))
    (let [id (:dispute-id (first (d/disputes-in kb 'CxDeploy)))]

      (testing "no ballots is a tie — nothing upheld, the dispute stays open"
        (let [r (adj/resolve-by-majority kb id ph 'CxDeploy)]
          (is (= {:for 0 :against 0} (select-keys r [:for :against])))
          (is (= :tie (:outcome r)))
          (is (nil? (:ruling r)))
          (is (d/disputed? kb P 'CxDeploy))))

      (ballot! kb 'AgentAtlas ph :for)
      (ballot! kb 'AgentBoreas ph :against)
      (testing "1-1 is still a tie — a split house decides nobody"
        (is (= {:for 1 :against 1} (adj/tally kb ph)) "distinct voters, counted anywhere")
        (let [r (adj/resolve-by-majority kb id ph 'CxDeploy)]
          (is (= :tie (:outcome r)))
          (is (nil? (:ruling r)))
          (is (d/disputed? kb P 'CxDeploy))))

      (testing "2-1 for carries it — resolved, recorded as the majority's call, reversible"
        (ballot! kb 'AgentCiel ph :for)
        (let [r (adj/resolve-by-majority kb id ph 'CxDeploy)]
          (is (= {:for 2 :against 1} (select-keys r [:for :against])))
          (is (= :for (:outcome r)))
          (is (not (d/disputed? kb P 'CxDeploy)))
          (is (= :true (:verdict (v/argue kb P 'CxDeploy))))
          (is (= adj/majority-arbiter (:arbiter (adj/who-ruled kb (:ruling r)))))
          (v/retract! kb (:ruling r))
          (is (d/disputed? kb P 'CxDeploy) "retract the ruling and the dispute reopens"))))))

(tu/deftest-kb resolve-by-majority-can-vote-the-claim-down
  (let [ph (holds! kb 'AgentAtlas P)]
    (holds! kb 'AgentBoreas not-P)
    (doseq [a '[AgentAtlas AgentBoreas AgentCiel]]
      (v/assert kb (list 'genlCx 'CxDeploy (id/context-for a)) 'CxUniverse {:strength :monotonic}))
    (let [id (:dispute-id (first (d/disputes-in kb 'CxDeploy)))]
      (ballot! kb 'AgentBoreas ph :against)
      (ballot! kb 'AgentCiel ph :against)
      (ballot! kb 'AgentAtlas ph :for)
      (testing "an against-majority upholds the NEGATION — the claim is voted down"
        (let [r (adj/resolve-by-majority kb id ph 'CxDeploy)]
          (is (= {:for 1 :against 2} (select-keys r [:for :against])))
          (is (= :against (:outcome r)))
          (is (not (d/disputed? kb P 'CxDeploy)))
          (is (= :false (:verdict (v/argue kb P 'CxDeploy))) "the proposal is rejected"))))))

(tu/deftest-kb a-repeat-ballot-is-one-vote
  (let [ph (holds! kb 'AgentAtlas P)]
    (holds! kb 'AgentBoreas not-P)
    (ballot! kb 'AgentBoreas ph :against)
    (ballot! kb 'AgentBoreas ph :against)
    (is (= {:for 0 :against 1} (adj/tally kb ph))
        "idempotent by sentence identity — one agent, one ballot")))

(tu/deftest-kb a-voter-who-votes-both-ways-spoils-their-ballot
  (let [ph (holds! kb 'AgentAtlas P)]
    (holds! kb 'AgentBoreas not-P)
    (ballot! kb 'AgentAtlas ph :for)
    (ballot! kb 'AgentBoreas ph :against)
    (ballot! kb 'AgentBoreas ph :for)                       ; Boreas contradicts himself
    (is (= {:for 1 :against 0} (adj/tally kb ph))
        "Boreas is counted on neither side — a self-contradicting ballot abstains, so one
         confused voter cannot manufacture a tie or swing the majority")))

(tu/deftest-kb a-voter-can-change-their-vote
  (let [ph (holds! kb 'AgentAtlas P)]
    (holds! kb 'AgentBoreas not-P)
    (let [bh (ballot! kb 'AgentBoreas ph :for)]             ; Boreas first votes for
      (is (= {:for 1 :against 0} (adj/tally kb ph)))
      (v/retract! kb bh)                                    ; the documented change flow: retract, re-cast
      (ballot! kb 'AgentBoreas ph :against)
      (is (= {:for 0 :against 1} (adj/tally kb ph)) "the changed vote is the one that counts"))))

(tu/deftest-kb resolving-by-majority-twice-is-a-belief-no-op
  (let [ph (holds! kb 'AgentAtlas P)]
    (holds! kb 'AgentBoreas not-P)
    (doseq [a '[AgentAtlas AgentBoreas AgentCiel]]
      (v/assert kb (list 'genlCx 'CxDeploy (id/context-for a)) 'CxUniverse {:strength :monotonic}))
    (let [id (:dispute-id (first (d/disputes-in kb 'CxDeploy)))]
      (ballot! kb 'AgentAtlas ph :for)
      (ballot! kb 'AgentCiel ph :for)
      (ballot! kb 'AgentBoreas ph :against)
      (let [r1 (adj/resolve-by-majority kb id ph 'CxDeploy)
            r2 (adj/resolve-by-majority kb id ph 'CxDeploy)]
        (is (= :for (:outcome r1) (:outcome r2)))
        (is (= (:ruling r1) (:ruling r2))
            "the same ruling handle — a second resolve re-rules as a belief no-op, so a driver may poll it")
        (is (not (d/disputed? kb P 'CxDeploy)) "still resolved, no thrash")))))

(tu/deftest-kb the-majority-can-change-its-mind
  ;; Ballots are retracted and re-cast, so the house can swing.  The count is the
  ;; authority each time: a ruling that no longer matches it is withdrawn before the new
  ;; one lands, else two monotonic rulings on one clash would be a `:conflict` reported
  ;; as `:contradiction` under a return value claiming the swing carried.
  (let [ph (holds! kb 'AgentAtlas P)]
    (holds! kb 'AgentBoreas not-P)
    (doseq [a '[AgentAtlas AgentBoreas AgentCiel]]
      (v/assert kb (list 'genlCx 'CxDeploy (id/context-for a)) 'CxUniverse {:strength :monotonic}))
    (let [id (:dispute-id (first (d/disputes-in kb 'CxDeploy)))
          ba (ballot! kb 'AgentAtlas ph :for)
          bc (ballot! kb 'AgentCiel ph :for)
          bb (ballot! kb 'AgentBoreas ph :against)
          r1 (adj/resolve-by-majority kb id ph 'CxDeploy)]
      (is (= :for (:outcome r1)))
      (is (= [] (:withdrawn r1)))
      (is (= :true (:verdict (v/argue kb P 'CxDeploy))))
      (testing "the house swings: for-voters retract and vote against"
        (v/retract! kb ba)
        (v/retract! kb bc)
        (ballot! kb 'AgentAtlas ph :against)
        (ballot! kb 'AgentCiel ph :against)
        (let [r2 (adj/resolve-by-majority kb id ph 'CxDeploy)]
          (is (= {:for 0 :against 3 :outcome :against} (select-keys r2 [:for :against :outcome])))
          (is (= [(:ruling r1)] (:withdrawn r2)) "the standing ruling is withdrawn first")
          (is (not (v/in? kb (:ruling r1))))
          (is (= :false (:verdict (v/argue kb P 'CxDeploy)))
              "one ruling stands, so the verdict follows the new count")
          (is (empty? (filter #(= :conflict (:dispute-class %)) (d/disputes-in kb 'CxDeploy)))
              "no monotonic conflict between two rulings")
          (testing "and a majority that dissolves into a tie withdraws its ruling"
            (v/retract! kb (v/handle-of kb (list 'votesAgainst 'AgentCiel (sx/sentex-handle ph))
                                        (id/context-for 'AgentCiel)))
            (ballot! kb 'AgentCiel ph :for)
            (let [r3 (adj/resolve-by-majority kb id ph 'CxDeploy)]
              (is (= {:for 1 :against 2 :outcome :against} (select-keys r3 [:for :against :outcome])))
              (is (= [] (:withdrawn r3)) "the count held, nothing withdrawn")
              (is (= (:ruling r2) (:ruling r3))))
            (v/retract! kb bb)                              ; Boreas abstains: 1-1
            (let [r4 (adj/resolve-by-majority kb id ph 'CxDeploy)]
              (is (= {:for 1 :against 1 :outcome :tie} (select-keys r4 [:for :against :outcome])))
              (is (= [(:ruling r2)] (:withdrawn r4)))
              (is (d/disputed? kb P 'CxDeploy) "nobody rules a split house")
              (is (= :contradiction (:verdict (v/argue kb P 'CxDeploy)))))))))))

(tu/deftest-kb an-arbiter-who-rules-again-supersedes-their-own-ruling
  ;; The same contract one level down: one ruling per arbiter per dispute.
  (let [did (clash! kb)
        h1  (adj/rule kb 'AgentArbiter did P 'CxDeploy)]
    (is (= :true (:verdict (v/argue kb P 'CxDeploy))))
    (let [h2 (adj/rule kb 'AgentArbiter did not-P 'CxDeploy)]
      (is (not (v/in? kb h1)) "the earlier ruling is retracted")
      (is (= [h2] (adj/standing-rulings kb 'AgentArbiter did)))
      (is (= :false (:verdict (v/argue kb P 'CxDeploy))))
      (is (= h2 (adj/rule kb 'AgentArbiter did not-P 'CxDeploy))
          "ruling the same side again is the standing handle"))))

(tu/deftest-kb who-ruled-is-nil-for-an-ordinary-non-ruling-handle
  (let [ph (holds! kb 'AgentAtlas P)]
    (is (nil? (adj/who-ruled kb ph)) "a plain, still-stored claim carries no adjudication provenance")))

(tu/deftest-kb one-arbiter-ruling-two-disputes-the-same-way-holds-both
  ;; Canonical dedup gives one sentex per (sentence, context), so an arbiter upholding
  ;; the same claim against two different opponents stamps **one** handle twice.  A
  ;; single-valued `:adjudication` tag kept only the later id, so the earlier dispute
  ;; read no standing ruling, skipped the one-per-arbiter guard, and took a second
  ;; monotonic ruling beside the first — two known-true claims on one clash.
  (let [_    (clash! kb)                                 ; Atlas P vs Boreas ¬P
        _    (holds! kb 'AgentCiel not-P)
        _    (v/assert kb (list 'genlCx 'CxDeploy (id/context-for 'AgentCiel))
                       'CxUniverse {:strength :monotonic})
        ds   (mapv :dispute-id (d/disputes-in kb 'CxDeploy))
        [d1 d2] ds]
    (is (= 2 (count ds)) "P is disputed by two opponents")
    (let [h1 (adj/rule kb 'AgentArbiter d1 P 'CxDeploy)
          h2 (adj/rule kb 'AgentArbiter d2 P 'CxDeploy)]
      (is (= h1 h2) "one sentex is the ruling of both — canonical dedup")
      (testing "and it is the standing ruling of each, not only the last"
        (is (= [h1] (adj/standing-rulings kb 'AgentArbiter d1)))
        (is (= [h1] (adj/standing-rulings kb 'AgentArbiter d2)))
        (is (= #{(adj/dispute-key d1) (adj/dispute-key d2)}
               (:dispute-ids (adj/who-ruled kb h1)))))
      (testing "so ruling the first the other way supersedes rather than doubling"
        (let [h3 (adj/rule kb 'AgentArbiter d1 not-P 'CxDeploy)]
          (is (not (v/in? kb h1)) "the shared ruling is withdrawn, not left beside")
          (is (= [h3] (adj/standing-rulings kb 'AgentArbiter d1)))
          (is (= :false (:verdict (v/argue kb P 'CxDeploy)))))))))

(tu/deftest-kb a-dispute-id-is-read-in-either-spelling
  ;; `dispute-id` sorts, but a caller may hold the pair either way round — and a tag
  ;; written under one spelling was invisible to a read for the other, which is a
  ;; standing ruling the guard cannot see.
  (let [did (clash! kb)
        h   (adj/rule kb 'AgentArbiter did P 'CxDeploy)]
    (is (= [h] (adj/standing-rulings kb 'AgentArbiter (vec (reverse did))))
        "the reversed pair names the same dispute")
    (is (= h (adj/rule kb 'AgentArbiter (vec (reverse did)) P 'CxDeploy))
        "and ruling under it is the same standing ruling, not a second")))

(tu/deftest-kb an-arbiter-who-is-a-party-is-refused
  ;; A ruling lands in the arbiter's own context, so for a party that context already
  ;; holds a side: ruling their own way would restamp their claim as its own
  ;; adjudication, and ruling the other way would retract it — the disputed claim
  ;; deleted rather than the dispute settled.
  (let [did (clash! kb)]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"is a party to dispute"
                          (adj/rule kb 'AgentAtlas did P 'CxDeploy)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"is a party to dispute"
                          (adj/rule kb 'AgentAtlas did not-P 'CxDeploy)))
    (testing "and the party's own claim is untouched"
      (is (v/ask? kb P (id/context-for 'AgentAtlas))))
    (testing "an uninvolved arbiter still rules it"
      (is (some? (adj/rule kb 'AgentArbiter did P 'CxDeploy))))))

;; ---- and every order of the same rulings, not the one written out above ----

(defn- ruling-kb
  "A KB of this namespace's shape on the **isolated** space: the permutation tests below
  rebuild one per ordering, which would clear the shared space out from under another
  namespace's `:once` fixture."
  []
  (doto (tu/isolated-fresh) (core-context/load-into)))

(defn- two-disputes!
  "Atlas holds P; Boreas and Ciel each hold ¬P, and `CxDeploy` sees all three.  So one
  claim is disputed twice, which is what makes the ruling of both one sentex.  Returns
  `[claim-handle [dispute-id dispute-id]]`."
  [kb]
  (let [ph (holds! kb 'AgentAtlas P)]
    (holds! kb 'AgentBoreas not-P)
    (holds! kb 'AgentCiel not-P)
    (doseq [a '[AgentAtlas AgentBoreas AgentCiel AgentDora]]
      (v/assert kb (list 'genlCx 'CxDeploy (id/context-for a)) 'CxUniverse {:strength :monotonic}))
    [ph (mapv :dispute-id (d/disputes-in kb 'CxDeploy))]))

(defn- settled-reading
  "What a settled channel looks like from outside: the verdict, both sides' belief, the
  two clash reports, whether any dispute has gone to `:conflict`, and how many standing
  rulings the arbiter is left holding.  The counts are **sorted**, because `disputes-in`
  promises the set: which dispute is at which index is not a claim this makes, and under
  an ordering that reverses the second rather than the first the two swap."
  [kb arbiter ds]
  {:verdict        (:verdict (v/argue kb P 'CxDeploy))
   :ask-p          (v/ask? kb P 'CxDeploy)
   :ask-not-p      (v/ask? kb not-P 'CxDeploy)
   :disputed       (d/disputed? kb P 'CxDeploy)
   :conflicts      (count (v/conflicts kb))
   :contradictions (count (v/contradictions kb))
   :conflict-class (count (filter #(= :conflict (:dispute-class %)) (d/disputes-in kb 'CxDeploy)))
   :standing       (vec (sort (map #(count (adj/standing-rulings kb arbiter %)) ds)))})

(deftest every-order-of-the-same-rulings-reaches-one-belief
  ;; One claim disputed by two opponents is **two** disputes, and one arbiter upholding it
  ;; against both stamps **one** sentex — canonical dedup gives one per sentence and
  ;; context.  Which dispute the arbiter is asked about first is a free choice of the
  ;; caller's, and the belief must not turn on it.  It did: the ruling remembered a single
  ;; dispute, so the other read no standing ruling, skipped the one-per-arbiter guard, and
  ;; took a second monotonic ruling beside the first — `CxDeploy` holding P and ¬P at once
  ;; with `argue` reporting `:contradiction`, where the mirror-image order reached a clean
  ;; `:false` under a return value that said the same thing both times.
  (testing "an arbiter upholds the claim in both disputes, then reverses one"
    ;; Two free choices, four runs, and they are the whole of the freedom: which dispute is
    ;; ruled first, and which one is later reversed.  The reversal is a fixed pivot rather
    ;; than a permuted op — a reversal before there is a ruling to reverse is a different
    ;; scenario, not a different order of this one.
    (let [readings (into {}
                         (for [order [[0 1] [1 0]]
                               flip  [0 1]]
                           [[order flip]
                            (tu/with-cleared-kb [kb ruling-kb]
                              (let [[_ ds] (two-disputes! kb)]
                                (is (= 2 (count ds)) "P is disputed by two opponents")
                                (doseq [i order] (adj/rule kb 'AgentArbiter (nth ds i) P 'CxDeploy))
                                (adj/rule kb 'AgentArbiter (nth ds flip) not-P 'CxDeploy)
                                (settled-reading kb 'AgentArbiter ds)))]))]
      (is (= 1 (count (set (vals readings))))
          (str "the same rulings in a different order left a different belief — "
               (pr-str (into (sorted-map) readings))))
      (let [r (val (first readings))]
        (testing "and the one reading is the reversal carried, with nothing left beside it"
          (is (= :false (:verdict r)))
          (is (false? (:ask-p r)))
          (is (true? (:ask-not-p r)))
          (is (false? (:disputed r)))
          (is (zero? (:conflicts r)) "one ruling stands, so no clash a ruling cannot settle")
          (is (zero? (:conflict-class r))))))))

(deftest every-order-of-the-same-polls-reaches-one-belief
  ;; The same claim through the majority policy, which reaches `rule` by its own route and
  ;; under a fixed arbiter (`majority-arbiter`).  The count is shared — a ballot is cast on
  ;; the claim, not on a dispute — so the two polls agree on the outcome and differ only in
  ;; which dispute records it, which is exactly the free choice the test above permutes.
  ;; Its own `deftest` rather than a second arm, so that neither exhaustive cross-product
  ;; carries the other's cost into the default gate.
  (testing "the house is polled once per dispute, then swings"
    (let [readings (into {}
                         (for [before [[0 1] [1 0]]
                               after  [[0 1] [1 0]]]
                           [[before after]
                            (tu/with-cleared-kb [kb ruling-kb]
                              (let [[ph ds] (two-disputes! kb)
                                    poll!   (fn [order]
                                              (doseq [i order]
                                                (adj/resolve-by-majority kb (nth ds i) ph 'CxDeploy)))
                                    ba (ballot! kb 'AgentAtlas ph :for)
                                    bd (ballot! kb 'AgentDora ph :for)]
                                (ballot! kb 'AgentBoreas ph :against)
                                (poll! before)                  ; 2-1 for: the claim is upheld
                                (v/retract! kb ba)              ; the house swings
                                (v/retract! kb bd)
                                (ballot! kb 'AgentAtlas ph :against)
                                (ballot! kb 'AgentDora ph :against)
                                (poll! after)                   ; 0-3 against: the claim goes down
                                (settled-reading kb adj/majority-arbiter ds)))]))]
      (is (= 1 (count (set (vals readings))))
          (str "the same polls in a different order left a different belief — "
               (pr-str (into (sorted-map) readings))))
      (let [r (val (first readings))]
        (testing "and the one reading is the swing carried, recorded against both disputes"
          (is (= :false (:verdict r)))
          (is (false? (:disputed r)))
          (is (zero? (:conflicts r)))
          (is (= [1 1] (:standing r))
              "one ruling settles both disputes, and is found again for each"))))))

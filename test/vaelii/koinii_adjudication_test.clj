;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.koinii-adjudication-test
  "Koinii adjudication: the default leave-open-and-notify policy, the
  open->notified->resolved(+stale) lifecycle with a timeout sweep, and reversible arbiter
  escalation.  A client wrapper over the dispute reads — it changes belief only through ordinary
  asserts/retracts and never touches settle."
  (:require [clojure.test :refer [is testing use-fixtures]]
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
      (is (= {:arbiter 'AgentArbiter :dispute-id did :at t-rule}
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

(tu/deftest-kb who-ruled-is-nil-for-an-ordinary-non-ruling-handle
  (let [ph (holds! kb 'AgentAtlas P)]
    (is (nil? (adj/who-ruled kb ph)) "a plain, still-stored claim carries no adjudication provenance")))

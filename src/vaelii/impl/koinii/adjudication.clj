;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.koinii.adjudication
  "Koinii adjudication — the DEFAULT policy: leave-open-and-notify, plus the
  lifecycle that keeps disputes from piling up, plus arbiter escalation.  A thin CLIENT
  wrapper over the dispute reads (`vaelii.impl.koinii.dispute`) — it touches no
  engine internals and changes belief only through ordinary asserts / retracts.

  koinii's honest first answer to a disagreement is NOT to pick a winner.  When two agents
  assert P and ¬P at `:default`, the KB stays **paraconsistent** — both coexist, `argue`
  reports `:contradiction` (Priest's LP) — and this layer just records the dispute open,
  pushes it to whoever is watching, and manages its life.  Automatic resolution by source
  trust is a harder, engine-side policy; do not reach for it here.

  Three policies, one default (koinii.md, *Adjudication: split by policy*):

  - **Leave-open-and-notify** *(the default, here)* — record open, notify, change no
    belief.  Correct for a ground truth people curate.
  - **Arbiter escalation** *(also here, client)* — a designated arbiter's ruling is an
    ordinary `:monotonic` assertion of the upheld side; its strength defeats the losing
    `:default` side, so the clash clears, `why` explains who ruled, and retracting the
    ruling reopens the dispute (cascading).
  - **Trust-resolve** — out of scope; that is engine work, not this layer's.

  The dispute module owns the reads, the state vocabulary, and the dispute id; THIS module owns the policy
  the dispute module deliberately left out — the **clock**, the **timeout**, and the **notify sinks**.  The
  clock is the engine clock (`v/*clock*`), so a lifecycle stamp and its assertion's
  `:created` provenance agree.

  Additive, like the sibling koinii modules: only the public core API plus koinii
  `dispute` and `identity` — nothing in core loads it."
  (:require [vaelii.core :as v]
            [vaelii.impl.koinii.dispute :as d]
            [vaelii.impl.koinii.identity :as id]))

;; ---- the policy seams the dispute module left to the caller --------------

(def ^:dynamic *timeout-ms*
  "How long a dispute may stay live with no ruling before `sweep-stale` flags it (and
  re-surfaces it to a human).  A judgement call — a curated ground truth wants it long
  enough that a real disagreement is not swept before anyone looks.  Default 24h."
  (* 24 60 60 1000))

(def ^:dynamic *notify-sink*
  "Where a newly-opened dispute is pushed: `(fn [dispute-entry] …)`, called once per
  dispute as it transitions `open -> notified`.  This is the seam the channel's feed
  subscribers and a configured human sink wire into; nil ships no push (the
  lifecycle mark is still recorded, so nothing is lost — a later `notify-disputes` with a
  sink still finds it un-pushed only if the mark was cleared).  Idempotency does not live
  here — it lives in the stored mark — so a sink need not dedupe."
  nil)

(def ^:dynamic *stale-sink*
  "The operator sink for `sweep-stale`: `(fn [dispute-entry] …)`, called once per dispute
  swept to `:stale`.  An aged-out dispute is re-surfaced to a human, never silently
  dropped.  nil ships no push."
  nil)

(defn- now
  "The current stamp from the engine clock (`v/*clock*`), so a lifecycle timestamp and the
  `:created` provenance of the assertion recording it agree.  Bind `v/*clock*` in a test to
  pin it."
  []
  (v/*clock*))

;; ---- notify: open -> notified, pushed once -------------------------------

(defn notify-disputes
  "The default policy's core move: announce every not-yet-announced dispute `channel`
  observes and record it `notified`.  For each `:open` dispute (from the dispute module's
  `pending-disputes`), stamp a `notified` mark (`open -> notified`) and push the entry to
  `*notify-sink*`.  Changes NO belief — both sides stay `in?` at `:default` and `argue`
  still reports `:contradiction`; only the lifecycle record moves.

  **Fires once per dispute.**  The stored mark is the idempotency key: a notified dispute
  is no longer `:open`, so a redelivery or a catch-up re-run does not re-push
  it.  Returns the disputes newly notified."
  [kb channel]
  (let [pending (d/pending-disputes kb channel)]
    (doseq [entry pending]
      (d/mark-notified kb (:dispute-id entry) (now))
      (when *notify-sink* (*notify-sink* entry)))
    pending))

;; ---- the stale sweep: bound the accumulation -----------------------------

(defn- opened-at
  "When dispute `id` arose: the later `:created` stamp of its two clashing sides (the clash
  exists once the second side is asserted).  0 if neither side carries a stamp — an
  un-stamped dispute is treated as old, so the sweep surfaces it rather than hiding it."
  [kb id]
  (reduce max 0 (keep #(:created (v/provenance kb %)) id)))

(defn sweep-stale
  "Sweep every dispute `channel` observes that has stayed live past `*timeout-ms*` with no
  ruling to `:stale`, pushing each to `*stale-sink*`.  A stale dispute is STILL live — both
  sides coexist, `argue` still reports `:contradiction` — `:stale` only flags that it aged
  out unaddressed, so open disputes do not accumulate unbounded and none is silently
  dropped.  Idempotent: an already-`:stale` dispute is skipped.  Returns the disputes swept."
  [kb channel]
  (let [cutoff (- (now) *timeout-ms*)
        swept  (filterv (fn [e]
                          (and (not= :stale (d/dispute-state kb (:dispute-id e)))
                               (< (opened-at kb (:dispute-id e)) cutoff)))
                        (d/disputes-in kb channel))]
    (doseq [e swept]
      (d/mark-stale kb (:dispute-id e) (now) 'TimedOut)
      (when *stale-sink* (*stale-sink* e)))
    swept))

(defn poll
  "One driver tick over `channel`: notify the fresh disputes, then sweep the aged ones.
  Returns `{:notified [...] :stale [...]}`.  A subscribe loop or a timer calls
  this; the two halves are also usable apart."
  [kb channel]
  {:notified (notify-disputes kb channel)
   :stale    (sweep-stale kb channel)})

;; ---- arbiter escalation: a reversible ruling that clears the clash -------

(defn rule
  "Arbiter escalation: `arbiter` (an agent id, e.g. `AgentArbiter`) rules dispute `id`
  within `channel` in favour of `upheld` — which MUST be one of the dispute's two clashing
  sentences.

  The ruling is an ordinary assertion: `upheld` at `:monotonic` strength in the arbiter's
  OWN context (`id/context-for`), lifted under `channel` so the channel sees it, stamped
  creator `arbiter` and tagged `:adjudication id` in provenance.  Monotonic strength
  defeats the losing `:default` side, so the coexisting clash clears — the dispute reads
  `:resolved` and `argue` collapses to `:true`/`:false`.  `why` on `upheld` shows the
  adjudication and who ruled.

  **Reversible.**  Retract the returned handle and the losing side is no longer defeated —
  the dispute reopens, cascading through the JTMS.  A ruling koinii could not undo would be
  a worse store than one that stays honestly disputed.  The dispute's open/notified/stale
  marks are cleared as the episode ends, so a reopen starts fresh at `:open` (and
  re-notifies).  Returns the ruling handle.

  Resolves a `:default` coexisting dilemma only.  A `:monotonic` `:conflict` (two things
  asserted known-true) cannot be settled by a monotonic ruling — it needs a human to
  retract a premise — so it is not this path's job."
  [kb arbiter id upheld channel]
  (let [actx (id/context-for arbiter)]
    (v/assert kb (list 'genlCx channel actx) 'CxUniverse {:strength :monotonic})
    (d/reopen! kb id)                                    ; end the lifecycle episode
    (v/assert kb upheld actx {:strength :monotonic :creator arbiter
                              :provenance {:adjudication id}})))

(defn who-ruled
  "Read a ruling off its handle: `{:arbiter :dispute-id :at}` from the provenance `rule`
  stamped, or nil if `ruling-handle` is not an adjudication assertion.  'Who ruled this
  dispute, and when' as a plain provenance read."
  [kb ruling-handle]
  (let [p (v/provenance kb ruling-handle)]
    (when-let [did (:adjudication p)]
      {:arbiter (:creator p) :dispute-id did :at (:created p)})))

;; ---- a second resolution policy: majority vote ---------------------------
;;
;; Arbiter escalation upholds whatever ONE authority decrees; this upholds whatever a
;; MAJORITY of cast ballots does — and, the honest part, upholds NOTHING on a tie, so an
;; evenly-split house stays open rather than being decided by fiat.  A ballot is a
;; meta-sentex on the disputed claim (`channel/vote` casts it — `(votesFor voter
;; (sentexHandle claim))` / `(votesAgainst …)`, knowledge like every other move), so `why`
;; explains a decision as "the majority voted, here are the ballots."  The decision itself
;; REUSES `rule` — a reversible monotonic assertion — so retracting it reopens the dispute
;; exactly as an arbiter ruling does; the only differences are who is recorded as deciding
;; (`majority-arbiter`) and that a tie decides nobody.

(def majority-arbiter
  "The principal recorded as ruler of a majority-vote resolution — not a real agent but
  the stand-in 'the house majority', so `who-ruled` tells a counted vote apart from a named
  arbiter's decree."
  'AgentMajority)

(defn tally
  "Count the ballots cast on the claim at `claim-handle`: `{:for n :against n}`, each a
  count of DISTINCT voters.  Matched anywhere (`?ctx`) because a ballot names the
  globally-unique claim handle — the same reason the dispute and channel recovery reads do; a channel
  read would miss ballots sitting in the voters' own contexts (`sentexes-matching` scopes
  to a context's own sentexes, not the genlCx cone).

  A voter who cast BOTH stances (without retracting the first, against `vote`'s contract)
  has SPOILED their ballot — counted on neither side — so one self-contradicting voter can
  neither manufacture a tie nor swing a majority; their confusion abstains rather than
  double-voting."
  [kb claim-handle]
  (letfn [(who [pred]
            (into #{} (map (comp second :sentence))
                  (v/sentexes-matching kb (list pred '?a (v/sentex-handle claim-handle)) '?ctx)))]
    (let [yes (who 'votesFor) no (who 'votesAgainst)]
      {:for (count (remove no yes)) :against (count (remove yes no))})))

(defn resolve-by-majority
  "Resolve dispute `id` over the claim at `claim-handle` by MAJORITY VOTE, within
  `channel`.  Count the ballots (`tally`); if one side has strictly more, uphold it as a
  reversible ruling (`rule`, arbiter `majority-arbiter`) — the claim for a `:for` majority,
  its negation for an `:against` majority — so the clash clears and retracting the ruling
  reopens it.  **A tie upholds nothing**: an evenly-split house (or one nobody has voted in)
  stays honestly disputed, the leave-open default holding rather than a winner picked by
  fiat — which is the whole reason to count instead of decree.

  Returns `{:for n :against n :outcome :for/:against/:tie :ruling handle-or-nil}`.  Idempotent
  in spirit: re-running after a resolution re-counts and re-rules (a fresh monotonic assert
  of the same side, a no-op on belief), so a driver may poll it."
  [kb id claim-handle channel]
  (let [{yes :for no :against :as counts} (tally kb claim-handle)
        claim (:sentence (v/sentex kb claim-handle))]
    (cond
      (> yes no) (assoc counts :outcome :for
                        :ruling (rule kb majority-arbiter id claim channel))
      (> no yes) (assoc counts :outcome :against
                        :ruling (rule kb majority-arbiter id (list 'not claim) channel))
      :else      (assoc counts :outcome :tie :ruling nil))))

;; ---- does an open dispute block dependent reasoning? no — but make it visible

(defn- support-handles
  "The transitive premise handles a stored conclusion `handle` rests on — a
  visited-guarded walk of `why`'s `:because` graph, excluding the conclusion itself.  Cheap
  for a shallow derivation and cycle-safe; a premise has no `:because`, so the walk stops
  there."
  [kb handle]
  (loop [stack [handle] seen #{}]
    (if-let [h (peek stack)]
      (if (seen h)
        (recur (pop stack) seen)
        (let [prem (for [j (:support (v/why kb h)) b (:because j)] (:handle b))]
          (recur (into (pop stack) prem) (conj seen h))))
      (disj seen handle))))

(defn contested-premises
  "The disputed premises the conclusion `S` rests on in `ctx`: the handles in S's support
  closure that are a side of an open dispute `ctx` observes.  Empty if S rests on nothing
  contested.

  This is the paraconsistent default made HONEST.  An open dispute does NOT block dependent
  reasoning — the KB keeps deriving and both sides stay believed at `:default` — but a
  conclusion resting on a contested premise should be *visible as such* so a reader is never
  silently misled.  A pure read: it changes no belief, unlike `quarantine`.  Returns the
  contested premise handles."
  [kb S ctx]
  (if-let [h (v/handle-of kb S ctx)]
    (let [contested (into #{} (mapcat :dispute-id) (d/disputes-in kb ctx))]
      (filterv contested (support-handles kb h)))
    []))

(defn rests-on-contested?
  "Does the conclusion `S` in `ctx` rest on any premise that is currently disputed there?
  The boolean over `contested-premises` — the flag a high-stakes reader checks before
  trusting a derived answer."
  [kb S ctx]
  (boolean (seq (contested-premises kb S ctx))))

;; ---- quarantine: the OPTION, off by default ------------------------------

(defn quarantine
  "OPTIONAL, off by default: hide the contested sentex `target-handle` from `channel`'s
  reads and derivations, reversibly, via an index-layer `except` asserted in `channel`.  For
  a high-stakes channel that must never let a conclusion rest silently on a contested
  premise.  Scoped to `channel`: the claim stays believed in its OWN context (its author
  still holds it); only `channel`, and what `channel` feeds, stops seeing it.

  **The trade-off, and why it is off by default.**  Quarantine never lets a conclusion rest
  silently on a contested premise — but it OVER-SUPPRESSES: with the claim masked, `channel`
  can no longer see the dispute at all (`argue` there reads the lone surviving side, not
  `:contradiction`), and `except` is an index-layer mask that interacts with the TMS and
  contexts.  Prefer `contested-premises` / `rests-on-contested?` (pure reads that surface
  the risk without hiding anything) unless a channel genuinely must exclude contested claims
  from derivation.  Returns the mask's handle; `unquarantine!` retracts it and restores the
  claim (cascading its derivations back)."
  [kb channel target-handle]
  (v/assert kb (list 'except (v/sentex-handle target-handle)) channel {:strength :monotonic}))

(defn unquarantine!
  "Undo a `quarantine`: retract the `except` mask at `handle`, so the claim and anything it
  fed count again in the channel.  Returns `retract!`'s counts."
  [kb handle]
  (v/retract! kb handle))

(defn quarantined
  "The sentex handles `channel` is currently quarantining — the targets of its
  `(except (sentexHandle ?h))` masks.  'What has this channel screened out' as a plain read."
  [kb channel]
  (->> (v/sentexes-matching kb (list 'except '?h) channel)
       (keep (fn [s] (let [t (second (:sentence s))]
                       (when (v/sentex-handle? t) (second t)))))
       vec))

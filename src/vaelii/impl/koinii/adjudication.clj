;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.koinii.adjudication
  "Koinii adjudication — the DEFAULT policy: leave-open-and-notify, plus the
  lifecycle that keeps disputes from piling up, plus the two escalations (a named
  arbiter's ruling, and a counted majority).  A thin CLIENT
  wrapper over the dispute reads (`vaelii.impl.koinii.dispute`) — it touches no
  engine internals and changes belief only through ordinary asserts / retracts.

  koinii's honest first answer to a disagreement is NOT to pick a winner.  When two agents
  assert P and ¬P at `:default`, the KB stays **paraconsistent** — both coexist, `argue`
  reports `:contradiction` (Priest's LP) — and this layer just records the dispute open,
  pushes it to whoever is watching, and manages its life.  Automatic resolution by source
  trust is a harder, engine-side policy; do not reach for it here.

  Three policies, one default (koinii.md, *Adjudication: split by policy*), and all three
  are here:

  - **Leave-open-and-notify** *(the default)* — record open, notify, change no
    belief.  Correct for a ground truth people curate.
  - **Arbiter escalation** — a designated arbiter's ruling is an
    ordinary `:monotonic` assertion of the upheld side; its strength defeats the losing
    `:default` side, so the clash clears, `why` explains who ruled, and retracting the
    ruling reopens the dispute (cascading).
  - **Majority vote** — the ballots cast on the disputed claim are counted and the side
    with strictly more is upheld, through that same reversible ruling; a tie upholds
    nothing, so an evenly-split house stays open.

  **Trust-resolve** — automatic resolution by source trust — is out of scope for this
  layer: it is engine-side reputation work, and reaching for it here would resolve
  disagreements by weighing spoofable identities.

  The dispute module owns the reads, the state vocabulary, and the dispute id; THIS module owns the policy
  the dispute module deliberately left out — the **clock**, the **timeout**, and the **notify sinks**.  The
  clock is the engine clock (`v/*clock*`), so a lifecycle stamp and its assertion's
  `:created` provenance agree.

  Additive, like the sibling koinii modules: only the public core API plus koinii
  `dispute` and `identity`, and `naming` for the two content orders it reports
  (`contested-premises`, `standing-rulings`) — nothing in core loads it."
  (:require [vaelii.core :as v]
            [vaelii.impl.koinii.dispute :as d]
            [vaelii.impl.koinii.identity :as id]
            [vaelii.impl.naming :as nm]))

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
  dropped.  Idempotent: an already-`:stale` dispute is skipped.  Returns the disputes swept.

  **One whole-KB scan for the sweep, not one per dispute.**  The skip reads the stored
  `:stale` mark (`dispute/stale?`) rather than the whole lifecycle state: every entry
  `disputes-in` hands back is live by construction, and `dispute-state` establishes
  liveness with a fresh `contradictions` + `conflicts` scan — so asking it per entry would
  re-derive what the enumeration just settled, at a whole-KB scan apiece."
  [kb channel]
  (let [cutoff (- (now) *timeout-ms*)
        swept  (filterv (fn [e]
                          (and (not (d/stale? kb (:dispute-id e)))
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

(defn who-ruled
  "Read a ruling off its handle: `{:arbiter :dispute-ids :at}` from the provenance `rule`
  stamped, or nil if `ruling-handle` is not an adjudication assertion.  'Which disputes
  this sentex is the standing ruling of, who ruled them, and when' as a provenance read.

  `:dispute-ids` is a **set**, and it has to be.  Canonical dedup gives one sentex per
  (sentence, context), so an arbiter who rules two disputes the same way — the same
  claim upheld against two different opponents — is stamping one handle twice, and a
  single-valued tag would keep only the later id.  The earlier dispute would then read
  no standing ruling at all, skip the one-ruling-per-arbiter guard, and land a second
  monotonic ruling beside the first: two known-true claims on one clash, a `:conflict`
  no ruling can settle."
  [kb ruling-handle]
  (let [p (v/provenance kb ruling-handle)]
    (when-let [dids (:adjudication p)]
      {:arbiter (:creator p) :dispute-ids (set dids) :at (:created p)})))

(defn standing-rulings
  "The rulings `arbiter` currently holds on dispute `id`: the handles in the arbiter's own
  context whose provenance `rule` tagged with `id`.  One provenance read per sentex in
  that context — an arbiter's context holds its rulings and whatever else the agent
  asserts, and the tag is what tells them apart.

  **Believed rulings only** (`{:believed? true}`).  A ruling this arbiter no longer believes
  is not one they hold, and `rule`'s caller retracts what this returns: read unfiltered, a
  ruling already defeated or unsupported would be withdrawn a second time as though it were
  the arbiter's standing word on the dispute.

  Ranked by the ruling's own **sentence**, so the answer is content-ordered rather than
  an artifact of the extent's seq order — and rather than of the handles, which are
  allocated in assertion order, so ranking on one would make `resolve-by-majority`'s
  `:withdrawn` list a fact about how the KB was loaded.  One context holds them and
  canonical dedup gives one sentex per (sentence, context), so the sentence alone is a
  total order.

  The order is the engine's structural one (`nm/sort-by-content-key`, i.e.
  `nm/compare-form`), which is the whole reason to use it here rather than a printed key:
  it walks the two forms instead of printing them, so no ambient `*print-*` var can elide
  two rulings to one key and drop the tie back onto the enumeration order this exists to
  keep out — and it reads numbers numerically, so a ruling of 9 precedes one of 10."
  [kb arbiter id]
  (let [k (d/dispute-key id)]
    (into [] (comp (map :id)
                   (filter #(contains? (:dispute-ids (who-ruled kb %)) k))
                   (distinct))
          (nm/sort-by-content-key :sentence
                                  (v/sentexes-in-context kb (id/context-for arbiter)
                                                         {:believed? true})))))

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

  **One ruling per arbiter per dispute.**  A ruling this arbiter already holds on `id`
  for the *other* side is retracted first — two monotonic rulings on one clash are a
  `:conflict` no ruling can settle, and the later word is the arbiter's current one.
  Ruling the same side again is a belief no-op that returns the standing handle.

  **Reversible.**  Retract the returned handle and the losing side is no longer defeated —
  the dispute reopens, cascading through the JTMS.  A ruling koinii could not undo would be
  a worse store than one that stays honestly disputed.  The dispute's open/notified/stale
  marks are cleared once the ruling has LANDED and the episode is over, so a reopen starts
  fresh at `:open` (and re-notifies) — and a REFUSED ruling clears nothing, leaving the
  episode exactly as it found it.  Returns the ruling handle.

  Resolves a `:default` coexisting dilemma only.  A `:monotonic` `:conflict` (two things
  asserted known-true) cannot be settled by a monotonic ruling — it needs a human to
  retract a premise — so it is not this path's job.

  **An arbiter who is a party to the dispute is refused** (`:arbiter-is-party`).  A ruling
  is an assertion in the arbiter's own context, so for a party that context already holds
  one of the two clashing sentences: ruling their own way would silently restamp their
  claim as its own adjudication, and ruling the other way would *retract* it — the
  disputed claim deleted rather than the dispute settled, which `dispute-state` then reads
  as `:resolved` because there is no longer a clash to see.  Whether an arbiter may judge
  their own case is not a question this can answer by guessing, so it does not."
  [kb arbiter id upheld channel]
  (let [actx (id/context-for arbiter)
        k    (d/dispute-key id)
        held (set (keep #(v/sentex kb %) (if (sequential? k) k [k])))
        ;; the arbiter's own *claims*, which is what makes them a party — a sentex their
        ;; context holds and BELIEVES that is not one of their own rulings.  A standing
        ;; ruling is exactly what this call is entitled to supersede, so it is not evidence
        ;; of anything, and re-ruling must not read it as taking a side.  Belief-filtered
        ;; (`{:believed? true}`) because a claim the arbiter's context stores but no longer
        ;; believes is not a side they hold: a defeated claim would convict them of being a
        ;; party to a dispute they have already stepped out of.
        mine (into #{} (comp (remove #(who-ruled kb (:id %))) (map :sentence))
                   (v/sentexes-in-context kb actx {:believed? true}))]
    (when (some #(contains? mine (:sentence %)) held)
      (throw (ex-info (str "koinii: " arbiter " is a party to dispute " (pr-str k)
                           " — an arbiter's ruling lands in the arbiter's own context, so"
                           " ruling a dispute they hold a side of would restamp or retract"
                           " their own claim rather than settle the clash")
                      {:type :arbiter-is-party :arbiter arbiter :dispute-id k})))
    (v/assert kb (list 'genlCx channel actx) 'CxUniverse {:strength :monotonic})
    (let [same    (v/handle-of kb upheld actx)
          stale   (remove #{same} (standing-rulings kb arbiter id))
          ;; the tag is a set, and this handle may already carry other disputes' ids —
          ;; ruling one must not un-rule another that dedups onto the same sentex
          carried (when same (:dispute-ids (who-ruled kb same)))
          ;; one settle: the replacement lands before the displaced ruling goes, so a
          ;; throw between them cannot leave the arbiter having retracted a ruling and
          ;; asserted nothing (`edit!` adds first, then removes)
          res     (v/edit! kb {:add    [[upheld actx {:strength :monotonic :creator arbiter
                                                      :provenance {:adjudication
                                                                   (conj (set carried) k)}}]]
                               :remove (vec stale)})]
      ;; the lifecycle episode ends only once the ruling has LANDED.  `edit!` refuses an
      ;; inadmissible replacement by throwing, and clearing the marks first would leave the
      ;; dispute reopened and un-notified with nothing ruled on it — the driver then
      ;; re-announcing a clash whose ruling never happened.
      (d/reopen! kb id)                                  ; end the lifecycle episode
      (first (:added res)))))

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

  **The count is the authority, every time.**  The house can change its mind — ballots
  are retracted and re-cast — and a ruling that no longer matches the count is withdrawn
  before the new one lands: a majority that swings retracts the standing ruling and
  rules the other side (`rule`'s one-ruling-per-arbiter contract), and a majority that
  dissolves into a tie retracts it and leaves the dispute open.  Left standing, the old
  ruling and the new would be two monotonic claims on one clash — a `:conflict`
  reported as `:contradiction`, under a return value claiming the swing carried.

  Returns `{:for n :against n :outcome :for/:against/:tie :ruling handle-or-nil
  :withdrawn [handle …]}`, `:withdrawn` naming the rulings this count retired.
  Idempotent: re-running on an unchanged count re-rules the same side (a belief no-op
  returning the standing handle) and withdraws nothing, so a driver may poll it."
  [kb id claim-handle channel]
  (let [{yes :for no :against :as counts} (tally kb claim-handle)
        claim    (:sentence (v/sentex kb claim-handle))
        standing (standing-rulings kb majority-arbiter id)
        decide   (fn [outcome upheld]
                   (let [h (rule kb majority-arbiter id upheld channel)]
                     (assoc counts :outcome outcome :ruling h
                            :withdrawn (filterv #(not= h %) standing))))]
    (cond
      (> yes no) (decide :for claim)
      (> no yes) (decide :against (list 'not claim))
      :else      (do (doseq [h standing] (v/retract! kb h))
                     (assoc counts :outcome :tie :ruling nil :withdrawn standing)))))

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
  contested premise handles.

  **Content-ordered.**  `support-handles` walks a graph into a set, whose seq order is a
  hash artifact, and the handles themselves are allocated in assertion order — so ranking
  on either would make this list a fact about how the KB was loaded.  The order is the
  premise's own `[sentence context]` (`nm/sort-by-content-key`), which two KBs holding the
  same knowledge agree on whatever order they were built in."
  [kb S ctx]
  (if-let [h (v/handle-of kb S ctx)]
    (let [contested (into #{} (mapcat :dispute-id) (d/disputes-in kb ctx))]
      (nm/sort-by-content-key #(let [sx (v/sentex kb %)] [(:sentence sx) (:context sx)])
                              (filterv contested (support-handles kb h))))
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

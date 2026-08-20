;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.koinii.dispute
  "Koinii dispute reads: two context-scoped views over the engine's
  whole-KB contradiction surface, plus the small dispute-STATE surface the
  adjudication driver drives.

  The engine *represents* contradiction but answers it only whole-KB: `contradictions`
  and `conflicts` each scan the whole store and hand back entries whose sides carry
  their own `:context`.  A subscriber wants the per-channel question — 'is there an open
  dispute *here*?' — so that scoping lives in one wrapper rather than being re-derived at
  every call site.

  **'Disputed' is a precise word.**  It is NOT 'false' and NOT 'defeated-by-strength'.
  A dispute is a *coexisting* clash — S and ¬S both believed with no strength winner, so
  `argue` returns `:contradiction` and the engine deliberately leaves both standing
  (paraconsistent tolerance — Priest's LP, the four-valued `argue`).  A clean
  strength-defeat (a `:monotonic` premise beating a `:default` one) is the opposite: the
  loser is `:defeated`, `argue` returns `:false`, and that is *resolved*, not disputed.

  Two error classes, kept distinct, never merged:

  - **`:contradiction`** — a coexisting `:default` dilemma (a rebuttal, or a definitional
    clash left at equal strength).  Both sides believed; `argue` -> `:contradiction`.
  - **`:conflict`** — an irreducible clash among `:monotonic` content: two things asserted
    known-true that cannot both hold, which the engine has no grounds to prefer.  Harder
    than a rebuttal, and a caller usually wants to see it alongside.

  **Detection matches the engine, not the intuition.**  A coexisting dilemma keeps BOTH
  sides `in?`, so `why-not` reports `:believed? true` on either — it never reads
  `:defeated` there (that reason is reserved for the strength-defeat, i.e. the resolved
  case).  So the named-sentence read is `argue`, whose `:contradiction` verdict is exactly
  'both provable, neither strength-wins' and whose context scoping is exactly 'the asker
  sees both sides'.  `argue` is per-sentence and never computes whole-KB contradictions,
  which is the perf property the hot path needs.

  This module owns the *reads*, the state *vocabulary*, and the dispute *id*.  The clock,
  the timeout value, and the notify sink are the driver's.  So the
  recording functions here take the timestamp (and stale reason) from the caller rather
  than reading a clock: this module supplies the mechanism, the driver supplies the policy.

  Additive, like the sibling koinii modules: only the public core API (`argue`,
  `canonical-sentex`, `sentex-handle`) — nothing under `vaelii.impl`, and nothing in core
  loads it."
  (:require [vaelii.core :as v]))

;; ---- the dispute id: a stable name for one clash -------------------------

(defn dispute-id
  "The stable id of a dispute `entry` (from `disputes-in`, `contradictions`, or
  `conflicts`): the sorted pair of its two side `:handle`s.  Order-independent, so the
  same clash always yields the same id however the engine happened to order the sides —
  the key the driver attaches lifecycle state to."
  [entry]
  (vec (sort (:handles entry))))

(defn dispute-term
  "The reified term naming a dispute by its id, for the stored lifecycle marks:
  `(dispute (sentexHandle lo) (sentexHandle hi))`, handles sorted so the term is a
  function of the clash and not of argument order.  `id` is a `dispute-id` (a handle
  pair) or any two-handle seq."
  [id]
  (let [[lo hi] (sort id)]
    (list 'dispute (v/sentex-handle lo) (v/sentex-handle hi))))

;; ---- disputes-in: the whole surface, scoped to what a context sees -------

(defn- observed-by?
  "Does `ctx` observe the clash `entry` — i.e. can it read BOTH clashing sides?  A
  contradiction is visible exactly where both its sentences are readable, up the
  `genlCx` cone (`sees?`).  So a clash between `(ist CxAtlas P)` and `(ist CxBoreas ¬P)`
  surfaces in the channel `CxDeploy` (which sees both agent contexts) and NOT in a
  sibling that sees only one — from a one-sided vantage there is no clash to see, and
  `argue` from there returns `:true`, not `:contradiction`.  Both-sides is what keeps the
  named read (`disputed?`, `argue`-based) and this whole-surface read agreeing."
  [kb ctx entry]
  (every? (fn [side] (v/sees? kb ctx (:context side))) (:sides entry)))

(defn disputes-in
  "The disputes a context `ctx` observes: every `contradictions` and `conflicts` entry
  both of whose sides `ctx` sees, each tagged with its `:dispute-class`
  (`:contradiction` — a coexisting `:default` dilemma / `:conflict` — a `:monotonic`
  irreducible clash) and its stable `:dispute-id`.  The engine entry's own `:kind`
  (`:disjoint` / `:functional` / `:asymmetric`, nil for a plain rebuttal) rides along
  unchanged.

  This is the per-channel view the whole-KB `contradictions` cannot give: 'what is
  disputed *here*'.  It hides nothing and invents nothing — the union of `disputes-in`
  over every context equals `(contradictions kb)` + `(conflicts kb)`, because the
  common-descendant context that raised each clash sees both of its sides and so reports
  it.  Conflicts are folded in by default (most callers want the harder monotonic clashes
  beside the rebuttals); a caller wanting only one class filters on `:dispute-class`."
  [kb ctx]
  (->> (concat (map #(assoc % :dispute-class :contradiction) (v/contradictions kb))
               (map #(assoc % :dispute-class :conflict)      (v/conflicts kb)))
       (filter #(observed-by? kb ctx %))
       (mapv   #(assoc % :dispute-id (dispute-id %)))))

;; ---- disputed?: the per-sentence hot path, and the thin any-path ---------

(defn disputed?
  "Is there an open dispute?  Two arities:

  - **`(disputed? kb ctx)`** — is *anything* disputed in `ctx`?  Thin over
    `disputes-in`.

  - **`(disputed? kb S ctx)` / `(disputed? kb S ctx opts)`** — is the named sentence `S`
    disputed in `ctx`?  THE HOT PATH: a scoped `argue` read, which never computes whole-KB
    contradictions (subscribers call it in a loop, so that is a perf property, not a
    nicety).  `S` is disputed exactly when `argue` returns `:contradiction` — S and ¬S
    both provable from `ctx` with no strength winner — which is a coexisting `:default`
    dilemma OR a `:monotonic` conflict, but NOT a clean strength-defeat (that returns
    `:false`: resolved, not disputed).  `opts` (e.g. `{:max-depth n}`) is passed to
    `argue`; without it `argue` uses `ask?` — ground facts and provers, no rule expansion —
    which is what a koinii dispute (an asserted `¬S`) needs.

  Arity tells the two apart: 2 args is `(kb ctx)`, 3+ is `(kb S ctx …)`."
  ([kb ctx] (boolean (seq (disputes-in kb ctx))))
  ([kb S ctx] (disputed? kb S ctx nil))
  ([kb S ctx opts]
   (= :contradiction (:verdict (v/argue kb S ctx opts)))))

;; ---- the dispute lifecycle (koinii design D9) ----------------------------
;;
;; open -> notified -> resolved, with a stale sweep for the un-ruled.  Two of the four
;; states are DERIVED from current belief (`:open`, `:resolved`) and two are STORED as
;; ordinary assertions (`:notified`, `:stale`) — stored so `why` explains them and
;; retracting one reopens the dispute.  This module records and reads them; the driver decides
;; WHEN (the clock, the timeout, the notify sink).

(def state-context
  "The coordination context the stored lifecycle marks (`:notified`, `:stale`) live in.
  A dispute id is globally unique within the KB (a handle pair), so one well-known place
  to look suffices; the marks are bookkeeping, not channel knowledge, so they sit apart
  from the channels' own reasoning."
  'CxDisputes)

(defn- marks-of
  "The stored lifecycle mark sentexes for `id` under `pred` (arity per pred), in
  `state-context`."
  [kb pred id args]
  (v/sentexes-matching kb (list* pred (dispute-term id) args) state-context))

(defn notified?
  "Is there a stored `:notified` mark for dispute `id`?"
  [kb id]
  (boolean (seq (marks-of kb 'disputeNotified id ['?at]))))

(defn stale?
  "Is there a stored `:stale` mark for dispute `id`?"
  [kb id]
  (boolean (seq (marks-of kb 'disputeStale id ['?at '?reason]))))

(defn mark-notified
  "Record that dispute `id` has been pushed to subscribers / a human, at time `at` (the
  caller — the driver — supplies the clock).  An ordinary assertion
  `(disputeNotified (dispute …) at)` in `state-context`, so `why` explains it and a
  retract (`reopen!`) un-notifies.  The mark is what stops the driver re-notifying a clash it
  has already announced.  Returns the mark's handle."
  [kb id at]
  (v/assert kb (list 'disputeNotified (dispute-term id) at) state-context))

(defn mark-stale
  "Record that dispute `id` aged out — open past the driver's timeout with no ruling — at time
  `at`, tagged with `reason` (a symbol, e.g. `TimedOut`).  An ordinary assertion
  `(disputeStale (dispute …) at reason)` in `state-context`, so open disputes do not pile
  up unmarked and `why` can explain the sweep.  Staleness does not resolve the clash — the
  dispute is still live — it only flags it.  Returns the mark's handle."
  [kb id at reason]
  (v/assert kb (list 'disputeStale (dispute-term id) at reason) state-context))

(defn reopen!
  "Retract every stored `:notified` / `:stale` mark on dispute `id`, returning it to
  `:open` (if the clash is still live).  The inverse of `mark-notified` / `mark-stale`,
  and the reason those states are stored rather than derived: retract the ruling and the
  dispute reopens.  Returns the number of marks retracted."
  [kb id]
  (reduce (fn [n sx] (v/retract! kb (:id sx)) (inc n))
          0
          (concat (marks-of kb 'disputeNotified id ['?at])
                  (marks-of kb 'disputeStale id ['?at '?reason]))))

(defn- live-ids
  "The ids of every clash currently on the whole-KB surface — `contradictions` +
  `conflicts`.  A whole-KB scan; the lifecycle driver is not the hot path (that is the
  named `disputed?`), so this is where the scan is affordable."
  [kb]
  (into #{} (map dispute-id) (concat (v/contradictions kb) (v/conflicts kb))))

(defn- mark-state
  "The state implied by the stored marks alone (`:stale` > `:notified` > `:open`), for a
  clash already known to be live."
  [kb id]
  (cond (stale? kb id)    :stale
        (notified? kb id) :notified
        :else             :open))

(defn dispute-state
  "The lifecycle state of dispute `id`:

  - `:open`     — live, no mark recorded (`disputes-in`/`disputed?` report it, `argue`
                  returns `:contradiction`).  Derived.
  - `:notified` — live, and the driver has recorded a notify mark.  Stored.
  - `:stale`    — live, and the driver has recorded a stale sweep.  Stored.
  - `:resolved` — no longer live: a side was retracted or strength-demoted, the clash is
                  gone and `argue` has collapsed to `:true`/`:false`.  Derived.

  For an `id` obtained from `disputes-in` (the contract), `:resolved` means 'was a
  dispute, now settled'; an id that was never a clash also reads `:resolved` (absent = not
  an open dispute here).  Reading state runs a whole-KB liveness scan — fine for the
  driver, which is not the loop `disputed?` serves."
  [kb id]
  (if (contains? (live-ids kb) (vec (sort id)))
    (mark-state kb id)
    :resolved))

(defn pending-disputes
  "The disputes `ctx` observes that still need announcing — `disputes-in` entries in
  state `:open` (no notify/stale mark yet).  The driver's work-list: the clashes to push.  Each
  entry from `disputes-in` is live by construction, so this checks the marks, not liveness
  again."
  [kb ctx]
  (filterv #(= :open (mark-state kb (:dispute-id %))) (disputes-in kb ctx)))

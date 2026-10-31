;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.koinii.channel
  "Koinii's core coordination library: the async assert / reply loop an
  agent runs over a shared channel, with the KB as the medium.  An agent JOINS its own
  context, SUBSCRIBES to the channel over the change feed, and REPLIES to what it sees —
  all decoupled in time, nothing requiring two agents online at once.

  The mechanism is already in the engine (the change feed, docs/feed.md); this layer is
  ergonomics and correctness over it, not a new transport.  It commits three pieces of
  `koinii.md`'s *deployment shape* to code:

  - **D8, the per-agent context.**  An agent writes only its OWN context (`CxAtlas`),
    lifted under the channel (`(genlCx CxDeploy CxAtlas)`) so the channel sees the union
    of every agent's assertions.  Identity fixes the write destination (`identity`).
  - **D1, reply-as-meta-sentex.**  A reply is a META-SENTEX on its target (`speech_acts`'
    `answers` / `disputes` / `endorses` / `justifies`), so it lives ON the target rather
    than merely naming it: retract the target and its replies are torn down with it
    (`target_following_predicate`), no dangling edges.
  - **D7, the single-writer total order.**  See the docstring on `writer-order` below.

  **Two deployment shapes, one surface.**  The `Medium` protocol has two
  implementations, and which one an agent joins is the whole single-process /
  cross-process decision (`koinii.md`, *When to stop*):

  - **`wire`** — a daemon connection (`vaelii.client`).  The inter-agent case: agents are
    separate processes funnelling every write through the one daemon (the single writer),
    and `subscribe` runs the feed's `poll` loop OFF the agent's own thread.  This is the
    mandatory shape the moment agents are separate processes, and the reason is the
    writer's thread: an in-process feed callback runs ON the single writer's thread
    (docs/feed.md), so one slow agent would stall the writer for everyone.  Polling off
    the agent's thread is what removes that coupling.
  - **`local`** — an in-process KB.  Simpler, and correct when every agent lives in one
    process: `subscribe` is a plain `core/watch` listener, no cursor apparatus.  The
    callback runs on the writing thread, so a slow one still slows the writer — fine
    single-process, wrong across agents, which is why `wire` exists.

  `assert` / `answer` / `endorse` / `justify` / `dispute` / `vote` / `reply-many` and the
  recovery reads are shape-agnostic — they run the same over either medium; only
  `subscribe` differs, because only the feed does.

  Additive, like the sibling koinii modules: the public core API, `vaelii.client`, koinii
  `identity`, and Trove for the two subscription defaults.  Every write goes through the
  provenance-recording `assert` path — never `bulk-assert-facts!`."
  (:refer-clojure :exclude [assert])
  (:require [taoensso.trove :as trove]
            [vaelii.client :as c]
            [vaelii.core :as v]
            [vaelii.koinii.identity :as id]
            [vaelii.koinii.types :as koinii-types
             :refer [-assert -check-edit -edit -matching -query
                     -sentex -subscribe]]))

;; ---- D7: the single-writer total order -----------------------------------

(def ^{:doc
       "**Documentation of the consistency model, not a runtime value** (koinii design D7).

  The daemon serializes every write through one monitor (docs/operations.md), so the
  change-feed cursor delivers a TOTAL ORDER: every agent reads the same events in the same
  sequence, and an agent can only reply to a claim it has already seen.  The happy path is
  causally sound BY CONSTRUCTION.  **Logical clocks (Lamport / vector) are redundant
  here**: they reconstruct a causal order across CONCURRENT writers, and with one writer the
  store order is the causal order.  Causal metadata becomes necessary only if koinii goes
  multi-writer (multiple daemons over sharded KBs)."}
  writer-order
  :single-writer-total-order)

;; ---- the medium: the transport an agent coordinates over -----------------

;; ---- wire: the cross-process shape, the poll loop off the agent's thread --

(defn- wire-subscribe
  "Open a wire subscription and drive its `poll` loop on a fresh DAEMON thread, never the
  writer's.  Long-polls with `:wait-ms` (default 20s), hands each event to `callback`, and
  reads `:lagged` on every reply (docs/feed.md): non-zero, the ring dropped events and
  `:on-lagged` is told the count so the agent can resync from the KB.  A `callback` that
  throws loses its own event only (`:on-error`, then carry on).  When the subscription is
  dropped (`stop`, or an idle reap) the parked poll wakes refused and the loop exits.

  **Neither extension point is silent when unset**: `:on-lagged` defaults to a `:warn` line
  naming the drop count and `:on-error` to an `:error` line naming the failure; a supplied
  handler replaces the line.  **`:running` is the subscription's liveness.**  The poll loop
  resets `:running` false at each exit.  A failed poll's exit resets `:running` before the
  loop unwatches the daemon's subscription.  `stop` resets `:running` to cut a batch short."
  [conn goal context callback opts]
  (let [{:keys [token cursor]} (if goal (c/watch conn goal context) (c/watch conn))
        wait-ms (:wait-ms opts 20000)
        on-lag  (:on-lagged opts)
        on-err  (:on-error opts)
        running (atom true)
        thr (Thread.
             (fn []
               (loop [cur cursor]
                 (when @running
                   ;; one arm, and `Throwable` for the reason the callback's arm below
                   ;; gives: an `Error` out of the poll that ended this thread would leave
                   ;; `running` true on a subscription that never delivers again
                   (let [step (try {:ok (c/poll conn token cur {:wait-ms wait-ms})}
                                   (catch Throwable e {:err e}))]
                     (if-let [e (:err step)]
                       ;; subscription gone (unwatch / reap / bad-cursor) -> stop quietly;
                       ;; anything else -> surface once, then stop rather than hot-loop.
                       ;; Either way the loop is over, so `running` is made to agree with
                       ;; it: a dead reader that still reads live is the one failure a
                       ;; subscriber cannot detect and so cannot resubscribe from.
                       (let [ty    (:type (ex-data e))
                             live? (compare-and-set! running true false)]
                         (when (and live? (not (#{:unknown-subscription :bad-cursor} ty)))
                           (if on-err
                             (on-err e)
                             (trove/log!
                              {:level :error :id ::subscription-failed
                               :msg   (str "koinii: subscription " token " stopped — the"
                                           " feed poll failed: " (ex-message e))
                               :data  {:token token :goal goal :context context}})))
                         (when (and live? (not= :unknown-subscription ty))
                           (try (c/unwatch conn token) (catch Throwable _ nil))))
                       (let [{:keys [events lagged cursor]} (:ok step)]
                         (when (pos? (long (or lagged 0)))
                           (if on-lag
                             (on-lag lagged)
                             (trove/log!
                              {:level :warn :id ::subscription-lagged
                               :msg   (str "koinii: subscription " token " dropped "
                                           lagged " event(s) — the ring outran this"
                                           " reader; resync from the KB")
                               :data  {:token token :lagged lagged
                                       :goal goal :context context}})))
                         ;; `Throwable`, because that is what the contract above says and
                         ;; what `core/notify-listener!` catches on the in-process side: a
                         ;; callback rendering a deeply nested event raises
                         ;; `StackOverflowError`, and an `Exception` catch would let it
                         ;; kill this daemon thread mid-batch — leaving `running` true and
                         ;; the feed silently stopped, which is the one failure a
                         ;; subscription must not have.
                         (doseq [ev events :while @running]
                           (try (callback ev)
                                (catch Throwable e
                                  (if on-err
                                    (on-err e)
                                    (trove/log!
                                     {:level :warn :id ::callback-threw
                                      :msg   (str "koinii: a subscription callback threw;"
                                                  " skipping its event: " (ex-message e))
                                      :data  {:token token}})))))
                         (recur cursor))))))))]
    (.setName thr (str "koinii-subscribe-" token))
    (.setDaemon thr true)
    (.start thr)
    {:token token :medium :wire :thread thr :running running
     :stop (fn []
             (reset! running false)
             (try (c/unwatch conn token) (catch Exception _ nil)))}))

(defrecord WireMedium [conn]
  koinii-types/Medium
  (-assert     [{:keys [conn]} s ctx opts] (c/assert conn s ctx opts))
  (-sentex     [{:keys [conn]} h]          (c/sentex conn h))
  (-matching   [{:keys [conn]} s ctx]      (c/sentexes-matching conn s ctx))
  (-check-edit [{:keys [conn]} batch]      (c/call conn :check-edit [batch]))
  (-edit       [{:keys [conn]} batch]      (c/call conn :edit [batch]))
  (-subscribe  [{:keys [conn]} goal ctx cb opts] (wire-subscribe conn goal ctx cb opts))
  (-query      [{:keys [conn]} goal ctx]   (c/query conn goal ctx))
  (-feed-open  [{:keys [conn]} goal ctx]   (if goal (c/watch conn goal ctx) (c/watch conn)))
  (-feed-poll  [{:keys [conn]} token cursor opts]
    (if opts (c/poll conn token cursor opts) (c/poll conn token cursor)))
  (-feed-close [{:keys [conn]} token]     (c/unwatch conn token)))

;; ---- local: the single-process shape, a plain in-process listener --------

(defrecord LocalMedium [kb]
  koinii-types/Medium
  (-assert     [{:keys [kb]} s ctx opts] (v/assert kb s ctx opts))
  (-sentex     [{:keys [kb]} h]          (v/sentex kb h))
  (-matching   [{:keys [kb]} s ctx]      (v/sentexes-matching kb s ctx))
  (-check-edit [{:keys [kb]} batch]      (v/check-edit kb batch))
  (-edit       [{:keys [kb]} batch]      (v/edit! kb batch))
  (-subscribe  [{:keys [kb]} goal ctx cb _opts]
    ;; `core/watch` IS the in-process feed; the callback runs on the writing thread
    ;; (docs/feed.md), so a slow one slows the writer — acceptable single-process, and
    ;; the reason `wire` exists for the cross-process case.  No cursor / lag / wait: the
    ;; in-process feed has no ring, so the wire-only opts are ignored.
    (let [tok (if goal (v/watch kb goal ctx cb) (v/watch kb cb))]
      {:token tok :medium :local :stop (fn [] (v/unwatch kb tok))}))
  (-query      [{:keys [kb]} goal ctx]   (v/query kb goal ctx))
  (-feed-open  [_ _goal _ctx]
    (throw (ex-info (str "koinii: an in-process medium has no cursor feed — catch-up is a"
                         " wire-only concern, and there is no ring here to fall off."
                         "  Subscribe to this medium for a live feed, or take a wire"
                         " medium (koinii.channel/wire over a daemon connection) for a"
                         " cursor")
                    {:type :koinii/no-wire-feed})))
  (-feed-poll  [_ _token _cursor _opts]
    (throw (ex-info (str "koinii: an in-process medium has no cursor feed — nothing here"
                         " issues a poll token, so there is none to resume from."
                         "  Subscribe to this medium, or take a wire medium"
                         " (koinii.channel/wire over a daemon connection)")
                    {:type :koinii/no-wire-feed})))
  (-feed-close [_ _token]
    (throw (ex-info (str "koinii: an in-process medium has no cursor feed — nothing here"
                         " issues a poll token, so there is none to close")
                    {:type :koinii/no-wire-feed}))))

(defn wire
  "A channel medium over a daemon connection `conn` (from `vaelii.client/client`) — the
  cross-process shape.  Every write funnels through the daemon (the single writer) and
  `subscribe` polls the wire feed off the agent's thread."
  [conn]
  (->WireMedium conn))

(defn local
  "A channel medium over an in-process KB — the single-process shape.  `subscribe` is a
  plain `core/watch` listener; simpler, and correct when every agent is in one process."
  [kb]
  (->LocalMedium kb))

;; ---- join: an agent bound to its identity, context, and the channel ------

(defn- agent-context-owners
  "The agents `ctx` is the own context of, in content order, read off the MARK every koinii
  placement writes into a context it places (`id/agent-context-mark`); empty for a context
  nobody has placed.  The mark is a positive stored fact, so the read is deterministic
  (the match is a SET, ordered by content).  Two ids mapping to one context (`Atlas` and
  `AgentAtlas` both give `CxAtlas`) is the only way to have more than one."
  [medium ctx]
  (into (sorted-set)
        (map (comp last :sentence))
        (-matching medium (id/agent-context-mark ctx '?agent) ctx)))

(defn- check-channel-parent
  "Throw unless `parent` is a coordination channel.  `join` widens what `parent` sees: every
  ancestor set read of `parent` returns the joining agent's claims, and with
  `belief/believe-own` they become what `parent`'s own agent is proved to believe.  So a
  parent is refused (`:koinii/not-a-channel`) when it is

  - the admin registry, which governs the agents rather than hosting them;
  - the joining agent's own context, which a join LIFTS and cannot also lift under;
  - a context already placed as an agent's own (`agent-context-owners`).

  **An unmarked context is admissible**: a channel carries no mark, so refusing what is
  unmarked would refuse every deployment.  A context placed by a build that wrote no mark
  reads as unmarked, and a placement is idempotent, so the mark lands the next time that
  agent joins.  Recognition reaches as far as the placements a KB records, the cooperative
  limit `authenticate` states."
  [medium parent agent-id]
  (let [owners (agent-context-owners medium parent)
        why    (cond
                 (= parent id/registry-context)
                 "the admin registry governs agents rather than hosting them"

                 (= parent (id/context-for agent-id))
                 "an agent's own context is what a join lifts, never what it lifts under"

                 (seq owners)
                 (str "that context is already placed as " (first owners) "'s own"))]
    (when why
      (throw (ex-info (str "koinii: " agent-id " cannot join under " parent
                           " — a channel is a context agents are lifted INTO, and " why)
                      {:type :koinii/not-a-channel :agent agent-id :parent parent
                       :owners owners})))))

(defn join
  "Bind `agent-id` to `medium` and the coordination `channel` (koinii design D8).  The agent's
  own context (`id/context-for`, `AgentAtlas` -> `CxAtlas`) is lifted under the channel
  (`(genlCx channel CxAtlas)`), rooted so it speaks the reply vocabulary
  (`(genlCx CxAtlas CxSpeechActs)`, override with `:speaks`), and marked as the agent's own
  (`id/agent-context-mark`).  All three are monotonic and idempotent.  Returns the agent
  handle `{:medium :agent :context :channel}`, threaded first into every call below.

  **The channel must be a channel** (`:koinii/not-a-channel`): grafting onto the admin
  registry, the agent's own context, or a context placed as another agent's own is refused
  (`check-channel-parent`).  Requires the `channel` and `CxSpeechActs` already loaded, so the
  `target_following_predicate` marks that make a reply cascade are in force."
  ([medium channel agent-id] (join medium channel agent-id nil))
  ([medium channel agent-id opts]
   ;; the write boundary, enforced at the entry point rather than trusted to the destination:
   ;; joining AS the admin registry (`AgentRegistry` -> `CxRegistry`) is refused here,
   ;; where `place-agent-context` would otherwise make that context writable
   (id/check-registry-write! agent-id (id/context-for agent-id))
   (let [roots (:speaks opts 'CxSpeechActs)]
     ;; and the other end of the same edge: the context the agent is grafted UNDER
     (check-channel-parent medium channel agent-id)
     ;; `identity`'s placement, written through the MEDIUM rather than straight to a KB —
     ;; for a `wire` handle that is the daemon, the single writer
     (let [actx (id/place-agent-context #(-assert medium %1 %2 %3) channel agent-id roots)]
       {:medium medium :agent agent-id :context actx :channel channel}))))

(def ^:private agent-first-acts
  "The speech-act predicates whose FIRST argument names the speaker — every act
  `speaker-of` / `responder-of` reads a `?agent` off (`queries` originates, the rest
  respond, the two ballots are counted).  A sentence with one of these functors is a
  claim ABOUT who spoke, so `assert` refuses one that names anyone but the handle's own
  agent: otherwise `speaker-of` (read off the sentence) and the `:creator` provenance the
  entry point records would disagree, and an agent could sign another's name."
  '#{queries answers endorses justifies disputes votesFor votesAgainst notUnderstood refuse})

(defn- check-write-entry-points
  "Throw unless `handle`'s agent may write `sentence` under `opts`: the ONE place an agent
  write's boundary is stated, held by `assert` and `reply-many`.  Three refusals:

  - **the admin registry is not writable through an agent entry point**
    (`:koinii/registry-forbidden`), whatever context the handle carries (D4).  Own-context-only
    is a proof-tier rule these cooperative entry points do not impose.
  - **a `:creator` that disagrees with the handle's agent** (`:koinii/creator-mismatch`):
    `belief/disregard` withdraws only a statement whose creator is the withdrawing agent,
    so honouring it lets an agent sign another's name and dropping it leaves a creator that
    looks like it took.
  - **a speech act naming someone else as its speaker** (`:koinii/speaker-mismatch`):
    `speaker-of` reads the first argument while the creator comes off the handle.

  `opts` is the map that will be WRITTEN, so `reply-many`'s own `{:creator agent}` passes
  through the creator arm like any caller's."
  [handle sentence opts]
  (let [agent (:agent handle)]
    (id/check-registry-write! agent (:context handle))
    (when (and (contains? opts :creator) (not= (:creator opts) agent))
      (throw (ex-info (str "koinii: " agent " cannot assert as " (pr-str (:creator opts))
                           " — a claim originated through an agent handle records that"
                           " agent as its creator, which is what makes the write boundary an identity")
                      {:type :koinii/creator-mismatch
                       :agent agent :creator (:creator opts)})))
    (when (and (seq? sentence) (contains? agent-first-acts (first sentence))
               (not= (second sentence) agent))
      (throw (ex-info (str "koinii: " agent " cannot speak as " (pr-str (second sentence))
                           " — a " (first sentence) " names its speaker, and a handle"
                           " speaks as itself")
                      {:type :koinii/speaker-mismatch
                       :agent agent :named (second sentence) :act (first sentence)})))))

(defn assert
  "Originate a claim: assert `sentence` into the agent's OWN context, recording `:creator` as
  the agent, through the medium (for a `wire` handle, through the daemon).  The destination
  is fixed by identity, and a speech act it asserts names that agent as its speaker
  (`:koinii/speaker-mismatch` otherwise).  Returns the handle.  **A conflicting `:creator` is
  refused** (`:koinii/creator-mismatch`); the agent's own id is redundant and allowed.
  Every other `opts` key passes through.  The refusals are stated once in
  `check-write-entry-points` and held identically by `reply-many`."
  ([handle sentence] (assert handle sentence nil))
  ([handle sentence opts]
   (check-write-entry-points handle sentence opts)
   (-assert (:medium handle) sentence (:context handle)
            (assoc opts :creator (:agent handle)))))

(defn pose-query
  "Originate a query NODE `(queries agent question)` in the agent's own context — the
  thing a responder later `answer`s by handle.  Minted (unlike a plain
  `assert`) because a question must be told apart from a claim.  Returns its handle."
  [handle question]
  (assert handle (list 'queries (:agent handle) question)))

;; ---- reply: the response act as a meta-sentex on its target --------------
;;
;; The sugar that turns "respond to target T" into asserting a speech-act response
;; meta-sentex ON T, in the replying agent's own context, with its creator recorded.  Two
;; properties fall out of the shape and are why it is a meta-sentex rather than a bare
;; assertion (koinii.md, *Reply is an assertion*):
;;
;;   - **Idempotent by sentence identity.**  Re-asserting the same meta-sentex in the
;;     same context is a no-op (one sentex, one handle, no belief moved) — first-writer-
;;     wins.  That is what makes an at-least-once feed safe to act on: replay a reply and
;;     the KB is unchanged.
;;   - **No dangling edges (D7).**  The reply lives ON its target (`(sentexHandle T)`, a
;;     `target_following_predicate`), so retracting T tears its replies down with it
;;     (docs/storage.md).  A bare assertion that merely NAMED T would outlive it.

(defn answer
  "`answers`: reply to the query at `target-handle` with `content`.  A ternary meta-sentex
  `(answers agent content (sentexHandle T))` in the agent's own context, creator recorded.
  The answerer's identity is read off THIS sentex, never off the query.  Returns the
  answer's handle; a re-answer with the same content returns that same handle."
  [handle content target-handle]
  (assert handle (list 'answers (:agent handle) content (v/sentex-handle target-handle))))

(defn endorse
  "`endorses`: stand behind the claim at `target-handle`.  A binary meta-sentex
  `(endorses agent (sentexHandle T))`.  Two endorsers of one claim are two distinct
  sentexes with two creators — the case a bare re-assert would collapse to one.  Returns
  the endorsement's handle."
  [handle target-handle]
  (assert handle (list 'endorses (:agent handle) (v/sentex-handle target-handle))))

(defn justify
  "`justifies`: offer `ground` as a reason for the claim at `target-handle`.  A ternary
  meta-sentex `(justifies agent ground (sentexHandle T))`.  Returns its handle."
  [handle ground target-handle]
  (assert handle (list 'justifies (:agent handle) ground (v/sentex-handle target-handle))))

(defn dispute
  "`disputes`: challenge the claim at `target-handle`.  Two writes in the agent's own context,
  creator recorded: the REBUTTING claim (the negation of the target's sentence, so the pair
  surfaces in `(contradictions kb)`) and a `disputes` meta-sentex naming the target.
  Represents the challenge only; adjudication is a separate policy layer.  Returns the
  dispute edge's handle.  **A handle that names no record is refused**
  (`:koinii/no-such-handle`), as `deref`'s `marker` refuses one, since the rebuttal would
  assert `(not nil)`."
  [handle target-handle]
  (let [sx (-sentex (:medium handle) target-handle)]
    (when (nil? sx)
      (throw (ex-info (str "koinii: cannot dispute handle " (pr-str target-handle)
                           " — it names no record on this medium")
                      {:type :koinii/no-such-handle :handle target-handle})))
    (assert handle (list 'not (v/sentence-of sx)))
    (assert handle (list 'disputes (:agent handle) (v/sentex-handle target-handle)))))

(defn vote
  "Cast a ballot on the claim at `target-handle`: `stance` `:for` -> `(votesFor agent
  (sentexHandle T))`, `:against` -> `(votesAgainst agent (sentexHandle T))`.  A meta-sentex
  in the agent's own context, creator recorded, which a resolution policy COUNTS
  (`adjudication/tally`).  This entry point authenticates nobody, so its ballot carries no
  attestation, and `adjudication/resolve-by-majority` refuses a count that includes one
  unless a daemon holding a token table recorded the ballot's `:principal`;
  `adjudication/cast-ballot` casts the attested ballot in process.  A ballot is a response
  act (`target_following_predicate` in `CxSpeechActs`), so retracting the disputed claim
  withdraws its votes.  Idempotent by sentence identity: one ballot per agent per stance; to
  change a vote, retract the old ballot first.  Returns the ballot's handle.  **A stance
  that is neither is refused by name** (`:koinii/no-such-stance`, carrying the two that
  exist)."
  [handle stance target-handle]
  (let [pred (case stance
               :for     'votesFor
               :against 'votesAgainst
               (throw (ex-info (str "koinii: no such ballot stance " (pr-str stance)
                                    " — a vote is cast :for or :against")
                               {:type :koinii/no-such-stance :stance stance
                                :known [:for :against]})))]
    (assert handle (list pred (:agent handle) (v/sentex-handle target-handle)))))

;; ---- reply-many: a multi-claim reply that validates before it commits ----

(defn reply-many
  "Assert MORE THAN ONE linked claim as one reply: VALIDATE the whole batch with `check-edit`
  first, then commit it with `edit!` in one settle, since `edit!` is not atomic on a throw
  (docs/feed.md) and a mid-batch failure would leave a HALF-reply.  Each of `sentences` is
  asserted into the agent's own context, creator recorded.  **Every entry point `assert`
  holds, this holds for the whole batch before the first write**: the registry is not
  writable (`:koinii/registry-forbidden`) and no sentence may name another agent as its
  speaker (`:koinii/speaker-mismatch`, `check-write-entry-points`).  Throws
  `:koinii/reply-inadmissible` (carrying the `check-edit` `:problems`) if the batch is not
  admissible.  Returns `edit!`'s result."
  [handle sentences]
  (let [ctx  (:context handle)
        opts {:creator (:agent handle)}]
    (run! #(check-write-entry-points handle % opts) sentences)
    (let [batch {:add (mapv (fn [s] [s ctx opts]) sentences)}
          probs (-check-edit (:medium handle) batch)]
      (if (seq probs)
        (throw (ex-info (str "koinii: multi-claim reply refused — check-edit found "
                             (count probs) " problem(s) across the " (count sentences)
                             " claims, the first "
                             (pr-str (:type (first probs))) " on "
                             (pr-str (:entry (first probs))) ".  A batch lands whole or"
                             " not at all, so fix the entries in :problems and send it"
                             " again")
                        {:type :koinii/reply-inadmissible :problems probs}))
        (-edit (:medium handle) batch)))))

;; ---- subscribe: the async reply trigger ----------------------------------

(defn subscribe
  "Call `callback` when a claim matching `goal` appears or changes in `context`: the async
  reply trigger.  `goal` nil watches every change; a `goal` refused by `core/watch` is
  refused identically here.  Watch the CHANNEL context to see every agent's moves (the feed
  is scoped up the `genlCx` ancestor set).  For a `wire` handle the poll loop runs OFF the
  agent's own thread, since an in-process callback runs on the single writer's thread and
  one slow agent would stall every writer.  `opts`: `:wait-ms` (long-poll, wire only),
  `:on-lagged` (fn of the dropped count: resync from the KB), `:on-error` (fn of a
  throwable); unset, the wire shape LOGS each.

  Returns a subscription `{:token … :stop (fn []) …}`; `:stop` drops it (wire: it also wakes
  the parked poll, and `:running` reads false from then on).  A subscription is
  FORWARD-ONLY: history that predates it is recovered by READING the KB (`answers-to` /
  `sentexes-matching`), the durable half of the channel; the feed is the live half."
  ([handle goal context callback] (subscribe handle goal context callback nil))
  ([handle goal context callback opts]
   (-subscribe (:medium handle) goal context callback opts)))

(defn unsubscribe
  "Drop a `subscription` (from `subscribe`).  Idempotent."
  [subscription]
  ((:stop subscription)))

;; ---- reads: recover the conversation as knowledge ------------------------
;;
;; Decoupled-in-time catch-up: the KB persists every move, so an agent that connects
;; later reads the conversation whether or not its author is still online.  These match
;; with `?ctx` (anywhere) rather than a channel context, because `sentexes-matching`
;; scopes to a context's OWN sentexes — the target handle is globally unique, so a reply
;; naming it anywhere is a reply to it.

(defn answers-to
  "Every believed answer to the query `query-handle` — `(answers ?agent ?content
  (sentexHandle query-handle))`, matched anywhere.  'What answered the query, and who said
  it' is a plain read: pair each with `speaker-of` for who, and `answer-content` for what."
  [handle query-handle]
  (-matching (:medium handle) (list 'answers '?a '?c (v/sentex-handle query-handle)) '?ctx))

(defn endorsements-of
  "Every believed endorsement naming `target-handle` — `(endorses ?agent (sentexHandle
  target-handle))`, matched anywhere.  Distinct endorsers are distinct sentexes."
  [handle target-handle]
  (-matching (:medium handle) (list 'endorses '?a (v/sentex-handle target-handle)) '?ctx))

(defn open-queries
  "Every query node on the channel — `(queries ?agent ?question)`, matched anywhere.  The
  catch-up read: an agent connecting LATER reads the open questions from the durable KB,
  decoupled in time from whoever asked and whether they are still online."
  [handle]
  (-matching (:medium handle) (list 'queries '?a '?q) '?ctx))

(defn query
  "ANCESTOR-SET-AWARE solutions for `goal` in `context`, as binding maps — the read that sees a
  channel's agents' own-context sentexes up the genlCx ancestor set (unlike the direct
  `sentexes-matching` the reads above use).  It answers the channel's whole current view of
  `goal`, which is what catch-up (`catchup`) snapshots the state from."
  [handle goal context]
  (-query (:medium handle) goal context))

(defn speaker-of
  "Who made the response move `sentex` — its `?agent`, the FIRST argument of the
  meta-sentex.  Read off the reply's own sentence (so it crosses the wire without a
  provenance op) and equal to the `:creator` provenance the daemon recorded: the
  conversation is in the graph, not in the client."
  [sentex]
  (second (:sentence sentex)))

(defn answer-content
  "The `?content` of an `answers` move `sentex` — its third argument."
  [sentex]
  (nth (:sentence sentex) 2 nil))

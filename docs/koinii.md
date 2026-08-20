# Koinii: multi-agent coordination over one knowledge base

- **Covers:** the coordination layer that lets independent agents assert, reply, dispute
  and resolve over a **shared** KB — agents as contexts, moves as sentexes, the change
  feed as the medium — and the two deployment shapes it runs in (one single-writer daemon,
  or independently-replicated seats). The design decisions the koinii modules cite by
  number (D1, D3–D9) are tabled here.
- **Not here:** the per-function API — that is in the module docstrings under
  `vaelii.impl.koinii.*`; the change feed the channel rides →
  [feed.md](feed.md); the single-writer daemon and client → [operations.md](operations.md);
  modal belief projection → [belief.md](belief.md); paraconsistent contradiction and
  strength defeat → [nmtms.md](nmtms.md); the `except` visibility mask →
  [exceptions.md](exceptions.md); content-address canonicalization →
  [canonicalization.md](canonicalization.md).
- **Assumes:** sentex, context, `genlCx`, provenance / `:creator`, meta-sentex,
  `targetFollowingPredicate`, the change feed → [glossary.md](glossary.md),
  [contexts.md](contexts.md), [storage.md](storage.md), [feed.md](feed.md).

Koinii is the layer where more than one agent works over one knowledge base — a *shared,
common* store several parties read and write. Its whole claim is that a common-sense KB
**already is** the substrate a
group of agents needs to coordinate — identity, a shared medium, provenance, contradiction
handling, truth maintenance — so coordination is not a new transport bolted on the side but a
small vocabulary and a handful of conventions expressed **in the KB itself**.

It is **additive**. Nothing in `vaelii.core` loads it; every koinii module is built on the
public core API and the thin `vaelii.client`, exactly as `vaelii.impl.argue` is. Load a
koinii context explicitly (`identity/load-registry`, `speech-acts/load-speech-acts`) — the
starter walks only `upper/` and `middle/`, so a KB pays for koinii only when a deployment
asks for it.

## The model: agents are contexts, moves are knowledge

Three identifications carry the whole layer. Each reuses a core mechanism rather than adding
one.

- **An agent *is* a context.** Atlas writes into `CxAtlas`; the channel `CxDeploy` sees it
  through `(genlCx CxDeploy CxAtlas)`, so a read of the channel is the union of every agent's
  assertions and a read of `CxAtlas` alone is "everything Atlas said." Because context is
  part of sentex identity, Atlas's `P` and Boreas's `P` are two **distinct** sentexes with
  two creators — first-writer-wins provenance loses no co-source. Identity therefore needs no
  new subsystem: it is the context lattice, and the one enforcement point is "write your own
  context, and nothing else" (`identity/check-write-boundary!`).

- **A move *is* a sentex.** A question, an answer, an endorsement, a dispute — each is a
  fact in the KB, queryable and retractable and auditable like any other, not an out-of-band
  message. A **response** is a *meta-sentex on its target*, naming it by handle
  `(sentexHandle T)`; because it lives on the target, retracting the target sweeps its
  replies with it. This is the property a message bus cannot give (see *Reply is an
  assertion*).

- **The KB *is* the medium.** There is no separate broker. Agents coordinate by writing and
  reading; the live half is the **change feed** ([feed.md](feed.md)) — an agent subscribes
  and is told when belief moves — and the durable half is the store, which persists every
  move so an agent that connects later reads the conversation whether or not its author is
  still online. Decoupled in time by construction: history that predates a subscription is
  recovered by *reading*, not by replay.

The consequence worth stating plainly: **the conversation is in the graph, not in the
client.** Who spoke is the sentex's own context and `:creator`; what was said is its
sentence. A client holds no conversation state a fresh reader could not reconstruct from the
KB.

## The deployment shape

Every write funnels through **one single writer**. In the cross-process case that writer is
the daemon ([operations.md](operations.md)), which serializes every assertion through one
monitor. This is not an incidental detail — three properties rest on it, and they are why
koinii ships no logical clocks:

The change-feed cursor delivers a **total order**: every agent reads the same events in the
same sequence, and a reply is a later write than the claim it answers, in the one order every
agent observes. So the happy path is **causally sound by construction** — a reply never
precedes its target in any agent's view. Lamport and vector clocks exist to *rebuild* a
causal order across concurrent writers; with one writer the store order already **is** the
causal order, so a timestamp would be a field nothing reads. (If koinii ever goes
multi-writer — several daemons over sharded KBs — that is when causal metadata becomes load
bearing. Until then it is ceremony. This is decision D7.)

The transport an agent coordinates over is the `Medium` protocol, with two implementations:

- **`wire`** — a daemon connection (`vaelii.client`). The inter-agent case: agents are
  separate processes funnelling every write through the one daemon, and a subscription runs
  the feed's poll loop **off** the agent's own thread. This matters because an in-process
  feed callback runs *on* the writer's thread ([feed.md](feed.md)); one slow agent would
  stall the writer for everyone. Polling off the agent's thread removes that coupling.
- **`local`** — an in-process KB. `subscribe` is a plain `watch` listener, no cursor
  apparatus. The callback runs on the writing thread, so a slow one still slows the writer —
  fine single-process, wrong across agents.

Everything above the protocol — `reply` / `assert` / `reply-many`, the recovery reads — runs
the same over either medium. Only `subscribe` differs, because only the feed does.

### When to stop

`local` is the right shape until the moment agents become **separate processes**. Then `wire`
is mandatory, and the reason is exactly the writer's thread above: separate processes cannot
share an in-process callback, and even if they could, one slow agent stalling the single
writer is a failure the whole deployment feels. The single-writer daemon plus the wire feed
is the shape that scales to N independent agents; the in-process medium is the shape that
keeps a single-process demo simple. Neither is a lesser version of the other — they are the
two honest answers to "is this one process or many," and the `Medium` protocol is the one
surface that lets everything else not care.

## Identity and the write boundary

The engine deliberately pushes per-caller identity *out*: `*creator*` is an unauthenticated
annotation and the daemon's only auth is one shared bearer token. Koinii's answer is the
context lattice, not a new auth subsystem (decision D8): the destination of an agent's writes
is a **deterministic function of its id** — `AgentAtlas` → `CxAtlas` (`identity/context-for`)
— so "write only your own context" needs no lookup, and a principal can never be routed to a
context that is not its own. The one context every governed agent may *not* write is the
admin-only registry `CxRegistry`: the governed may not write the authority that governs them.

The auth **strength** is conditional on policy (decision D4):

- **Cooperative** (the default) — `*creator*` trusted by convention, the write routed to the
  agent's own context. Correct for a notify-only deployment among trusted agents. State it
  plainly: identity here is **unverified** — `authenticate` trusts the claimed id with no
  proof, so it defends fat-fingers, not attackers.
- **Proof-tier** — required the moment trust-resolve is enabled, because trust-weighting a
  spoofable identity is worse than no trust. `authenticate` verifies a credential through the
  `verify-fn` seam (sign-at-ingest, an authenticating proxy, A2A AgentCards / DIDs) and
  **refuses** an unverified request; a nil verifier fails *closed*.

The registry itself carries three facts per agent — a membership mark (`agent`), a display
name (`displayNameOf`), and a **trust value** (`trustLevel`). Trust is a *mutable number*,
not a fixed rank (decision D3): an operator-assigned tier at bootstrap, overwritten by earned
reputation later. `trustLevel` is `functional`, so an update retracts the old value and
asserts the new rather than accumulating two. The number must support one constraint the
reputation math will later compute into — an endorsement is a trust signal only across
**distinct** principals, so homogeneous agents endorsing each other are discounted to one
signal — but here trust is only *stored*.

## Speech acts: reply is an assertion

The moves agents make are a small vocabulary in `CxSpeechActs` (decision D5). They split by
whether a move stands on its own or answers another:

- **Origination** (`asserts`, `queries`) — a plain assertion in the acting agent's own
  context. The claim, plus its provenance, **is** the act; nothing wraps it, because
  provenance already records who spoke. So `asserts` is documentary vocabulary, never minted
  — *an assertion in koinii is just an assertion*. A `queries` node **is** minted, because a
  question must be told apart from a claim.
- **Response** (`answers`, `disputes`, `endorses`, `justifies`) — a **meta-sentex on the
  target**, naming it by handle, asserted in the responder's own context and stamped with the
  responder as creator.

Two independent facts force the response shape, and together they are decision D1:

- **The cascade.** Each response predicate is declared `targetFollowingPredicate` in
  `CxSpeechActs`, so retracting a target sweeps its replies with it
  (`retract-following-metas!`). A bare assertion that merely *named* the target would outlive
  it as a dangling edge; a meta-sentex on the target does not. (The cascade needs *both* the
  meta-sentex and the mark — an unmarked meta merely orphans harmlessly.)
- **First-writer-wins.** Because provenance is first-writer-wins, an endorsement cannot be
  the endorser re-asserting the claim (that writes no new provenance) — it must be its own
  object with its own creator. So two endorsers of one claim are two distinct `endorses`
  sentexes, the case a bare re-assert would collapse to one.

```clojure
(def h  (ch/assert atlas '(usesDatabase ProdCluster Postgres)))
(ch/endorse boreas h)                    ; a distinct sentex, creator Boreas
(ch/answer  atlas "Postgres 16" query-h) ; (answers Atlas "Postgres 16" (sentexHandle query-h))
(ch/dispute cyra h)                       ; asserts ¬claim AND a disputes edge — the pair clashes
```

Idempotence falls out of sentence identity: re-asserting the same meta-sentex in the same
context moves no belief, so an at-least-once feed is safe to act on — replay a reply and the
KB is unchanged. The error acts (`notUnderstood`, `refuse`) name the received edge in the
refusing agent's context and are deliberately *unmarked*: a parse failure is a fact about the
exchange that should outlive whatever provoked it. Adjudication is a separate concern (below);
this layer only *represents* the moves.

## Disputes and adjudication

**"Disputed" is a precise word.** It is not "false" and not "defeated-by-strength." A dispute
is a *coexisting* clash — `S` and `¬S` both believed with no strength winner, so `argue`
returns `:contradiction` and the engine deliberately leaves both standing (paraconsistent
tolerance — [nmtms.md](nmtms.md)). A clean strength-defeat, a `:monotonic` premise beating a
`:default` one, is the **opposite**: the loser is `:defeated`, `argue` returns `:false`, and
that is *resolved*, not disputed. Two error classes are kept distinct and never merged:

- **`:contradiction`** — a coexisting `:default` dilemma (a rebuttal, or a definitional clash
  at equal strength). Both sides believed.
- **`:conflict`** — an irreducible clash among `:monotonic` content: two things asserted
  known-true that cannot both hold, which the engine has no grounds to prefer.

The engine represents contradiction but answers it only whole-KB; koinii adds the
**per-channel** view — "is there an open dispute *here*?" A dispute is observed by a context
exactly where it can read **both** clashing sides, up the `genlCx` cone. So a clash between
Atlas's `P` and Boreas's `¬P` surfaces in the channel that sees both agent contexts and *not*
in a sibling that sees only one — from a one-sided vantage there is no clash to see. The hot
path (`disputed?` on a named sentence) is a scoped `argue`, which never computes whole-KB
contradictions, so a subscriber may call it in a loop.

The **dispute lifecycle** is decision D9: `open → notified → resolved`, with a stale sweep for
the un-ruled. Two of the four states are *derived* from current belief (`:open`, `:resolved`)
and two are *stored* as ordinary assertions (`:notified`, `:stale`) — stored so `why` explains
them and retracting one reopens the dispute.

### Adjudication: split by policy

koinii's honest first answer to a disagreement is **not** to pick a winner. When two agents
assert `P` and `¬P` at `:default`, the KB stays paraconsistent — both coexist — and the layer
records the dispute, pushes it to whoever is watching, and manages its life. Three policies:

- **Leave-open-and-notify** *(the default)* — record open, notify, change no belief. Correct
  for a ground truth people curate. Notification fires **once per dispute**; the stored mark
  is the idempotency key, so a redelivery or a catch-up re-run does not re-push it. A stale
  sweep bounds the accumulation: an aged-out dispute is flagged `:stale` (still live — the
  clash still coexists) and re-surfaced to a human, never silently dropped.
- **Arbiter escalation** — a designated arbiter's ruling is an ordinary `:monotonic`
  assertion of the upheld side. Its strength defeats the losing `:default` side, so the clash
  clears, `why` explains who ruled, and — the point — **retracting the ruling reopens the
  dispute**, cascading through the JTMS. A ruling koinii could not undo would be a worse store
  than one that stays honestly disputed.
- **Majority vote** — a ballot is a meta-sentex on the disputed claim (`votesFor` /
  `votesAgainst`), knowledge like every other move, so `why` explains a decision as "the
  majority voted, here are the ballots." The decision reuses the arbiter's reversible
  monotonic assertion; the honest part is that **a tie upholds nothing** — an evenly-split
  house stays open rather than being decided by fiat, which is the whole reason to count
  instead of decree. A voter who cast both stances has *spoiled* their ballot, counted on
  neither side.

**Trust-resolve** — automatic resolution by source trust — is deliberately out of scope for
this layer; it is engine-side reputation work, and reaching for it here would resolve
disagreements by weighing spoofable identities.

An open dispute does **not** block dependent reasoning — the KB keeps deriving and both sides
stay believed. But a conclusion resting on a contested premise should be *visible as such*:
`contested-premises` / `rests-on-contested?` are pure reads that surface the risk without
hiding anything. The heavier option, `quarantine`, reversibly masks a contested claim from a
channel via `except` — off by default, because it over-suppresses (with the claim masked the
channel can no longer see the *dispute* either).

## Belief: what an agent holds

Reading what an agent *holds* is modal belief projection ([belief.md](belief.md)):
`(believes agent P)` proves `P` in the agent's **own** context, never the asker's. So agents
may hold contradictory beliefs without the KB contradicting itself, and asking what one agent
believes never pulls in another's. `believe-own` links an agent's belief context to its
koinii write context, so it believes what it asserted and endorsed.

The constructive complement is `convene`: create a spec (arbiter) context that sees several
agents' belief contexts, so their otherwise-isolated beliefs meet in one place and any `P`/`¬P`
among them surfaces as a contradiction (`disagreements`) ready for adjudication. Agent belief
contexts share no ancestor, so contradictory beliefs coexist silently until a common
descendant is convened on demand.

A boundary here matters. An agent may **disregard** its own statement — `disregard` puts an
`except` in the agent's own context, hiding the statement reversibly without deleting it — but
this is restricted to *own* statements by construction, and the restriction is the point.
`except` is an **index-layer** mask: it removes a sentex from *view*. Using it across agents
(B hiding A's claim) would make a common-descendant context unable to *argue*, because
argumentation needs both a claim and its rebuttal visible for the TMS to weigh them.
Cross-agent disagreement is therefore `dispute` / `argue`, which keeps both sides visible;
`except` is only ever an agent editing the visibility of what it *itself* said.

## Catch-up: snapshot + tail

An agent that was offline must catch up on what it missed — including the case the naive
version gets wrong. The feed's ring is bounded, so an agent gone long enough is **lagged past
recovery**: its stored cursor can no longer replay the gap. This is exactly the **CDC
snapshot+tail** pattern (Debezium, Kafka): a consumer that joined late — or fell too far
behind — re-reads current state (the *snapshot*), then resumes streaming from the newest
offset (the *tail*). Koinii's context re-read is the snapshot half. This is decision D6.

**The snapshot is authoritative, not a fallback nicety.** The change feed is add-oriented: it
reports a datum entering or a derived conclusion leaving belief, but a **premise retracted**
is dropped ([feed.md](feed.md)). So the incremental stream cannot, by itself, be a complete
replica — only a full re-read reflects retractions. The tail is an optimization for the common
case (koinii accretes — claims, replies, votes); the snapshot is the source of truth, and
every catch-up path ends reconciled against it or a live tail. When `poll` reports `:lagged`
non-zero, `sync!` re-reads rather than trusting a stream it knows is incomplete.

The cursor an agent keeps ("the last feed position I processed") is deliberately **client-side**
(decision D7). A cursor in a KB context would be self-describing, but it would write to the
shared truth on every poll — turning a read loop into a *write* loop through the single writer.
A deployment backs the `CursorStore` with a file, a KV row, or the agent's own store; the
in-memory atom is the default and the test seam.

Catch-up is **wire-only**: the ring, the cursor, and lag exist on the wire feed. An in-process
medium has no ring to fall off, so a single-process agent needs none of this and the
`-feed-open` / `-feed-poll` operations throw there.

## The other deployment shape: independent seats

The default topology is N agents funnelling writes through one daemon — the daemon *is* the
shared KB, and dereferencing a claim is a plain read. A second topology drops the shared
daemon: independent **seats**, each a separate process holding its own copy of the KB, stay in
sync by **content-addressed commits** rather than a live socket. A seat asserts and commits;
another seat pulls the same commit and resolves the same sentence *from its own KB*. The
locator travels over a transport; the proof comes from the KB; neither seat trusts the marker.
Complements the daemon, not rivals it: the daemon for live co-writing, seats for disconnected
or independently-replicated deployments.

Three ideas, each grounded on a primitive that ships:

- **The locator is content-addressed.** A handle is a number one store minted and does not
  travel; a locator is a self-describing `"sha256:"` digest over a sentex's **canonical
  identity** — its context, truth polarity, and canonicalized sentence
  ([canonicalization.md](canonicalization.md)). Two seats holding the same assertion compute
  the *same* locator, because `import!` re-canonicalizes every record through the reading
  build's own constructor. The digest input is an explicit type-tagged byte encoding, not
  `pr-str`: injective across the value space a sentence holds, and independent of ambient
  print vars, so a symbol never digests as the like-spelled string.
- **The commit is a Merkle function of state.** `commit-id` is an RFC-6962 Merkle root over
  the seat's *sorted* per-sentex leaf digests, domain-separated (`0x00` leaf, `0x01` node) so
  a leaf cannot be forged as an internal node. Order- and handle-independent by construction,
  because belief and storage are order-independent ([nmtms.md](nmtms.md)) — so two seats that
  reached the same set of assertions by different routes compute the same commit id. The tree
  shape buys pure auditability: `inclusion-proof` yields an audit path and `verify-inclusion`
  recomputes the root from just a `(locator, proof)` pair, with **no KB**. (`commit-id`
  fingerprints *knowledge*; `state-root` folds provenance in for a git-commit-like *snapshot*
  identity that moves when who/when moves.)
- **The marker is untrusted.** `dereference` finds the sentence in the seat's own KB and
  rehashes what it found; a stale or tampered marker fails that check and is rejected, and a
  marker the seat cannot resolve means the commit was not received — never that the payload
  should be believed. Attribution is trustworthy only as far as the identity model above makes
  it: a distributed KB inherits the same cooperative-vs-proof-tier question.

## Design decisions

The koinii modules cite these by number. Each is a choice to reuse a core mechanism over
adding one, or to keep an honest limit over a convenient fiction.

| | Decision | Why |
|---|---|---|
| **D1** | A reply is a meta-sentex on its target | The `targetFollowingPredicate` cascade tears replies down with the target; first-writer-wins forces each act to be its own creator-stamped object. |
| **D3** | Trust is a mutable number, not a fixed rank | An operator tier at bootstrap, overwritten by earned reputation; `functional`, so an update retracts-then-asserts rather than accumulating. |
| **D4** | Identity strength is conditional on policy | Cooperative (trusted by convention) for notify-only; proof-tier (a verified credential, fail-closed) required once trust-resolve is on. |
| **D5** | Moves are knowledge, not messages | A speech act is a sentex — queryable, retractable, auditable — so the conversation lives in the graph, not the client. |
| **D6** | Catch-up is CDC snapshot + tail | The feed drops retracted premises, so it cannot be a complete replica; a full re-read is authoritative, the tail an optimization. |
| **D7** | Single-writer total order; client-side cursor | Store order already *is* causal order, so logical clocks are redundant; a KB-side cursor would turn every poll into a write. |
| **D8** | An agent writes only its own context | The write destination is a deterministic function of the authenticated id, so "write your own context" needs no separate check. |
| **D9** | A four-state dispute lifecycle | `open`/`resolved` derived from belief, `notified`/`stale` stored so `why` explains them and a retract reopens the dispute. |

## Where it lives

Every module is additive over the public core API; nothing in core loads any of them.

- `vaelii.impl.koinii.identity` — per-agent contexts, the write boundary, the admin registry,
  the `authenticate` seam. KB: `resources/kb/koinii/CxRegistry.txt`.
- `vaelii.impl.koinii.speech-acts` — the `CxSpeechActs` vocabulary and the origination /
  response acts. KB: `resources/kb/koinii/CxSpeechActs.txt`.
- `vaelii.impl.koinii.channel` — the coordination library: the `Medium` protocol (`wire` /
  `local`), `join` / `assert` / `reply` / `subscribe` / `reply-many`, and the recovery reads.
- `vaelii.impl.koinii.dispute` — the per-channel dispute reads and the lifecycle vocabulary.
- `vaelii.impl.koinii.adjudication` — the leave-open / arbiter / majority policies, the notify
  and stale sweeps, and the contested-premise reads.
- `vaelii.impl.koinii.belief` — belief projection, `convene` / `disagreements`, and
  own-statement `disregard`.
- `vaelii.impl.koinii.catchup` — the CDC snapshot+tail consumer and the client-side
  `CursorStore`.
- `vaelii.impl.koinii.deref` — the independent-seat topology: content-addressed locators,
  Merkle commits, and untrusted-marker dereference.

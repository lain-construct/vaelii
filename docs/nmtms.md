# Non-monotonic truth maintenance

- **Covers:** how belief is computed from justification strength, and how `settle`
  resolves soft contradictions without throwing.
- **Not here:** the belief a batch would move before it commits →
  [preview.md](preview.md); the ASP backend a contested edge renders to →
  [asp.md](asp.md).
- **Assumes:** sentex, context, justification, strength → [glossary.md](glossary.md).

`vaelii.impl.strength`, `vaelii.impl.solve`, `vaelii.impl.jtms`, and the settle layer in
`vaelii.impl.settle`.

A plain JTMS is a *monotone* least fixpoint: adding a belief can only turn nodes IN.
Defeasible common sense needs the opposite too — a new fact can *withdraw* an earlier
conclusion. This is the non-monotonic layer. Its design is
shaped by one observation:

> Most of a common-sense KB is default-true with no conflict. Only the **edges** —
> where defaults collide — need real arbitration. So resolve the easy majority in
> the engine, and hand only the contested edges to an external solver. Known-true
> content is never sent to a solver.

## Strengths and the defeat-class (`vaelii.impl.strength`)

Every assertion carries an assumption **strength**:

| Strength | Meaning | Defeasible? | Sent to solver? |
|----------|---------|-------------|-----------------|
| `:monotonic` | known-true | never | never |
| `:default` | defeasible (the common case) | yes | yes, at a tie |

Assert monotonic content with `(assert kb S ctx {:strength :monotonic})`; the
default is `:default`, because most of the KB is.

There are exactly **two** classes, and derivation adds none. They form a total order
**monotonic > default**. A node's **defeat-class** is the strongest support it
currently has: its premise strength, or the class any valid justification *confers*
on it. `relabel` computes it alongside the label; `core/defeat-class` (via
`jtms/defeat-class`) reads a believed handle's class back.

**Do not add a third.** The one problem that tempts an intermediate class — letting
`penguin ⇒ ¬flies` outrank the default `bird ⇒ flies` without the penguin fact having
to be known-true — is [`exceptWhen`](exceptions.md)'s: a rule states its own exception
and does not fire, so nothing needs to out-rank anything. A class between the two buys
one case and costs the total order everywhere else.

### Strength propagates from the antecedents

A justification confers **`min(its own strength, the weakest of its antecedents'
classes)`**, where a rule's own strength is read off its defeasibility:

- a **bare rule** confers `:monotonic` — it adds no defeasibility of its own, so the
  conclusion is capped by whatever it rests on;
- a **`set/defaultRule`** confers `:default` — it introduces defeasibility, so its
  conclusions are always `:default`.

A conclusion can therefore be no stronger than the weakest thing it rests on: a bare
rule over a merely-default premise concludes a *default*. The same bare rule over
known-true facts concludes `:monotonic`, which is correct — it *is* monotonically
entailed. Without the cap, a rule launders a default into something a
directly-asserted default cannot contradict: a conclusion carrying more authority than
any of its grounds.

The **informant is excluded from the cap**. A rule is one of its own justification's
antecedents — that is what makes retracting or defeating the rule withdraw everything
it licensed — but that is a *validity* role, not a ground. Since `assert` gives a rule
`:default` like anything else, capping on it too would put every derived datum at
`:default`.

This makes the class equation **recursive**: a node's class depends on its
antecedents' classes. `jtms/region-classes` solves it as a **least fixpoint inside
the region relabel**, so locality is untouched:

- every in-region IN node starts at `:default`, the bottom of the lattice;
- antecedents outside the region are boundary — their stored class is read and held
  fixed, exactly as their labels are (a boundary node whose class could move would
  have an antecedent in the region, and would therefore be in the region);
- iterate to stability with a **semi-naive worklist** — a node's class is recomputed
  only when one of its antecedents' classes moves (reached through `:consequences`), so
  the cost is O(region edges) rather than O(region depth × region).

The operator is monotone in the class lattice and the iteration starts at bottom, so
it converges to the *least* fixpoint — which is unique, and therefore independent of
visit order (and of the worklist's own visit order) and of the order the knowledge
arrived in. A single pass would be wrong
in a way that looks fine: visited one way it reads a not-yet-computed antecedent as
bottom and under-rates the conclusion, visited the other it reads a stale value and
over-rates it.

## Two invariants

Everything below is in service of these. They are not negotiable, and they pull
against each other, which is what makes the design interesting.

### 1. Order independence

**The same knowledge, given in any order, yields the same beliefs.** A common-sense
KB learns generalities and specifics in whatever order the world supplies them —
"birds fly" before or after "Tweety is a penguin" — and an engine whose answers
depend on that order is answering a question nobody asked.

Belief is therefore *computed from current state*, never accumulated as events
arrive. The subtle leak is **tie-breaks**: when two beliefs are equally strong,
something has to choose, and choosing by handle id smuggles arrival order back in,
because handles are allocated in assertion order. The Nixon diamond is where that
shows: keyed on a handle it elects the pacifist or the non-pacifist according to
which was typed first. Tie-breaks key on **content** instead (`solve/content-key`): what a sentex
says is the same whenever it is asserted. The choice stays arbitrary — two
equally-specific defaults give no principled winner — but arbitrary *and stable* is
the contract; arbitrary and order-dependent is a bug.

`test/vaelii/order_independence_test.clj` enumerates every permutation of each
scenario and demands a single distinct outcome. Note that the weaker assertion —
"exactly one side wins" — is true under every order *even when the winner flips*, so
it passes against an order-dependent engine. Asserting the **same** side every time is
what catches it.

### 2. Locality

**No operation recomputes the whole graph.** A change can only affect what is
downstream of it, so every relabel is scoped to the **affected region** — the
forward consequence closure of whatever changed — with the rest of the graph held
fixed as a boundary. Cost is proportional to the region, not to the size of the KB.

The reconciliation with invariant 1 is the crux: a least fixpoint over the region
with boundary labels fixed has a **unique** solution, and it is the same one a
global fixpoint would produce. Uniqueness is why locality costs no order
independence — there is nothing for a visit order to influence. Well-foundedness
survives too: the region starts with nothing believed inside it and only ever adds,
so a support cycle within the region that has no ground outside it never enters,
exactly as in the global computation.

The region is also **the answer to a question callers ask**, which is why `settle`
publishes it rather than discarding it. Three readers want the same thing — a
consequence preview, a consequence report, and a change feed
([preview.md](preview.md), [feed.md](feed.md)) — and each of them would otherwise diff
the believed set, which is O(KB) per write and flat in nothing. `settle-finish` decides
once what the settle moved (the relabelled regions plus the flips no relabel records)
and hands that one answer to all three.

The question those readers ask is a shade larger than "whose belief flipped": it is
*what I published about this datum may be out of date*. So `touched` also collects the
handles a **redundant justification** landed on — the one entry whose belief provably did
not move (see "The reports are rebuilt only where the region moved"). Every consumer
reads it as a superset, so an extra handle costs a re-derivation and never an answer.

Measured, on an in-memory graph of N premise→conclusion pairs (no store in the way).
Each cell is a whole-graph relabel against the region-scoped one, so the pair reads as
what locality is worth at that size:

| nodes | `add-justification` | `defeat` | `clear-defeats!` | `sweep!` (2 nodes) |
|-------|--------------------|----------|------------------|--------------------|
| 500   | 762µs / **18µs**   | 3063µs / **9µs** | 2792µs / **2µs** | 153µs / **38µs** |
| 1000  | 1297µs / **20µs**  | 5639µs / **9µs** | 4607µs / **2µs** | 339µs / **40µs** |
| 2000  | 2107µs / **20µs**  | 8245µs / **9µs** | 8074µs / **1µs** | 540µs / **41µs** |
| 4000  | 4006µs / **20µs**  | 16946µs / **8µs** | 15946µs / **1µs** | 1189µs / **48µs** |
| 8000  | —                  | —                | —                | 2536µs / **40µs** |
| 16000 | —                  | —                | —                | 5636µs / **46µs** |

The `sweep!` column collects a fixed two-node chain out of a graph of N
premise→conclusion pairs, so the region is the same size at every N and only the
background grows. A whole-graph relabel therefore tracks the background exactly, which
is what the left-hand figure shows.

The whole-graph column grows linearly with the graph; the region-scoped one is flat.
That is the whole point — the gap widens without bound, so locality is an asymptotic
property rather than a constant factor. At present KB sizes it is invisible end-to-end:
a single `assert` is dominated by fixed per-assert overhead, not this join. It is a
claim about what happens at a million facts, not at a thousand.

**The invariant is a claim about every representation, and the table above only tests
one.** These numbers are the reference network, whose persistent maps are region-local
by construction. The dense one holds belief in `RoaringBitmap`s, where any operation
that rebuilds a bitmap costs one pass over all of its 65,536-value containers — so it
satisfied locality up to 65,536 nodes, where there is exactly one container, and
silently violated it above. At 16,000 nodes, the largest graph measured here, nothing
could have shown it; it took a rebuild over nine million premises. See
[density.md](density.md), Phase 3. Whatever else a second representation must be proven
to match, **cost shape is part of it** — the dense oracle compares answers, and answers
were never wrong.

## The TMS (`vaelii.impl.jtms`)

Belief is a least fixpoint, recomputed region-locally rather than accumulated:

- **`:in`** is the believed set and the sole authority on belief — nodes carry no
  label of their own, so there is no second copy to drift. **`:groundable`** is what
  is *structurally* derivable ignoring defeats; a defeated node that is still
  groundable can revive, one that is not has lost its last derivation and is swept.
  Both are maintained region-locally by the same fixpoint.
- `affected-region` — the forward consequence closure of whatever changed. A node's
  label is a function of its justifications' antecedents, so a node whose label can
  move is by construction reachable from what moved; everything else is boundary and
  is never even looked at.
- `relabel-region*` — the localized least fixpoint. Also recomputes defeat-classes,
  but only inside the region: a boundary node whose class could move would have an
  antecedent in the region, and would therefore be in the region.
- `defeat` seeds the region with the newly-defeated datums; `clear-defeats!` seeds it
  with the *previously* defeated ones, so a settle that defeated nothing last round
  does no work at all.
- `set-blocked` seeds it with the **consequences of the justifications whose blocked
  status moved** — the ones blocked in both the old and the new set are already
  accounted for in the current labels, so a call that changes nothing does no work at
  all.
- the **sweep** (`sweep!`, and `retract!`'s tail) is region-local in the same way: the
  justifications to tear down are read off the dead nodes' own `:supports` /
  `:consequences`, never found by scanning the justification map. `exceptWhen` makes
  sweeping routine rather than a retraction-only path — a blocked justification leaves
  its conclusion ungroundable and the sweep collects it on ordinary fact arrival — so
  a sweep that scanned the whole graph would make a run of them quadratic.
- `relabel` (the whole-graph version) survives for exactly one caller: `recover`,
  which rebuilds the network from the durable store and so has no smaller region to
  start from. Nothing on the assert / retract / settle path calls it.

### Two representations of the same network

The network is always resident, which makes it a scale wall of its own (measured ~467
B/node — see [density.md](density.md#phase-3--the-dense-truth-maintenance-network-tms-dense)),
so it sits behind a `Tms` protocol with two implementations, chosen by `open-kb`'s
`:tms`:

| `:tms` | the graph is | |
|---|---|---|
| `:reference` (default) | one atom over one persistent map | readers get a consistent snapshot from a single deref |
| `:dense` | bitmaps + primitive-keyed maps, and no justification object at all | 5.5× denser on a fact corpus, 3.3× on a rules-heavy one |

**The seam is the representation, not the algorithm.** Both run the same least fixpoint
over the same affected region, because that is the semantics of belief here and not an
implementation detail; what differs is where a node's premise flag, depth and adjacency
live. `jtms_dense_oracle_test` compares the two in full after every step of randomized
operation streams, and `VAELII_TEST_TMS=dense lein test` runs the whole engine through
the dense one.

**The network keeps the graph; the record store keeps the record.** A justification is
stored durably, and belief reads only part of it — the antecedents, the `:out` list, the
consequence, the strength and the informant. The firing's **variable bindings** are no
part of that: they are read only to re-evaluate an `exceptWhen` query or a NAF antecedent
per firing, and both readers hold the KB and take the record from the store. So
`jtms/graph-just` projects a justification on the way in, and neither representation
holds a second copy of one. `core/justification` and its two neighbours read the store
for the same reason — a justification *is* a record, and a record's home is the store.
(The projection also normalizes, which is what makes the two representations store values
equal to each other's however a caller spelled the justification.)

Two properties are worth stating because they are easy to assume and would be wrong:

- **A dense network cannot simply replace the reference.** `RoaringBitmap` is mutable,
  and `jtms_atomicity_test` pins that a mutation applies all-or-nothing — a mutable
  bitmap inside that value would break `swap!`'s retry and let a reader observe a
  half-applied relabel. Hence two implementations rather than one, and hence the dense
  one serializes writers on a monitor and leaves readers unlocked, which is the latitude
  the one-writer contract already grants (docs/storage.md).
- **Order independence rests on the backward dependency and the forward propagation
  being the same edge set.** The class fixpoint re-examines a node when something it
  derives from moves, reached through `:consequences`. If a justification id were ever
  rebound to a different justification, a node's `:supports` would name a justification
  that now concludes elsewhere, and its class would depend on a value the propagation
  can never carry to it — at which point the answer depends on visit order, in *either*
  implementation. `p/next-id` is monotonic, so the engine cannot construct that state.

### Blocked justifications (`exceptWhen`)

`:blocked` is a set of **justification ids** whose rule's exception currently holds,
and `valid?` reads it alongside its antecedent and `:out` checks. The TMS is pure and
has no KB, so it cannot run the level-6 exception query itself: the caller evaluates
the exception and hands the answer in with `set-blocked`, which *replaces* the set
rather than accumulating it — the same discipline as the defeated set, and the reason
blocking cannot smuggle arrival order into belief.

Blocking is **not** defeat. A defeated *datum* is forced OUT but keeps its support and
stays `groundable`, so it can revive. A blocked *justification* is simply invalid: it
supports nothing, confers no defeat-class (`node-class` never reads a blocked
justification's strength), and does not make its consequence groundable — which is
what lets the ordinary retraction sweep garbage-collect an excepted conclusion instead
of retaining it. See [exceptions.md](exceptions.md), "Garbage collection, not defeat".

**Recovery starts unblocked.** Nothing about an exception is stored, so the blocked set
cannot be read back from the durable store — `relabel` therefore *clears* it before
rebuilding. Merging into whatever was there could only ever add, leaving a block
standing for a justification whose exception no longer holds (the bug
[taxonomy.md](taxonomy.md) records for the transitive closures). The window between
the rebuild and the caller's re-evaluation believes an excepted conclusion; the next
settle withdraws it. `retract!` prunes the blocked set of swept justification ids for
the same reason: a stale id must not survive to be reapplied.

Both premises and justifications carry a **strength**: a premise its assumption strength
(on the sentex record), a `Justification` a `strength` field (the defeat-class it
confers) alongside an `out` slot (reserved for negation-as-failure antecedents; empty
today — NAF is built, as `unknown` / `thereExists`, but by re-evaluation rather than
the out-list, see [naf.md](naf.md)).

**Retraction** is dependency-directed, expressed as relabel-then-sweep: drop the
premise, relabel, and in the retracted datum's consequence-closure delete any datum
that ends OUT with no valid support (solely supported by the retraction) — while a
merely *defeated* datum keeps its support and is retained for revival.
Alternate-witness derivations survive; solely-supported ones are swept.

The closure it marks **is** the region it relabels, so marking and relabelling walk
the graph once between them, and the groundability the sweep consults is the
`:groundable` set that relabel just recomputed rather than a second whole-graph
fixpoint of its own.

`suspend-premise` is the first two steps without the third: drop the premise, relabel
the region, sweep nothing. It is a retraction's whole effect on **belief**, because the
sweep never moves a label — it collects datums that are already OUT and ungroundable.
That makes it the one *reversible* retraction: `add-premise` at the same strength puts
it back, at the same handles, with every justification still where it was.
`core/preview` is the caller ([preview.md](preview.md)).

**Belief-sensitive reads.** A defeated default stays *stored* (for revival) but is
not *believed*. So matching is belief-sensitive: `res/raw-match`, `core/sentexes-matching`,
and `core/types-of` skip handles that are currently OUT. Raw introspection
(`core/sentex`, `find-sentexes`, the web browser) still sees everything.

## Soft, prioritized contradictions (the settle layer)

`assert` does not throw on `S` vs `(not S)`. Instead `settle` runs after every
assert / retract / `forward-chain` / `recover`:

1. `clear-defeats!` then `relabel` — fresh labels and classes; previously-defeated
   defaults tentatively return so revival can happen.
2. Find the active **nogoods** — sets of believed sentexes that cannot all hold.
   Two sources:
   - every believed `(not X)` paired with a believed `X` **when some context sees
     both** (`negation-nogoods`), asked each round;

     Two narrowings, and they answer different halves. **Which bodies could pair at
     all** is the `:opposed` coincidence set — the bodies stored in *both* polarities,
     maintained O(1) at the store and removal choke points — so a KB with no
     contradiction does one emptiness read and a negation-heavy load never scans its own
     negations. **What each of those bodies pairs** is memoized per body: a settle
     re-derives only the bodies it could have moved and carries the rest, since
     otherwise every standing contradiction pays two belief-filtered queries and a cross
     product on every round, which is quadratic in the contradictions a load creates for
     exactly the reason the definitional pairs below are (measured at 56ms an assert
     against 7.5ms, at 1600 standing dilemmas).

     Three things move a body's pairing and no one of them sees the other two: a
     relabel (`jtms/touched` — a revival with no store behind it), a store or a removal
     (`kb/note-opposed!` — and a removal is the case only this covers, since the record
     is gone before a settle could ask the handle what body it was about), and a
     `genlContext` edge (which can make standing pairs jointly visible without going
     near either side, so its generation retires the memo whole).
   - the **definitional clashes** — disjointness, functionality, asymmetry — each of
     which convicts by naming a second believed sentex, which is a nogood in exactly
     the same sense (`constraint-nogoods`). Discovered by re-running the checks over
     the settle's moved region, so a pair is a function of current belief rather than
     an accumulation, and priority sits **above** every rebuttal: these rank 3–4 where
     a rebuttal ranks 1–2.

     A pair whose members did not move, under a vocabulary of separations and predicate
     properties that did not move either, has its answer **carried forward** — a memo on
     the recomputation, since the carried value is exactly what re-deriving would give.
     That is not an optimization to taste: a settle runs after every mutation, so one
     check per standing pair per settle is quadratic in the clashes a load creates
     (measured at 36ms an assert against 8ms, at 300 standing clashes).

   The argument constraints (`argIsa` / `argGenl` / `interArgIsa`) are deliberately
   *not* here. One is convicted by the **absence** of a path from the argument's types to
   the constraint type — an open-world negation-as-failure judgement — so there is no
   second sentex to weigh it against and nothing for a defeat class to compare. Those
   stay refusals, and on the derivation path stay drops.

   **`arity` is not here either, for a different reason worth knowing.** It *does* name a
   second believed sentex — the `(arity P n)` declaration — and is still not a nogood,
   because that sentex is the **vocabulary entry the conviction is read through**:
   `declared-arity` answers from a cache that follows belief, so a nogood defeating the
   declaration destroys its own premise, and the clash is decided once and then re-derived
   by nobody. So its retroactive half reports instead
   ([taxonomy.md](taxonomy.md#what-each-constraint-does-in-each-arrival-order) has the
   measurement). The rule it generalizes to: **a nogood whose detection reads a
   belief-following cache its own member supports is not stable.**
3. Resolve each nogood from its members' **defeat-classes** (`decide-nogood`):
   - **different defeat-class** → defeat the strictly-weaker member. No solver.
     (Monotonic beats default.)
   - **equal, and defeasible** → a **dilemma**. Both sides stay believed at
     `:default` and the pair is reported by `contradictions`. Nothing is arbitrated.
   - **equal `:monotonic`** → irreducible; report it in `conflicts` (never throw).
4. Loop until no active nogood remains.

A default/default clash is **not** decided, and defeat-class is the only axis it could
be decided on (see *There is no second axis*). Where one rule names the other's case,
[`exceptWhen`](exceptions.md) settles it structurally — the general rule states its own
exception, never fires, and produces no contradiction to arbitrate. Where neither names
the other's case (the Nixon diamond) the clash is a genuine dilemma, and the engine
represents it rather than picking a side.

The solver seam below therefore has no caller on the negation path. It is kept because
`set-solver` is public and because arbitration is still the right answer for nogoods
that are not plain rebuttals.

### Which door the content came through

One logical situation, one representation: the nogood above, however the content
arrived. The line between refusing and arbitrating is read off the **opposing claim's
defeat class** — the line `checks/asymmetry-problem` draws — and not off which path the
content came in on:

| where the clash arrives | opposing `:monotonic` | opposing `:default` |
|---|---|---|
| a **rule firing** (`place-conclusion`) | placed, then defeated — the loser has a `why-not` | placed; a represented dilemma |
| an **`assert`**, asymmetry | refused | admitted; a represented dilemma |
| an **`assert`**, disjointness / functionality | refused | refused, unless the KB arbitrates |

A firing has no caller to refuse, so there the choice is between dropping the
conclusion — no sentex, no justification, and `why-not` reduced to `:not-stored` — and
placing it for `settle` to weigh. Placing it is what gives the loser a reason, so that
is unconditional. Whether a *writer* is told no is a different question, a policy of
the application rather than of the engine, and it is answered per KB by `open-kb`'s
**`:constraints`** — `:refuse` (the default) has `assert` refuse a disjoint or functional
clash at any strength, `:arbitrate` refuses only against known-true content. A KB naming
neither reads the process default `checks/*arbitrate-constraints?*`
(`VAELII_ARBITRATE_CONSTRAINTS=1`), which is what lets a whole suite run under one
policy; `checks/arbitrating?` is the one read of both.

The policy governs the **retroactive** half too, and that is where it is felt: a
declaration arriving *after* the content it convicts is what an import routinely does,
and under `:refuse` the clash is filed by the exposure pass (`violations`) while both
sides stay believed, even though the same fact asserted one line later would be refused.
Under `:arbitrate` the declaration reaches back (`settle/declaration-implicates`) and the
weaker side is defeated, so belief does not depend on whether the schema or the facts
arrived first. Which sentences count as a declaration for that purpose is
[taxonomy.md](taxonomy.md); the one worth knowing here is that a term **joining** a
disjoint metatype is one of them, and is the only one the taxonomy rather than the
sentence identifies.

**One retroactive half is not policy at all**, and it is the exception that says what the
policy is about. `(functional P)` arriving after two symbol values for the same first
argument does not convict either of them — it *merges* them, which is an inference rather
than a refusal, so `special/equate-existing` runs it under both policies exactly as
`derive-functional-equalities` runs the same inference on the arriving fact
([equality.md](equality.md)). What `:refuse` and `:arbitrate` decide is whether a writer
is told no, and nobody is being told no here.

Three paths that *mint* content keep refusing either way, because each has somewhere
else to be and nothing to stand behind: the decontextualization lift's copy, the
equality migration's twin, and the gate on what `abduce` may assume
(`checks/constraint-violation`).

### Which contexts can contradict each other

Two beliefs clash when **some context sees both** — i.e. their contexts have a
non-empty common down-closure (`tax/maximal-common-descendant-contexts`). Asking only
whether one context `sees?` the other is too weak: it catches a *comparable* pair and
nothing else, silently exempting every sibling pair from contradiction detection. Two
incomparable contexts can share a descendant, and from that descendant `X` and
`(not X)` are both visible, so the clash is real there.

The common-descendant test strictly generalises `sees?` (if K sees Y then K is itself
a common descendant of the two), so it detects everything `sees?` would. The pair test
is **memoized per pass**: the nogood scan is already quadratic in the believed
negations, and computing a maximal-common-descendant set per pair would turn that into
a real cost. Contexts are few and repeat constantly, so the memo collapses it to one
computation per distinct pair.

A **definitional** clash reads the same rule from the other end. `X` against `(not X)`
needs no vocabulary to be a contradiction, so the pairing is the whole question; a
disjointness needs the separation and the genl edges it closes under to be visible too,
which is a scoped check rather than a set test. So the common descendant is where that
check is *asked from* (`settle/clash-askers`) rather than a predicate over an already
formed pair — the same answer to the same question, reached by running the check where
both halves can be seen.

### There is no second axis

Defeat-class alone cannot separate "birds fly" from "penguins do not" — both are
defaults, and since strength propagates the exception cannot buy rank from its rule
either. The tempting second axis is a **specificity heuristic**: score a type by the
size of its reflexive-transitive genl up-closure, a rule by the greatest such score
among its antecedent predicates, a datum by the greatest of those among its valid
justifications, and on a tie in class let the more specific member win.

Do not build it. `exceptWhen` makes the relation such a heuristic can only reconstruct
explicit: the exception is stated *on* the rule it excepts, so the general rule does not
fire and there is no tie to break. Deriving an ordering from the genl hierarchy is
inference *about* the knowledge rather than *from* it — it works when the exception
happens to be keyed on a narrower type and silently ties when it is not, so whether it
applies depends on how the ontology was written rather than on what it says.

There is a single axis, defeat-class, and a default/default clash it cannot separate is
reported as a dilemma rather than decided.

### Definitional constraints on the derivation path

argIsa types, disjointness and functionality hold of *derived* content as much as of
asserted content. A rule that concludes `(cat Rex)` where `(dog Rex)` is believed and
the two are declared disjoint has concluded something the KB says cannot be, so a check
that runs on only one path lets a rule quietly produce what `assert` refuses.

`chain/place-conclusion` runs the same three checks `assert` does, and **does not
throw**: chaining is a fixpoint and cannot abort halfway through one without making
the resulting belief set depend on which rule fired first, and the engine's stance is
that contradictions are soft. A failing conclusion is *dropped* — no sentex, no
justification, nothing believed — logged at `:warn`, and recorded in
`(core/violations kb)` as
`{:violation :arg-type|:disjoint|:functional :sentence :context :rule :detail}`.
Two more kinds ride the same path: a completed firing with **no placement context**
is recorded as `:no-placement`, and a *derived* `genl`/`genlContext` edge that would
close a cycle through negation is dropped and recorded as `:not-stratified`.

`(core/violations kb)` is an **accumulating** ledger, not a per-run snapshot. Each
entry carries the run id from `(core/chain-stats kb)`, the ledger is capped at the
newest 1000 entries, and it is emptied only by `(core/clear-violations! kb)` — never
auto-cleared per run. So a bulk load's drops all survive to the end instead of being
erased by the next assert.

The checks run only when the conclusion is **new** to its context. Re-deriving a
sentence already stored there adds a justification, not content — whatever it says was
admissible when it was first placed — so a second derivation cannot introduce a
violation that was not already there. That is load-bearing, not a micro-optimization:
`checks/args-problem` reads the memberships of every constrained argument — a posting
read, a record fetch and a belief test per type the term holds — and forward chaining
re-derives the same conclusion on every round of every defaults pass. Checking per
firing rather than per new conclusion made the starter's load ten times slower.

Dropping is what happens to a violation with **no opposing sentex** — an argument
constraint, an arity, a malformed special predicate, an unstratified derived edge.
A disjointness, functionality or asymmetry clash names a second believed sentex, so
it is not dropped at all: the conclusion is placed and this same settle layer
arbitrates the pair, defeating whichever side is weaker rather than discarding the
newcomer. So `violations` is the ledger of what genuinely cannot be represented, and
a contested conclusion is found in `contradictions` or `conflicts` instead.

The loop terminates because the defeated set grows monotonically and each defeat
turns a member OUT, deactivating its nogood.

### What a solve returns

Contradictions never *fail* a solve. The result is the set of nogoods the solver
could not satisfy — an irreducible clash among known-true beliefs. Their
`(contradicts X Y)` sentences are the reported result, read back with
`(core/conflicts kb)`. An arbitrated tie is **not** a conflict (the solver chose a
consistent side); only genuinely unsatisfiable contradictions are reported.

### A clash is reported, never stored

`(contradicts X Y)` is a **report form**, not a sentex. Nothing asserts it, no handle
resolves to it, and `(sentexes-matching kb '(contradicts ?a ?b) '?ctx)` is empty however many
clashes the KB holds — `resources/kb/CoreContext.txt` says as much of the predicate
itself, and `constraint_nogood_test` holds the engine to it, since the report *reads*
like a sentence and the mistake would otherwise be invisible.

Two reasons it stays a value. Stored, it would be a premise needing truth maintenance
of its own — a claim about beliefs, inside the machinery that computes belief. And it
would go stale the moment either side moved, where a report recomputed each settle
cannot: belief is computed from current state, and so is everything said about it.

`conflicts` and `contradictions` report the **same entry shape**, down to `:kind` and
both sides' justifications:

```clojure
{:nogood #{h1 h2} :handles [h1 h2] :priority int :kind kw-or-nil
 :sentence (contradicts X Y)
 :sides [{:handle :sentence :context :defeat-class :justifications [...]} ...]}
```

The two differ in *why* the pair was left standing — a defeasible tie the engine
declines to break, or a known-true clash it has no grounds to break — not in what a
caller needs in order to act on one. The known-true case is where the engine has
declined hardest and the application has the most to do, so giving it less material
than the easier case had it backwards.

**`:sides` and `:handles` name the pair in content order**, the same rule the sentence
inside `(contradicts X Y)` follows, and it is the tie-break invariant reaching the
reading a caller actually holds. A nogood is a *set*, so something has to linearize it;
sorting by handle is the tempting answer and it is the one that fails, because handles
are allocated in assertion order — "which side is `(first (:sides c))`?" would then mean
"which side was typed first", on a report whose `:sentence` said the same thing either
way. So the sides are ordered by printed sentence, then by context (one sentence can
clash with itself across two contexts), then by handle for a pair a reader cannot
tell apart regardless. `:handles` is `:sides`' handles in that order, so the two agree.

**The list is ordered by the same rule the sides are.** Ordering the pair inside a report
and leaving the vector of reports unordered would move the problem out one level rather
than solve it: the nogoods are held in a hash set keyed by handle, so
`(first (contradictions kb))` would be an answer about which pair was typed first, on a
call whose every other reading is order-independent. Both vectors sort by printed
sentence, then context, then handle — the sides' rule applied to the reports — and the
sort key rides each report's metadata, so a settle computes it once rather than once per
comparison. That last part is not a micro-optimization: recomputing the key inside the
comparator is a 60x regression on `lein perf`'s `clash-arbitration` check, which is what
holds it.

### The reports are rebuilt only where the region moved

A report is a function of its two handles — their sentences, their contexts, their
defeat classes, and the justifications supporting them — plus the three fields the
nogood itself carries (`:priority`, `:kind`, `:sentence`). So a pair the settle's region
does not hold has the report it had last settle, and `record-clashes!` carries it
forward; the memo holds what is *standing now*, rebuilt from each settle's own answer,
so it cannot accumulate. This matters because the readings are republished on every
settle and a settle follows every mutation: rebuilding all of them is a per-assert cost
proportional to how many clashes are standing, which is the defaults phase's shape in a
new place. `lein perf`'s `clash-arbitration` check is the gate: across a **32x** rise in
standing clashes an assert costs 9.5x more with both memos, 12.3x with this one removed,
and 46.5x with the carry-forward removed as well — 2.0µs of bookkeeping per standing
pair against 29µs to re-derive one.

That carry is only sound because the region covers every input to a report, and one of
them is not belief. A **redundant justification** — a second derivation of an
already-believed conclusion, conferring no stronger a defeat class — is the write the
JTMS deliberately declines to relabel for: that fast path is what collapses a recursive
forward load from O(derived²) to O(derived), since an already-IN node feeds its
consequences identically on one witness or two. Belief does not move, so no label does;
what moves is the *reason*, and in a dilemma the engine declines to decide the reasons
are the whole answer a caller is given. So `add-just*` notes the consequence as touched
even on the fast path — O(1) at the write, where asking every standing pair for its
support count at report time is O(standing) per settle: `negation-arbitration`'s growth
ratio was 19% worse for the polling route and unmoved by this one, at 800 standing
dilemmas. `touched-in` takes it too, or the window would read as "newly
believed" to `preview` and the change feed. The general shape: **the window means "what
I published about this datum may be out of date", which is a slightly larger question
than "did its belief flip"** — and every consumer reads a superset, so an extra handle
costs a re-derivation and never an answer.

Ω(standing) per settle is inherent, though, and no memo removes it: the readings *are*
the whole standing set, so publishing them costs what they are. What the memo buys is
that the per-pair term stays bookkeeping rather than a re-derivation of the checks.

### Who asks the pair's question

Discovery re-checks the sentexes the settle **moved**, and the checks are scoped to the
context they are asked in — a context is convicted only on grounds it can see
([contexts.md](contexts.md)). Where each side of a pair convicts the other that is
enough: whichever side arrives second finds the pair, so the answer does not depend on
which arrived first.

A pair whose halves sit either side of a `genlContext` edge convicts one way only.
`(animal X)` in a general context and `(plant X)` in one that sees it are each
admissible where they are written, and only the seeing side has both in view. Asked from
the arriving sentex's own context alone, the general side's check finds nothing at all,
so the same three sentences would land on a defeat or on two coexisting claims according
to the order they were written in — with unequal strengths, a difference in belief and
not only in reporting.

So each candidate's question is asked from **every context that can see a pair it could
form**: its own, and the maximal common descendant of its own and each context holding a
sentex it could pair with (`settle/clash-askers`). Nothing is widened by that — each
vantage already sees both halves, and it convicts on what it can see. The maximal common
descendant is the *least specific* context with the whole clash in view, so a narrow
context's separation never reaches back over a general claim it was never about.
Which sentexes a candidate could pair with is read off the argument-1 roots, one posting
per term: its term's other memberships for a separation, the other fillers of the slot
for a `functional` predicate, the converse of an `asymmetric` claim.

The vantages run under the KB's constraint policy, like the retroactive sweeps. A pair
split across a visibility edge is exactly the clash neither writer could see, so under
`:refuse` it stays the exposure pass's business — a `:disjoint` entry in `violations`
naming the contexts it is visible from, with belief untouched. Under `:arbitrate` every
route agrees. The exposure pass covers **disjointness only**, so under `:refuse` a
functional slot filled either side of the edge, or an asymmetric claim written across
one, is neither refused nor reported: the door sees one half and the ledger has no entry
kind for it.

**One sentence stated in two visible contexts is two sentexes**, and a claim that denies
it denies both. The same membership in a general context and in one that sees it can
carry different strengths and different support, so `checks/disjoint-problems` names one
pair per opposing *sentex* rather than per opposing type, and the asymmetric arm does the
same for the converse. `functional-problems` counted its clashes that way from the start.
The asymmetric arm therefore reads its converse twice: `inherit/surviving` answers what is
inherited — one claim per tuple, the strongest — and the sentexes literally stating the
converse are read beside it and merged on the handle.

### Where conviction is one-sided

One shape convicts one way only, **through argument preservation**. `(outranks animal
cat)` denies the more specific `(outranks cat reptile)`, because preservation reads a
goal's arguments upwards: the specific claim asks whether the general one denies it, and
the general one never asks about the specific. Written specific-first, both stand and
nothing is reported; written general-first, the second write is refused outright.

That is not a narrowing to remove — the exhaustive pass in
`settle/*incremental-clashes*` does not share it, since upward reading is what
preservation *is*. What a candidate rule for it reads is the **spec-side product**: the
tuples strictly below the arriving claim, which is `specs(a) × specs(b)` per moved fact
of a preserved predicate. Measured on a 4-way, 3-deep hierarchy under each of two roots
— 85 types below each — that is 7,225 candidate tuples for one claim, against the 2
postings the visibility question above reads off an argument root, and it grows as the
square of the hierarchy below the claim where the root read does not grow at all. So the
two shapes look alike and cost nothing alike, and this one is the limit the engine stops
at rather than a question nobody asked.

`clash_oracle_test` excludes this shape and says so — no `argPreserving` declaration is
made there — and covers the visibility one.

## The solver seam (`vaelii.impl.solve`)

The external solver is a plug-in behind a protocol:

```clojure
(defprotocol Solver
  (solve [solver program]
    ;; -> {:defeat #{handle...} :violated [nogood...]}
    ))
```

A `Program` carries four fields: `assumptions` (the contested defeasible handles —
never known-true), `fixed` (known-true background referenced by a contradiction,
assumed not decided), `contradictions` (nogoods with priorities and sentences), and
`content` (`{handle {:sentence s :context c}}` — what each assumption *says*, which is
what lets a tie-break key on content rather than on a handle). This is exactly what a
real backend renders to ASP:

- default nodes → choice/`{a}` atoms;
- `:monotonic` `fixed` nodes → **omitted** (assumed true — never sent);
- contradictions → **weak constraints** with priorities, so the program is always
  SAT and the violated weak constraints are the reported result.

### The split is enforced, in both directions

Only `:default` content is ever decided. `:monotonic` is the fixed background a solve
reasons *from* — a solver that could withdraw it would be deciding the premises rather
than the edges. That followed from `decide-nogood`, but nothing checked it, so `settle`
guards both ends:

- **Input** — `check-solver-eligible` rejects a contested handle that is not
  `:default`, and throws rather than proceeding. Read before any defeat lands, since
  `defeat-class` reports nil once a datum is OUT; after the fact the question cannot
  be asked.
- **Output** — `accepted-defeat` keeps only defeats the program actually offered.
  `set-solver` takes any implementation, and an unclamped `:defeat` would let a
  third-party solver withdraw known-true content the program never handed it. An
  overreaching defeat is dropped with a warning rather than obeyed.

The cost of a regression here is not a wrong answer; it is the engine quietly giving
away something it knows to be true. `asp_label_test` covers both directions.

Two solvers ship. The default is `local-solver`, a deterministic stub that satisfies
contradictions highest-priority-first by defeating the greatest-`content-key`
contested member and reports any nogood it cannot satisfy.

`vaelii.impl.asp.edge/edge-solver` is the real thing: it renders the Program to
ASPIF exactly as described above and solves it with clingo or clasp. Install it with
`(core/set-solver kb :asp)`; callers do not change, and it falls back to
the stub when no backend is reachable. Where the stub walks contradictions one at a
time, ASP optimizes globally — given two nogoods sharing a member it defeats the
shared one rather than one member of each. See [asp.md](asp.md).

## API

```clojure
(assert kb S ctx {:strength :monotonic})   ; known-true; never defeated, never solved
(assert kb S ctx)                           ; :default (the common case)
(conflicts kb)                               ; the reported contradiction sentences
(violations kb)                              ; derived conclusions dropped as inadmissible
(preview kb {:add […] :remove […]})         ; the belief a batch would move, then rolled back
(set-solver kb :asp)                        ; the real answer-set backend, by name
(set-solver kb solver)                      ; or any Solver value
```

`assert` also refuses a **non-ground** fact. `(mortal ?x)` asserts nothing — it is an
open sentence, and stored as a believed premise it matches any goal under `unify`,
behaving as a universal nobody licensed. Universals are written as rules, where
`rules/check-range-restricted` governs the variables. Rule-ness is decided from the
canonicalized record's `:antecedent`, so `implies`, a `set/*Rule` wrapper, and a
nesting of the two are classified alike. Every rejection carries an `ex-info` `:type`,
so a caller discriminates on that rather than guessing from which keys are present:
`:naming` `:not-well-formed` `:not-ground` `:not-range-restricted` `:not-indexable`
`:not-assertible` `:arity` `:arg-type` `:arg-genl` `:arg-position` `:inter-arg-type`
`:arg-constraint-kind` `:disjoint` `:functional` `:asymmetric` `:not-stratified`
`:exception-not-closed`, plus the two about the *request* rather than the knowledge —
`:shape` (the context is not a symbol, the sentence is not an s-expression) and
`:unknown-option` (a non-map `opts`, an `opts` key `assert` does not read, or a
`:strength` that is not an assertable class).

## Where the layer stops

- A nogood is not explicit negation only. A disjointness, functionality or asymmetry
  clash convicts by naming a *second believed sentex*, which is a nogood in exactly the
  same sense: `settle/constraint-nogoods` files it and ranks it **above** a rebuttal —
  priority 3–4 against 1–2. Whether the assert path admits such a sentence at all is
  the KB's `:constraints` policy (`open-kb`): `:refuse` throws, `:arbitrate` refuses
  only against `:monotonic` content and leaves a `:default` claim to settle. What is
  dropped and reported rather than arbitrated is a violation with **no opposing
  sentex** — an argument constraint, an arity, a malformed special predicate, an
  unstratified derived edge.
- NAF is the thing that is not a nogood. In rule antecedents it is `unknown` /
  `thereExists`, re-evaluated on the `exceptWhen` triggers and storing nothing
  ([naf.md](naf.md)); the JTMS `out` slot stays **reserved** — an existential NAF is
  negation over a pattern, with no single handle for the out-list to hold, so
  re-evaluation is the mechanism and nothing ever populates the slot. `valid?` reads it
  on every relabel and finds it empty.
- A default/default clash is never arbitrated: it is reported as a dilemma and the
  ranking is the application's. That is deliberate (see "There is no second axis"), but
  it does mean the engine offers no ordering at all among equally-strong rebuttals.
- A settle commits to one optimal answer set, so `in?` alone cannot distinguish a
  forced belief from an arbitrary pick between equals.
  `vaelii.impl.asp.label/classify` recovers that distinction by enumerating optima
  (`:true` / `:supportable` / `:false`), and `label-context` materializes one
  labeling as a specialization context — but belief itself still commits silently.
  See [asp.md](asp.md).
- Cardinality/aggregate contradictions are not expressed; a nogood is a flat set.

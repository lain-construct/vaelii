# Non-monotonic truth maintenance

- **Covers:** how belief is computed from justification strength, how `settle`
  resolves soft contradictions without throwing, which features a settle is built from,
  and what each step of a settle costs.
- **Not here:** the belief a batch would move before it commits →
  [preview.md](preview.md); the ASP backend a contested edge renders to →
  [asp.md](asp.md). Nor what an *agent* believes — `(believes Alice P)` is a projection
  into Alice's context and no part of this layer → [belief.md](belief.md). Nor what
  belief *is*, as a function of the stored content → [reference.md](reference.md).
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
`jtms/defeat-class`) reads a believed handle's class back. Two classes and no third:
[why](defenses.md#two-strength-classes-not-three).

**A re-assert takes the stronger of the two classes, and never the weaker.** The mark is
resolved from *content*, like a re-asserted rule's slots
([canonicalization.md](canonicalization.md)). `strength/max` is commutative and
idempotent, so every order agrees and a third assertion changes nothing. Narrowing a class
is `retract!` and re-assert — the retraction takes the mark with it, so nothing is
inherited across one. Why a bare re-assert's silence is not a downgrade:
[why](defenses.md#a-bare-re-assert-never-downgrades-the-class).

**A premise's strength is written in two places, and the record is the authoritative
one.** `assert-entry/put-premise-mark` writes both halves together — `jtms/add-premise` into the
network and `p/mark-premise` into the record store, where every backend keeps it as the
sentex's own `:strength` field; the disk store also caches the strength's rank in the record's
slot flags, and the field stays the durable copy. The record is what `recover` replays
(`rebuild-tms` reads `p/premise-strength`, never the network), so it is the copy that
survives a restart and the copy an import writes. The network's copy exists because the
class fixpoint reads it once per in-region node per worklist pop, under the dense
representation's exclusive write stamp: on the disk store that read is a lock and a slot
decode, and on a server store a round trip, so the resident copy is what keeps
[locality](#2-locality) a claim about every representation. It is also the only copy
`preview` can move — a suspended premise is suspended in the network alone, which is
what makes that retraction reversible without writing a frame.

### The forced-monotonic roster

Some content is held `:monotonic` whatever strength it was written at. The roster is
every predicate on it as `(forced_monotonic_predicate P)`, plus every `(F …)` literal whose
arguments are all spelled as predicates of arity 2 or more (camelCase,
[naming.md](naming.md)) for a functor on it as `(forced_monotonic_between_predicates F)`.
A predicate is on it by the engine's **baseline** or by a declaration. The baseline
(`checks/baseline-roster`) is code, held on every KB whether or not it loads CxCore:
`genlCx`, the relation marks (`irreflexive`, `anti_symmetric`, `asymmetric`, `functional`,
`functionalInArg`, `anti_transitive`, `transitiveInArg`, `transitiveInArgInverse`), the definitional declarations
(`disjoint`, `covering`, `partition`, `sibling_disjoint`, `orthogonal`), the arity bindings (`arity`, the
nine exact-arity classes, `variable_arity` and its two specializations, `arityMin`),
`except` and the equality relations (`rewriteOf`, `sameAs`, `equals`) with the first, and
`genl` with the second: a `genl` between two predicates is on the roster and a `genl`
between types stays defeasible, so a type edge admits exceptions. CxCore declares each of
these, which moves no membership, and the function classes (`injection`, `surjection`,
`bijection`), which are on the roster by declaration alone. CxOrganism declares the
metatype `folk_species` the same way, since a species membership is definitional: a rule
concluding a roster literal from `(folk_species ?s)` alone is a roster rule.
`checks/on-roster?` is the one reader of membership, the baseline united with the two
global properties the declarations maintain, and `checks/forced-monotonic?` reads a
literal through it. The source digest
covers the baseline, so a reasoning image computed under another baseline is declined and
the store recovers under the new one. The decisions that put each group on the roster are
[reference.md](reference.md#decisions) 1, 7 and 10 to 13 and 17.

**Forcing is applied when belief is computed, never when content is stored.** Every write
is stored as written: a premise at the strength it was written at, a denial of a roster
literal as an ordinary premise, and every rule firing whatever its rule and conclusion. The
network holds three forced sets beside the strengths (`jtms/set-forced`), each a set lookup
on the relabel path:

| set | members | what the labeller does |
|---|---|---|
| `:mono` | a premise of a roster literal, and a `checks/roster-rule?` concluding one (`checks/forced-premise?`) | its premise mark confers `:monotonic` |
| `:out` | a stored denial `(not S)` of a roster literal (`checks/inert-denial?`) | the fixpoint never adds it, so it is never believed, forms no nogood and fires no rule |
| `:void` | a firing `checks/forced-conclusion-violation` convicts | the justification is invalid: it supports nothing and confers no class |

`checks/force-sentex!` writes a stored sentex's `:mono` and `:out` memberships before its
premise mark or first justification lands, and the chainer writes `:void` before it adds a
convicted firing's justification (`chain/place-fact-conclusion`), so no element holds a
label its set rules out, even for one relabel. A denial held OUT keeps `S` believed, and
`why-not` answers `:inert` for it. A denial of an equation instance is one of these: the
equation rewrites the denied instance as it rewrites every other.

**A rule concludes a roster literal from roster antecedents only.** A firing is convicted
when its conclusion is a denial of a roster literal, or a roster literal and its rule is
not a `checks/roster-rule?`: every antecedent a roster literal, no `unknown`, no
`set/defaultRule`, and no believed `exceptWhen`. A convicted firing is stored, held void and
reported as a `:forced-conclusion` violation. A roster rule's firings confer the class its
antecedents give, and a roster rule's own premise is in `:mono`. CxCore's `injection`,
`surjection` and `bijection` rules are of this kind. A `genl` consequent with variable
arguments is on the roster only where a firing binds two predicate-spelled terms. An
`exceptWhen` arriving on a roster rule convicts its firings, and the last one leaving
releases them (`special/index-exceptWhen-meta`, `special/unindex-exceptWhen-meta`).

**The declaration is a switch.** Asserting or retracting `(forced_monotonic_predicate P)`
for a `P` outside the baseline rewrites the forced memberships over everything that
mentions `P` (its literals, their denials, the rules reading or concluding it, and their
firings), and the relabel each moved membership runs is the whole recompute
(`checks/force-reach!`, called from the declaration's special-table arms when `P` joins or
leaves the roster). A declaration of a baseline member moves no membership and runs no
switch. The rules in that
reach are queued for a fresh join (`:all-rejoin`), so a firing swept while it was held void
is placed again. There is no ratchet: a KB that retracted a declaration believes what a KB
that never held it believes. The recompute costs the reach of `P`. Belief moving a
declaration (a derived declaration going OUT) moves the property and runs no switch.

**Retracting a declaration is refused where its predicate has no unforced semantics.**
`retract!` and `edit!` refuse the retraction of every declaration CxCore makes except those
of `injection`, `surjection` and `bijection`, with `:type :uncleared-forcing`, the
`:predicate` and the `:missing` semantics (`checks/uncleared-forcing`). `genlCx` is always
forced and lifted. The refusal reads the sentence alone.

**A restart rebuilds the sets from the records.** `recover` replays every premise at its
stored strength and every justification, then writes the forced memberships the roster
gives (`checks/force-roster!`) before it reads belief. A denial of a roster literal
stored with no premise mark and no support is the record a store from before this design
kept inert; `force-roster!` gives it the `:default` premise mark. A premise such a store
holds `:monotonic` stays `:monotonic`: no record tells a coerced strength from a written one. A
firing such a store dropped is placed again by the re-join a retraction of its
declaration queues, and by `forward-chain` where the declaration was retracted before
the upgrade. The reasoning image carries the forced sets and stamps the declared roster
in its policy (`reasoning-image/declared-roster`), so an image computed under another
roster is declined.

### Strength propagates from the antecedents

A justification confers **`min(its own strength, the weakest of its antecedents'
classes)`**, where a rule's own strength is read off its defeasibility:

- a **bare rule** confers `:monotonic` — it adds no defeasibility of its own, so the
  conclusion is capped by whatever it rests on;
- a **`set/defaultRule`** confers `:default` — it introduces defeasibility, so its
  conclusions are always `:default`;
- a **guarded rule**, one with an `(unknown S)` antecedent or an `exceptWhen` stored
  against it, confers `:default` whatever its defeasibility and its antecedents' classes
  ([reference.md](reference.md#decisions), decision 14). A blocker arriving takes its
  conclusion OUT, so the conclusion is never `:monotonic`.

`provers/firing-strength` computes this class, and a firing records it as its
justification's `:strength`, which the dense network keeps in its `j-mono` bitmap. The
exceptions are read as stored, belief unread. An `exceptWhen` can arrive after the rule
has fired and can leave again, so `special/restrength-firings!` rewrites the strength of
the rule's recorded firings when one is stored or removed, as it does when a re-assert
resolves the rule's defeasibility ([inference.md](inference.md)).

A conclusion is therefore no stronger than the weakest thing it rests on: a bare rule
over a merely-default premise concludes a *default*, the same bare rule over known-true
facts concludes `:monotonic`. **The taxonomy edges a firing names are grounds like the
facts** — a `genl` edge a subsumed match climbed, a `genlCx` edge the conclusion's context
reads the rule or the facts over ([contexts.md](contexts.md)) — and cap it the same way.
The **informant is excluded** from the cap.

A rule's own class (`:strength` — `opts :strength` at the entry point, what `defeat-class` answers
for its handle, what a solver is shown) and a rule's defeasibility (bare versus
`set/defaultRule`, what its firings confer) are two slots, and only the second moves belief;
nothing in the engine defeats a rule. Why the cap, why the taxonomy edges count, and why the
informant does not: [why](defenses.md#a-firing-is-capped-by-its-weakest-ground).

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

The least fixpoint is unique, so it is independent of visit order and of the order the
knowledge arrived in: [why a single pass would be
wrong](defenses.md#the-class-fixpoint-is-a-least-fixpoint-not-a-single-pass).

## Two invariants

Everything below is in service of these. They are not negotiable, and they pull
against each other, which is what makes the design interesting.

### 1. Order independence

**The same knowledge, given in any order, yields the same beliefs.** A common-sense
KB learns generalities and specifics in whatever order the world supplies them —
"birds fly" before or after "Tweety is a penguin" — and an engine whose answers
depend on that order is answering a question nobody asked.

Belief is therefore *computed from current state*, never accumulated as events arrive.
Two leaks would let arrival order back in. The first is **tie-breaks**: when two beliefs
are equally strong something has to choose, and every such choice keys on **content**
(`solve/content-key`) rather than on the handle — [why content and not the
handle](defenses.md#tie-breaks-and-orderings-key-on-content-not-the-handle). The second is
**a dependency a justification does not record**: retracting X must leave what a KB built
without X would hold, so a justification names every reachability its firing rests on — the
`genl` edges a subsumed match climbed, and the `genlCx` edges the conclusion's context sees
the rule and the facts over ([contexts.md](contexts.md)) — and both retract and defeat run
the ordinary dependency-directed path. Where a reachability outlives the one witness the
firing named, the conclusion comes back as a re-derivation: after a retraction or a network
defeat of the witness in the network, and after a reader's verdict or an `except` of it at each
reader that still reaches ("Where the layer stops" states what the re-derivation leaves
stored).

**The invariant is over the writes offered.** No definitional clash is refused
(decision 8 of [reference.md](reference.md#decisions)): a sentence that completes a
disjointness, functional, cover, `asymmetric` or `anti_transitive` clash with content the
KB already holds is stored, and the settle decides the nogood from its members' classes.
So the same sentences in any order leave the same store and the same beliefs, and a clash
whose members are all `:monotonic` stands in `conflicts` whichever member arrived last.

**What a refusal may rest on.** A refusal reads the sentence and nothing the KB holds
beyond the vocabulary that spells it: naming (which reads the sentence's own argument
count), groundness, a malformed special predicate, and an argument constraint, which
convicts on the *absence* of a path and so has no member to weigh.
`checks/refuses-assert?` answers false for a clash that names the other stored members
of its nogood (`checks/arbitrable?`), so the entry point stores it, and what is stored is
a function of what was offered. A declaration over two `genl`-related types, and a cover naming a part
disjoint from its whole, are stored like any other declaration, and each is a hard clash
a reader reports
([Declarations over related types](#declarations-over-related-types)). A tuple under
`irreflexive`, a non-mergeable `anti_symmetric` converse and a tuple whose length breaks
its predicate's arity binding are stored in every order, and each reader decides them
([Nogoods decided at the reader](#nogoods-decided-at-the-reader)). A write the
forced-monotonic roster rules out is stored as written and held OUT or void by the
labeller ([The forced-monotonic roster](#the-forced-monotonic-roster)).

`test/vaelii/order_independence_test.clj` enumerates every permutation of each
scenario and demands a single distinct outcome. Note that the weaker assertion —
"exactly one side wins" — is true under every order *even when the winner flips*, so
it passes against an order-dependent engine. Asserting the **same** side every time is
what catches it. `subsumption_support_test` and `placement_context_witness_test` are the
retraction half, each asking whether losing an edge lands where never having had it does.

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

**Locality is more than one claim, and they are secured differently.** The
*equivalence* — a region relabel reaches the labels a global one would — is semantic,
and the differential oracle holds it by comparing the whole network after every step.
The *containment* — the flips are inside the published window, and the window inside the
region — is what says a small region was asked for, and it is measured on both networks.
That **no work is paid per boundary node** is neither: it is structural, secured by the
`Tms` protocol passing no store, so no implementation of it *can* turn a boundary read
into a lock and a slot decode or a round trip. That is the same fact the resident
strength copy rests on. What is left — the cost of the in-region work itself — is the
one piece nothing on the protocol holds, and
[defenses.md](defenses.md#locality-is-a-claim-about-every-representation) is where the
shape that would break it is measured. The obligations a second network inherits are
listed once, with the gate for each, in the protocol's own docstring
(`src/vaelii/impl/jtms_protocol.clj`).

The region is also **the answer to a question callers ask**, which is why `settle`
publishes it rather than discarding it. Three readers want the same thing — a
consequence preview, a consequence report, and a change feed
([preview.md](preview.md), [feed.md](feed.md)) — and each of them would otherwise diff
the believed set, which is O(KB) per write and flat in nothing. `settle-finish` decides
once what the settle moved (the relabelled regions plus the flips no relabel records)
and hands that one answer to all three. That region collects a **superset** of the
handles whose belief flipped, on purpose:
[why](defenses.md#the-touched-window-is-a-superset-not-the-flip-set).

Measured, on an in-memory graph of N premise→conclusion pairs (no store in the way).
Each cell is a whole-graph relabel against the region-scoped one, so the pair reads as
what locality is worth at that size:

| nodes | `add-justification` | `sweep!` (2 nodes) |
|-------|--------------------|--------------------|
| 500   | ~760µs / **~18µs**  | ~150µs / **~38µs** |
| 1000  | ~1,300µs / **~20µs** | ~340µs / **~40µs** |
| 2000  | ~2,100µs / **~20µs** | ~540µs / **~41µs** |
| 4000  | ~4,000µs / **~20µs** | ~1,200µs / **~48µs** |
| 8000  | —                  | ~2,500µs / **~40µs** |
| 16000 | —                  | ~5,600µs / **~46µs** |

The `sweep!` column collects a fixed two-node chain out of a graph of N
premise→conclusion pairs, so the region is the same size at every N and only the
background grows. A whole-graph relabel therefore tracks the background exactly, which
is what the left-hand figure shows.

The whole-graph column grows linearly with the graph; the region-scoped one is flat.
That is the whole point — the gap widens without bound, so locality is an asymptotic
property rather than a constant factor. At present KB sizes it is invisible end-to-end:
a single `assert` is dominated by fixed per-assert overhead, not this join. It is a
claim about what happens at a million facts, not at a thousand — and a claim about every
representation of the network, not only the one this table measures:
[why cost shape is part of matching the reference](defenses.md#locality-is-a-claim-about-every-representation).

## The TMS (`vaelii.impl.jtms`)

Belief is a least fixpoint, recomputed region-locally rather than accumulated:

- **`:in`** is the believed set and the sole authority on belief — nodes carry no
  label of their own, so there is no second copy to drift. It is maintained
  region-locally. Nothing forces a datum OUT: a contradiction is decided at each reader
  ([A defeat is scoped to its vantage](#a-defeat-is-scoped-to-its-vantage)), so the
  network holds support labels only, and a datum OUT is one with no valid derivation.
- `affected-region` — the forward consequence closure of whatever changed. A node's
  label is a function of its justifications' antecedents, so a node whose label can
  move is by construction reachable from what moved; everything else is boundary and
  is never even looked at.
- `relabel-region*` — the localized least fixpoint. Also recomputes defeat-classes,
  but only inside the region: a boundary node whose class could move would have an
  antecedent in the region, and would therefore be in the region.
- `set-blocked` seeds it with the **consequences of the justifications whose blocked
  status moved** — the ones blocked in both the old and the new set are already
  accounted for in the current labels, so a call that changes nothing does no work at
  all.
- the **sweep** (`sweep!`, and `retract!`'s tail) is region-local in the same way: the
  justifications to tear down are read off the dead nodes' own `:supports` /
  `:consequences`, never found by scanning the justification map. `exceptWhen` makes
  sweeping routine rather than a retraction-only path — a blocked justification leaves
  its conclusion OUT and the sweep collects it on ordinary fact arrival — so
  a sweep that scanned the whole graph would make a run of them quadratic.
- `relabel` (the whole-graph version) has **no engine caller at all**. The assert /
  retract / settle path relabels regions, and a rebuild composes the region relabels its
  own adds run rather than closing with a global pass (`recovery/rebuild-tms`), because a
  region relabel over the affected closure is equal to a global one. What `relabel` is
  for is the differential oracle: a whole-graph operation both representations implement,
  so the two can be compared on one.

### Derivation depth

A node's depth is what the forward chaining bound reads
([inference.md](inference.md#forward-chaining), `:max-depth`). The network holds every
depth at the least solution of one equation: a premise sits at 0, and any other node at
the least, over its justifications, of one more than the justification's deepest
antecedent. A justification's informant is not one of its antecedents. The solution is a
function of the network, so a network reached by any sequence of operations holds the
depths the same network built directly holds.

Two walks keep the stored depths there, each over a part of the region the relabel
already walks:

- **A depth that falls** — `ensure-node` placing a node shallower, or a premise mark
  landing on a derived node — is pushed down the consequences it lowers, shallowest
  first, and the walk stops at a consequence whose depth does not move
  (`jtms/lowered-depths`).
- **A node that loses a premise mark or a justification** — through `retract!`,
  `suspend-premise`, `drop-justification!`, or a sweep that removes a survivor's
  justification — has the consequence closure of the survivors among such nodes solved
  afresh, with every node outside it held fixed (`jtms/region-depths`, Knuth's
  generalization of Dijkstra's algorithm). A retraction that sweeps its whole closure
  walks nothing.

Both walks read the network through accessor functions, so the dense network runs the
same code over its columns, and `jtms_dense_oracle_test` compares the depths of the two
after every step of its streams.

A stored depth departs from the equation's solution in two cases:

- A firing places its conclusion at one more than its deepest **matched fact**
  (`chain/derive-conclusion`), and its justification also names the `genl` and `genlCx`
  supporters the match climbed. A supporter that is a premise sits at 0 and changes
  nothing. A supporter derived deeper than every matched fact leaves the placed depth
  shallower than the equation's, until a walk above re-solves the node.
- `recover` rebuilds the network with every depth at 0
  ([storage.md](storage.md)); only a later walk re-solves a node.

### Belief filtering is a namespace boundary

`jtms/in?` is the whole of the belief question, and the fourth invariant — a stored sentex
is not a believed one — is a claim about who asks it. The `IndexStore` postings are
storage: they hold a defeated default, a conclusion whose support was withdrawn and a
spelling an equality retired, because all three are revivable and belief lives here rather
than there. So a caller reading a posting owes an answer to *which* it wants, and read
straight off `vaelii.impl.protocols` a forgotten filter and a deliberate as-stored read are
the same three characters.

**`vaelii.impl.reads` is where the question gets asked, in the name of the read.**
`as-stored-…` takes the index store, because an as-stored read *is* an index operation, and
each entry point's docstring says what a stored-but-disbelieved answer is for. `believed-…` takes
the KB, because belief is a question about the KB — and it filters with `in?`, which drops a
superseded spelling along with a defeated one, so a believed entry point means what
`kb/sentexes-matching` means. An entry point is a wrapper and never a rewrite: one call to the
protocol method it names, the same laziness, the same count-aware path, so it adds no index
operation. The cardinalities, the vocabulary roster and the watched-rule roster carry one
entry point each, and each says why there is no second.

`lein lint`'s **E16** is what makes it a boundary rather than a habit: a raw index read
anywhere under `src/` but the implementers fails, and the roster in that check is the one
place an exception is written down. The implementers are the entry points themselves, the protocol,
the retrieval a believed read is built from (`kb`, `resolution`), the storage backends, and
the dump that copies every entry the index holds. `RecordStore` is deliberately outside the
check — a record *is* the storage, so fetching one asks nothing about belief. Why the
as-stored half is named rather than assumed:
[why](defenses.md#an-as-stored-read-is-named-never-implied).

### Two representations of the same network

The network is always resident, which makes it a scale wall of its own (the reference map
measured ~467 B/node — see
[density.md](density.md#phase-3--the-dense-truth-maintenance-network-tms-dense)), so it
sits behind a `Tms` protocol with two implementations, chosen by `open-kb`'s `:tms`:

| `:tms` | the graph is | |
|---|---|---|
| `:dense` (default) | bitmaps + primitive-keyed maps, and no justification object at all | 5.5× denser on a fact corpus, 3.3× on a rules-heavy one, ~3.8× at corpus scale |
| `:reference` | one atom over one persistent map | readers get a consistent snapshot from a single deref |

**The boundary is the representation, not the algorithm.** Both run the same least fixpoint
over the same affected region, because that is the semantics of belief here and not an
implementation detail; what differs is where a node's premise flag, depth and adjacency
live. What a second network owes — the fixpoint, atomicity to a concurrent reader, the
containment `touched` promises, and holding no store — is enumerated with its gate per
item in the `Tms` docstring, which both implementations depend on. The dense network also
requires the reference namespace for two helpers (`jtms/graph-just`, `jtms/dissoc-all`), and the
reference requires nothing of the dense one. `jtms_dense_oracle_test` compares the two in full after every step of randomized
operation streams; plain `lein test` runs the whole engine through the default dense one,
and `VAELII_TEST_TMS=reference lein test` through the persistent-map baseline.

**Every method is in one of seven roles, and the protocol says which.** The network is
one function — `label(graph, attributes, blocked) -> (in, classes)`,
with `believed = in - superseded` — so a method either supplies an argument, reads a
result, or edits the domain. `jtms-protocol/roles` writes the division as data and
`jtms_protocol_test` holds it. The division is of what a method *touches*, never of what a
network may be implemented without: every mutation relabels, so every role's mutators
write the output role's state.

The two sets a caller replaces whole each settle are two roles rather than one, because
they enter belief at two different points:

| override | enters at | moves | decided by |
|---|---|---|---|
| `blocked` | inside `valid?`, so a blocked justification supports nothing | `in`, so an excepted conclusion is swept | the `exceptWhen` re-evaluation, bounded by the recheck queue's triggers |
| `superseded` | subtracted at the read, after the fixpoint | nothing — the datum stays in `in` so its rewritten twin keeps its justification | the equality closure |

Neither is computed by the network, which holds no KB. Each method applies a set it was
handed, so its cost is the region that set seeds and never the cost of deciding the set.
A **third** place belief is decided is not on the protocol at all: a reader's verdict
on a nogood and a visibility `except` are applied per reading context above it, over
`jtms/grounded-in-region`, and the network's labels do not move for either (*[A defeat is
scoped to its vantage](#a-defeat-is-scoped-to-its-vantage)*).

The eighth role, `:hold`, is the settle's and not the fixpoint's. A settle moves labels in
more than one relabel before it publishes, so for a reader on another thread it holds the
belief it began from: while a hold is open, each relabel records the labels it moves as
they were before the first move, the region it already walks being the cost, and a thread
other than the settle's reads those until the settle publishes
([storage.md](storage.md#the-single-writer-contract)).

**The network keeps the graph; the record store keeps the record.** A justification is
stored durably, and belief reads only part of it — the antecedents, the consequence, the
strength and the informant. The firing's **variable bindings** are no
part of that: they are read only to re-evaluate an `exceptWhen` query or a NAF antecedent
per firing, and both readers hold the KB and take the record from the store. So
`jtms/graph-just` projects a justification on the way in, and neither representation
holds a second copy of one. `core/justification` and its two neighbours read the store
for the same reason — a justification *is* a record, and a record's home is the store.
(The projection also normalizes, which is what makes the two representations store values
equal to each other's however a caller spelled the justification.)

**No stored antecedent vector is in arrival order**, because belief reads it as a set and
every *report* reads it as a list. Three of the eleven builders get there by **sorting on
content** (`kb/antecedent-order`) — forward chaining's two placement sites and
`special/derive-equality`, the three handed a vector whose order is an arrival. The order
is the sentence then the context — a **structural** key, walked in place by
`nm/compare-form` rather than printed, so no ambient `*print-length*` can elide two long
sentences to one prefix and drop the tie back onto arrival — and the vector never holds
the informant: the record names a rule once, in its own `:informant` slot, and
`jtms/rests-on` adds it back for a reader that wants everything a justification stands on.
Nothing reads a position — `valid?` and `has-justification?` read the set.

**A rule informant is an implicit antecedent.** `valid?` needs the rule believed, and
both representations list the justification under the rule's node in the adjacency, so
retracting or defeating a rule withdraws everything it licensed through the same region
walk a fact's retraction takes.

**The other eight build the vector positionally instead, or copy a stored one, and the
position is a role.** `special/deduce-lift` writes `[fact, declaration]`, `special/justify-twin!` writes
`[original, equality edge]`, and `special/entail-arg-type` writes `[fact, declaration,
genl edges…]` — each slot filled by what that supporter *is* to the derivation, so there is
no arrival to sort out; the tail of the third is `checks/edge-support`, a shortest
**visible** path expanding in name order. `special/materialize-defn-rule` writes the one
definition the rule rests on, and `context-nat/materialize-edge` writes `[sub NAT's
termOfUnit, super NAT's termOfUnit, declaration]`, plus the relation fact when one is the
evidence. `io.import/import-justifications!` remaps a dumped vector handle for handle,
carrying the exporting KB's order across. `integrate/fold-dependents!` and
`integrate/fold-supports!` copy a stored vector onto the surviving row of a fold, the first
putting the survivor in the folded handle's position.

**A list of justifications is ordered by the same rule**, through one key
(`kb/justification-content-key`): the informant's own sentence and context, the
antecedents' sentences, the bindings, then what it concludes.
`core/supporting-justifications`, `core/dependent-justifications` and a clash report's
`:justifications` all sort by it, and all three start from an id **set** — `jtms/supports`
and `jtms/dependents`. That both the stored vectors and these lists order on content and
never on the handle is one rule with one home:
[why](defenses.md#tie-breaks-and-orderings-key-on-content-not-the-handle).

**The key is built once per entry, not once per comparison.** `sort-by` calls its key fn
from inside the comparator, so a naive sort builds it ~2·n·log₂n times — and each build
is a `get-sentex` per antecedent. The adjacency lists every firing a rule licenses
under the rule's node, so `dependent-justifications` on a rule pays that multiple on the
whole history:
at 100k firings, ~3.3M key builds where 100k would do. All three sites decorate, sort and
undecorate through `nm/sort-by-content-key`, which is the same comparator over the same
keys and stable either way.

Two properties are easy to assume and would be wrong — a dense network cannot simply
replace the reference (`RoaringBitmap` is mutable, and `jtms_atomicity_test` pins that a
relabel applies all-or-nothing), and order independence rests on a node's backward
`:supports` and forward `:consequences` naming the **same** edge set:
[why both, and why they mean two implementations rather than one](defenses.md#two-tms-implementations-not-one).

### Blocked justifications (`exceptWhen`)

`:blocked` is a set of **justification ids** whose rule's exception currently holds,
and `valid?` reads it alongside its antecedent and rule checks. The TMS has no KB and
cannot run the level-6 exception query: the caller evaluates the exception and hands the
answer in with `set-blocked`, which *replaces* the set rather than adding to it. A block
therefore holds only while its exception holds now,
whatever order the exceptions were discovered in. The set is the placement context's
answer; a reader below the placement asks the exception again and reads a firing it
finds blocked as invalid in its own withdrawal
([naf.md](naf.md#evaluated-in-the-placement-context-not-the-join)).

A blocked *justification* is invalid: it supports nothing and confers no defeat-class
(`node-class` never reads a blocked justification's strength), so an excepted conclusion
with no other derivation is OUT and the retraction sweep deletes it
([exceptions.md](exceptions.md#garbage-collection-not-defeat)).

**Recovery starts unblocked**, because it starts from an empty network and no store holds
an exception's answer. The window between the rebuild and the next settle believes an
excepted conclusion, and that settle withdraws it by replacing the set. The whole-graph
`relabel` clears the blocked set and the supersession map, since neither can be recovered
from the store, and `retract!` prunes swept justification ids from the blocked set so a
stale id is never reapplied.

Both premises and justifications carry a **strength**: a premise its assumption strength
(on the sentex record), a `Justification` a `strength` field (the defeat-class it
confers). A `Justification` has no out-list: NAF is built, as `unknown` /
`thereExists`, by re-evaluation, see [naf.md](naf.md).

**Retraction** is dependency-directed relabel-then-sweep: drop the premise, relabel, and
delete every datum in the retracted datum's consequence closure that ends OUT. A datum
with another derivation survives. The closure it marks **is** the region it relabels, so
the two walk the graph once between them, and the sweep reads the `:in` set that relabel
just recomputed.

`suspend-premise` is the first two steps without the third: drop the premise, relabel
the region, sweep nothing. It is a retraction's whole effect on **belief**, because the
sweep never moves a label — it collects datums that are already OUT.
That makes it the one *reversible* retraction: `add-premise` at the same strength puts
it back, at the same handles, with every justification still where it was.
`core/preview` is the caller ([preview.md](preview.md)).

**Belief-sensitive reads.** A default a reader takes OUT stays *stored* but is not
*believed* there. So matching is belief-sensitive: `res/raw-match`, `core/sentexes-matching`,
and `core/types-of` skip handles that are currently OUT, and a read at a context skips
what that context withdraws. Raw introspection
(`core/sentex`, `find-sentexes`, the web browser) still sees everything.

## Soft, prioritized contradictions (the settle layer)

`assert` does not throw on `S` vs `(not S)`. The write path relabels the region a write
affects, and `settle` runs after every assert / retract / `forward-chain` / `recover`.
Belief at a context comes out of four steps. The write path and the settle run the first
two, and a read runs the last two at its reader:

1. **Relabel.** `jtms/relabel-region*` runs two least fixpoints over the affected region:
   `region-fixpoint` computes the members that are IN, then `region-classes` computes the
   defeat-class of each. No verdict enters either fixpoint, so a nogood's members keep
   their network labels whatever a reader decides.
2. **Find the nogoods.** A **nogood** is a set of believed sentexes that cannot all hold.
   Every family but one comes off the write-time candidate index
   ([Nogoods decided at the reader](#nogoods-decided-at-the-reader)): a negation pair, a
   tuple-mark nogood, a membership nogood, an `irreflexive`, `anti_symmetric` or arity
   nogood. The settle finds the remaining family itself. `clear-inherited!` empties the
   inherited clashes from the candidate index, so the discovery reads no verdict, and
   `discover-inherited!` records each inherited nogood whose members the network believes,
   with its vantages (`inherited/install-inherited!`). Every nogood is decided at each reader
   that sees it, in one context as across several. The inherited family is:
   - a stored claim against a **known-true claim reached by argument preservation**
     (`preserving-nogoods`), whose second side was never stored. `(largerThan dog cat)`
     asserted `{:strength :monotonic}` reaches `(largerThan chihuahua maine_coon)`, and a
     stored `(not (largerThan chihuahua maine_coon))` denies a claim with no handle, as a
     stored `(largerThan maine_coon chihuahua)` does under an `asymmetric` mark on
     `largerThan` or a super-predicate of it (`inherit/converse-claim`). The
     members are the stored claim and everything the reading rests on: the general claim,
     the declaration that permits the move, the relation edges the reach travelled, and
     any `(transitive R)` or `(symmetric …)` the reading hangs on. An inherited claim has
     no sentex to defeat instead of its reasons, so `decide/verdict` weighs that set as it
     weighs any other. Priority is the rebuttal range. Discovery reads the settle's
     region and what it re-opens, since a `genl` edge changes what reaches whose tuple
     without either side going near the region, and carries a standing clash whose
     inputs did not move ([The inherited-clash memo](#the-inherited-clash-memo)). A KB
     whose `:preserving` roster is empty pays one `empty?`. [inherit.md](inherit.md) has the readings, and why a
     `:default` general claim produces no pair.

   The argument constraints are not nogood sources; the table in
   [What qualifies as a nogood](#what-qualifies-as-a-nogood) gives the reason.
3. **Decide at the reader.** `res/withdrawal` asks `decide/losers` for the nogoods a
   reader sees, and `decide/verdict` resolves each from its members' **defeat-classes**,
   read over the whole member set:
   - **a unique weakest member** → that member loses at this reader. This reader
     withdraws it, every other reader decides the nogood from its own view, and the
     network keeps the member IN. No solver. (Monotonic beats default.)
   - **a minimum shared by several, and defeasible** → a **dilemma**. Every member stays
     believed at `:default` and the set is reported by `contradictions`.
   - **a minimum shared by several `:monotonic` members** → irreducible; report it in
     `conflicts` (never throw).

   `decide/losers` decides in rounds. Each round forces the reader's `except` targets and
   the losers so far OUT (`jtms/grounded-in-region`), reads the members' classes over that
   region, and adds the new losers. The rounds stop at the first round that adds none
   ([A defeat is scoped to its vantage](#a-defeat-is-scoped-to-its-vantage)). The reader's
   withdrawn set is the losers together with every handle that rests only on one:
   `jtms/grounded-in-region` with the losers forced OUT. `res/withdrawal` caches the
   answer per reader in `:withdrawn` ([The withdrawal cache](#the-withdrawal-cache)).
4. **Read.** A read at context `C` subtracts what `C` withdraws from the network's labels:

   ```
   believed(C) = in − superseded − withdrawn(C)
   visible(C)  = believed(C) − except-hidden(C)
   ```

   `jtms/in?` answers `in − superseded`. `withdrawn(C)` is the set step 3 computes
   (`res/defeat-withdrawn-set`), and `res/believed-at?` answers `believed(C)`.
   `except-hidden(C)` is every target of a believed `except` visible from `C`, with every
   handle that rests only on such a target or on a loser. `res/hidden-fn` applies both
   sets.

Steps 1 and 3 run region-locally. A relabel is a belief fixpoint over the consequence
justifications, held to the affected region by [Locality](#2-locality), and a reader's
rounds walk the forward closure of what the reader withdraws. Finding a nogood reads no
justification edge. The negation pairs come off a write-time index, and whether some
context sees both members of a pair in two contexts is a walk over the `genlCx` lattice, so a `P` and a `(not P)` many contexts apart pair on the same terms
as two in one context. Locality is by **range**, and range cuts across the seven roles:

| range | what is in it | bounded by |
|---|---|---|
| support-graph-local | labels, the class fixpoint, the sweep | the affected region |
| lattice-ranged | nogood discovery — does some context see both members of a pair | the pairs the candidate index holds |
| query-ranged | the `exceptWhen` re-evaluation that fills `blocked` | the recheck queue's triggers |
| reader-ranged | a reader's verdict on a nogood, a visibility `except`, and the conclusions resting only on one | the withdrawn set's forward closure, per reading context, cached per reader between settles |

A protocol method's locality claim is about applying a set, never about computing one.

A default/default clash is **not** decided: defeat-class is the only axis
([There is no second axis](#there-is-no-second-axis)). Where one rule names the other's
case, [`exceptWhen`](exceptions.md) settles it structurally and no contradiction forms.
Where neither does (the Nixon diamond), the clash is a dilemma the engine reports.

No nogood the settle discovers reaches the `Solver` below
([defenses.md](defenses.md#a-settle-hands-no-nogood-to-a-solver)). The solver
`set-solver` installs is read by [`do/label`](solving.md) when no ASP backend is
reachable.

### What qualifies as a nogood

A nogood is a set the settle may resolve by defeating a member, so it has to survive
being acted on
([why the criterion is not "a member the detection reads through"](defenses.md#a-nogood-must-survive-being-acted-on)):

> **A nogood must stay derivable exactly as long as what it convicts stands.** Defeating
> its weakest member may dissolve it, but only by removing something the conviction was
> **about**. Inadmissible is a set whose defeat makes the clash undetectable while the
> content it convicted goes on standing.

The members and the reading, per source:

| source | members | read *through* | admissible because |
|---|---|---|---|
| negation, at the settle or the reader | the believed `P` and the believed `(not P)` | joint visibility — the reader sees both contexts ([Nogoods decided at the reader](#nogoods-decided-at-the-reader)) | no member supports the visibility verdict, and defeating either side removes one of the two claims the pair was about |
| a membership nogood, at the settle or the reader | the clashing memberships and denials alone, keyed on the **handle set**; the separations, covers and disjoint metatypes are read through and never members | the separating declaration or the cover, and the `genl` closure | no defeat this nogood licenses can unmake the reading that convicted |
| `preserving-nogoods` | the stored claim **and its reasons** — the general claim, the declaration permitting the move, the relation edges the reach travelled, any `(transitive R)` the reading hangs on | the same reasons, which here *are* members | defeating a reason withdraws the reach, which is what the pair was about, and the reason stays defeated |
| `arity`, at the reader | the offending tuple alone; for two related predicates, their bindings | the binding, read as storage ([Nogoods decided at the reader](#nogoods-decided-at-the-reader)) | the binding is on the forced-monotonic roster and goes OUT only by retraction, so no defeat unmakes the conviction |
| **not** `arg` / `genlArg` / `interArg` | there is no second sentex | the **absence** of a path — an open-world NAF judgement | nothing to weigh and no class to compare. A refusal at the entry point, a drop on the derivation path |

`nogood_admissibility_test` pins the first three rows: a definitional clash's `:nogood`
set holds the clashing sentexes and not the declaration that convicted them, and an
inherited clash's holds its reasons.

### The inherited-clash memo

`preserving-nogoods` keeps `{:stamp :mark :entries :seen}` in
`(reasoning/preserved-clashes kb)`. `:entries` maps a stored claim to its last answer (`discovery/preserving-entry`): the
nogoods, every context asked, and the defeat-class of every member. `:seen` holds each
asker's withdrawn set as that answer read it, and `:left` the sentences removed since the
call. A settle republishes the entries, which is
O(standing) bookkeeping, and asks again only where an input moved. The region is what the
touched window recorded since `:mark`, the mark taken before the last call's questions, so
the second pass of a settle asks only what the first pass moved, and not the settle's
whole window again; a mark from an earlier window reads that whole window. An image
install drops `:mark` (`reasoning-image/install-from!`): the installed network starts its
window at generation 0, where the writer's mark would read as a mark of that window. The
inputs:

- **a member.** An entry is asked again when a member other than the stored claim is OUT
  or holds another class, which also covers a supersession flip no region shows. The
  stored claim's own belief is not an input, since its question reads the tuple's other
  claims. An entry whose stored claim is OUT publishes nothing and stays.
- **the reading's vocabulary.** A handle in the region, or one whose withdrawal at an
  asker moved (`res/withdrawn-set` against `:seen`), re-opens the whole stored extent of
  every predicate a non-claim channel of `inherit/moved-channels` names: a declaration, a
  relation edge the reach can cross, a `(transitive R)` or a mark. A `genl` edge between
  predicates re-opens every preserved predicate above either end.
- **a claim.** A moved claim re-opens the stored facts it reaches
  (`inherit/claim-reach-extent`), and not the extent, when it can change an answer:
  believed and known-true, since `clashing-claim` reads known-true claims alone, or moved
  in the region and of a predicate holding an entry, since every entry is asked from the
  vantages `inherit/denial-contexts` reads off claims of every class. A known-true claim leaving is a member of every entry
  it answers, and a reader's verdict never withdraws known-true content.
- **the stamp.** The `genlCx` generation, the contexts each flat-cache entry is asserted
  from (`tax/flat-contexts`) and the `except` roster, compared as one value. When the stamp
  moves, every entry is asked again.
- **a deleted record.** `integrate/sentex-removed!` records a departing sentence under its
  handle in the memo's `:left` while an entry stands (`discovery/note-removed!`). A region
  handle with no record is read from `:left` through the two channels above: as
  vocabulary, and as an OUT claim moved in the region. A retracted `genl` edge between
  predicates is neither a member nor a stamp input, so its `:left` sentence is the only
  input that re-asks the clash the edge carried, whether the edge carried an `asymmetric`
  mark down (`tax/props-over`) or made a sub-predicate's claim the super's
  (`inherited_clash_oracle_test`). A region handle with neither a record nor a recorded
  sentence re-asks every entry.

`recover`'s settle has the whole store as its region and carries nothing, so its
discovery asks the preserved predicates' stored extents, read off the index, and reads
no record of any other sentex.

A stored claim asked and finding no clash is kept as an entry with no nogoods in two
cases. While `inherit/denial-contexts` names a claim that would deny it in a reader seeing
both, the `genlCx` edge that makes such a reader moves the stamp and asks it again. While an asker
reads something withdrawn, the next settle clears the standing nogoods, and its withdrawal
diff asks the claim again. A stored claim with no entry has no clash in any reader the
lattice could add, and the region and the re-opened facts are the writes that can give it
one.

`*incremental-preserving*` bound false carries nothing and re-opens the whole extent for
every moved claim, the reference `inherited_clash_oracle_test` compares against step by
step; its streams do not generate the supersession shape. The same test replays the set a
stream leaves stored into a fresh KB, since both of those arms ask through
`preserving-entry`. `lein perf`'s
`inherited-clash-arbitration` and `inherited-clash-arbitration-split` hold the per-assert
cost against the standing set, and `inherited-entry-retraction` the per-retract cost
against the carried entries.

### A revived datum is a datum the agenda has not seen

A revival is a **relabel**, which brings back everything still stored: a premise
restored by `preview`'s rollback, or a derivation an unblocked justification or a
returning antecedent gives back, and the conclusions resting on it. A handle a reader's
verdict gives back at its own context is read as a revival too (`readings/reader-moves`). A
relabel cannot bring back a conclusion that was
never derived. While a datum is OUT, `chain/*matcher*` does not match it, so a rule's
*other* antecedent arriving meanwhile joins against nothing and attempts no firing.

No other settle instrument finds that firing afterwards. It holds no justification, so
it is in no blocked set for `released-rules` to read, and it reached no placement, so it
left no entry for `released-refusals` to re-ask ([exceptions.md](exceptions.md)). A record
covering it would need one entry per **non-match**, which nothing bounds, where the
refusal record holds one entry per firing a rule declined to place. So `settle` reads the
trigger where the belief moved: it re-seeds the revived datums onto the chaining agenda
(`settle/revived-seeds`), and the ordinary fixpoint does the rest.

A relabelled region is mostly datums that did not move, and everything the window
*created* reads as newly believed too. The JTMS keeps four sets per window, cleared
together when `settle` finishes with them:

| | |
|---|---|
| `touched` | the relabelled regions: a superset of every handle whose belief could have moved |
| `touched-in` | of those, the ones already believed when the window first relabelled them |
| `touched-new` | the ones whose **node this window created** |
| `touched-out` | the ones a forced-set change took from IN to OUT ([The forced-monotonic roster](#the-forced-monotonic-roster)) |

`jtms/revived` is `touched` minus `touched-in` and `touched-new`, plus `touched-out`,
filtered to what is believed now. A datum a declaration took OUT and a later write in the
same window put back IN is in `touched-in` when it was believed as the window opened, and
a partner that arrived while it was OUT joined against nothing, so `touched-out` names it
for the re-seed. The change feed
and `preview` read `touched-in` to say which way each handle moved ([feed.md](feed.md));
`touched-new` exists only for `revived`. Without it every asserted fact and every
conclusion drawn from one would be re-seeded, since each is in its settle's region,
believed at the end of it and not at the start, and the window would be chained twice.
The distinction exists only at the moment of creation: by the time the relabel runs, a
new node and one that has been OUT for a hundred settles are both unbelieved nodes about
to become believed.

A reader that asks the window more than once in one settle takes a mark
(`jtms/touch-mark`) and reads what the window recorded after it (`jtms/touched-since`): a
datum relabelled again after the mark is in that answer although `touched` held it
already, which a set difference over `touched` would drop. Each mark is the reader's own,
and `reset-touched!` outdates every mark, after which one reads the whole window. Two
readers mark: the inherited family's discovery ([The inherited-clash
memo](#the-inherited-clash-memo)) and the withdrawal cache ([The withdrawal
cache](#the-withdrawal-cache)).

The seeds are **datums**, so re-chaining one costs what asserting it costs: a join per
rule keyed by its predicate. Seeding the *rules* instead joins each rule over its whole
extent. For a two-antecedent rule, re-chaining one datum is linear in the partner's
extent and re-chaining the rule is linear in the product of the two extents.

The re-check triggers are one idea over several populations: the rules a taxonomy edge
queued, an aggregate's moved value, a refused firing's recorded bindings, a relabelled
revival, and the spelling an un-merge gives back. Each has an instrument sized to its
own population, and they split on granularity. The three that can name a **datum** (a
released refusal's re-derived conclusion, a relabelled revival and an un-merged
spelling) hand it to `settle/rechain-seeds` and pay what asserting it pays. The two that
cannot (a rule queued with `:all` by a taxonomy edge, and an aggregate whose bound value
moved) have only the rule, so they take the extent-wide re-join through
`rechain-exception-rules` and are narrowed at the trigger instead.

A datum is seeded once per settle however many passes run, and a datum that revives and
is defeated again inside one settle is never seeded: the set is read after the resolve,
so it describes where the pass landed rather than what it passed through. A pass that
revived something is **productive** even when the blocked set stands still, as an
aggregate's is, or the loop would converge having derived nothing. So is a pass whose
resolution defeated a datum a watched rule's `unknown` or exception reads
(`readings/released-by-defeat`, [naf.md](naf.md)), or whose standing verdicts took a
member OUT or gave one back (`readings/released-by-verdicts`): the pass re-chains the
released rules whether or not anything was queued. A **rebuild** stands
aside (`settle/*rebuilding?*`): `recover` relabels the whole graph, so most of what it
believes reads as newly believed, and the stored justifications it replays already carry
every derivation.

#### The other half: a spelling an un-merge gives back

One kind of revival is not in the region at all. A datum displaced by an equality merge
is OUT while its **twin** joins in its place, so a partner arriving during the merge
concludes at the twin's spelling. When the equality stops being believed (retracted, or
a derived one's support withdrawn), the twin is swept and the displaced spelling comes
back. The conclusion has to be made again at the surviving spelling, or the KB believes
both antecedents of a forward rule and holds neither spelling of what they conclude.

Supersession changes belief with **no relabel behind it**: a superseded datum stays in
`:in` for `valid?`'s purposes, because its twin is justified *by it* and forcing it OUT
would leave the merge believing neither spelling ([equality.md](equality.md)). So the
flip is in none of the three window sets, and `jtms/revived` cannot see it.

`special/refresh-supersessions` runs on the write path, and it records each flip with the
entry it replaced (`special/take-supersession-moves!`), which `settle-finish` reads once
the loop has converged. So the spellings a flip gives back go into
`settle/*unmerged-sink*`, and **`settle` re-seeds them and settles again**, as `core/retract!` settles twice around its own re-derivation.
Rounds are bounded by `max-unmerge-rounds` (8); two is the structure of every real case,
and reaching the eighth is logged as a bug rather than looping. Two other designs, moving
the reconcile into the settle loop and a re-enter signal from `settle-finish`, cost more
elsewhere: [why](defenses.md#an-un-merge-re-seeds-through-a-second-channel).

### The set-membership states a node can hold

A node carries two independent descriptions, one persistent and one per-settle. Its
**belief state** is read from the datum-keyed set `:in` and the `:superseded` map, and it
survives across settles. Its **window position** is read from `:touched`, `:touched-in`
`:touched-new` and `:touched-out`, and `reset-touched!` clears those four at
`settle-finish`, so a window position exists only during the settle that wrote it.
`:blocked` and the `:void` forced set are keyed by justification id rather than by datum,
so they name no node state of their own; each reaches a node through `valid?`, which reads
it in the fixpoint. A node is OUT exactly when it has no valid derivation or is in the
`:out` forced set.

Reported belief — the answer `in?` gives — is `:in` minus `:superseded`, because a
superseded spelling stays in `:in` to keep its rewritten twin's justification valid even
though it no longer matches. The invariant `superseded ⇒ :in` leaves three belief
states:

| belief state | in | superseded | `in?` |
|---|:--:|:--:|:--:|
| believed | ● | | yes |
| superseded | ● | ● | no |
| no derivation | | | no |

A `believed` node is a premise or a datum with a valid justification, and not in the
`:out` forced set. A node with `no derivation` has no premise and no valid justification,
or is held OUT: a retraction sweep deletes one that is no premise, and one still present
in `:nodes` is one a sweep has not yet reached or a premise the roster holds OUT.

The **revival slot** of the window is `:touched` without `:touched-in` or `:touched-new`
— a datum this settle relabelled that was neither believed at the settle's start nor
created by it — together with `:touched-out`. `jtms/revived` reads that slot filtered to what is believed now, so a
believed node in the revival slot is a `revived` one. A believed node created this settle
sits under `touched-new`, and a believed node the settle relabelled without moving its
label sits under `touched-in`. A reader's verdict moves no node state: it withdraws a
handle from a reader's view (`res/withdrawal`), and the settle publishes that move beside
the window ([The published window](#the-published-window)).

### Which entry point the content came through

One logical situation, one representation: the nogood above, however the content
arrived. Neither the path the content came in on nor the members' classes decide whether
it is stored:

| where the clash arrives | members all `:monotonic` | a `:default` member |
|---|---|---|
| a **rule firing** (`place-conclusion`) | placed; a hard clash in `conflicts` | placed; the unique weakest is defeated with a `why-not`, a tie is a dilemma |
| an **`assert`**, disjointness / functionality / a refuted cover / asymmetry / anti-transitivity | stored; a hard clash in `conflicts` | stored; decided as a firing is |
| an **`assert`**, irreflexivity / antisymmetry that does not merge | stored; a hard clash in `conflicts` | stored; each reader decides it ([Nogoods decided at the reader](#nogoods-decided-at-the-reader)) |

The declaration, the functionality mark, the cover and the `genl` steps a conviction reads
are the nogood's grounds: read through, never weighed, and never a reason to refuse. A
known-true opposing claim beside a known-true declaration therefore makes a hard clash
rather than a refusal, whichever member arrived last.

A self tuple `(P a a)` of an `irreflexive` `P`, and a converse no equality could
reconcile under an `anti_symmetric` `P`, are the last row. Neither is decided by the
settle: a reader decides it when it reads, in either arrival order, so a late mark takes a
`:default` self tuple OUT at every reader that reads the mark
([Nogoods decided at the reader](#nogoods-decided-at-the-reader)).

A firing has no caller to refuse, so there the choice is between dropping the
conclusion — no sentex, no justification, and `why-not` reduced to `:not-stored` — and
placing it for `settle` to weigh. Placing it is what gives the loser a reason, and the
entry point makes the same choice for a writer.

The **retroactive** half runs the same way. A declaration arriving *after* the content it
convicts — what an import routinely does — reads no membership: the candidate index keeps
every term holding two memberships, or a membership and a denial, and a reader reads the
term's nogoods through the declarations it sees
([Nogoods decided at the reader](#nogoods-decided-at-the-reader)). The weaker side is
defeated, or an equal-strength set is reported by `contradictions` or `conflicts`, so
belief does not depend on whether the schema or the facts arrived first, and a recover of
the same records decides the same pairs. A pair only a common descendant context sees is
decided there. A term **joining** a disjoint metatype is a declaration too, and the only
one the taxonomy rather than the sentence identifies ([taxonomy.md](taxonomy.md)).

**One retroactive half is an inference rather than a nogood.** `(functional P)` arriving
after two `:monotonic` symbol values for the same first argument does not convict either
of them — it *merges* them, so `special/equate-existing` runs it exactly as
`derive-functional-equalities` runs the same inference on the arriving fact
([equality.md](equality.md)). `anti_symmetric` is the same shape: a believed `:monotonic`
converse `(P b a)` beside a `:monotonic` `(P a b)` forces `(equals a b)` and merges,
`special/derive-antisymmetric-equalities` and `antisym-equate-existing` reaching it from
the fact side and the declaration side. A symbol pair with a `:default` member is a
nogood under either mark: the settle decides a `functional` one as above, and each reader
decides an `anti_symmetric` one ([Nogoods decided at the reader](#nogoods-decided-at-the-reader)).

Content the engine stores on its own behalf is admitted as a firing's conclusion is
(`checks/derivation-violation`): the decontextualization lift's copy, the equality
migration's twin and the argument-type mint. A clash one of them forms is stored and
decided at each reader, since refusing it would read stored content and make the stored
set depend on the arrival order. Only the gate on what `abduce` may assume refuses a
clash (`checks/constraint-violation`): a hypothesis is never stored.

### A nogood is a set: `anti_transitive` has three members

`(anti_transitive P)` says a two-step chain forbids the direct step: `(P a b) ∧ (P b c) ⇒
¬(P a c)`. The three cannot all hold and no two of them are the clash, so the conviction
is one nogood with three members:

- **Discovery** reads the chains a step is a member of when the step is stored, in each
  of its three roles — the direct step, the first step and the second step
  (`tuple/found-for`) — so the chain enters the candidate index whichever step arrives
  last.
- **Decision** is `decide/verdict` over the whole member set: a unique weakest member is
  defeated, a defeasible minimum shared by several is a dilemma, and all-monotonic is a
  conflict. Three equal defaults are one three-sided dilemma.
- **Reporting**: `contradictions` returns one entry whose `:sides` are three, and
  `(contradicts …)` names all three sentences in content order. `:handles` is not a pair.

The mark is read **up** the predicate hierarchy like every other constraint mark, so
`(anti_transitive parentOf)` convicts a chain spelled in `fatherOf`; the steps are read under
every predicate below the mark, so a chain written half at each spelling is one chain. A
step reachable **only** by argument preservation is not enumerated
([Where conviction is one-sided](#where-conviction-is-one-sided)). A self tuple
`(P a a)`, its own whole chain, is admitted, as an `asymmetric` predicate's is:
`anti_transitive` does not imply `irreflexive`. No predicate is declared both
`anti_transitive` and `transitive` ([taxonomy.md](taxonomy.md)).

### Which contexts can contradict each other

Two beliefs clash when **some context sees both**: their contexts have a non-empty common
down-closure (`tax/maximal-common-descendant-contexts`). Asking whether one context
`sees?` the other catches only a comparable pair and exempts every sibling pair; two
incomparable contexts can share a descendant, and from there `X` and `(not X)` are both
visible. The common-descendant test generalises `sees?` (if K sees Y, K is itself a
common descendant), so it detects everything `sees?` would. A reader deciding a negation
pair asks the same question of its own ancestor set: it sees both contexts.

A **definitional** clash reads the same rule from the other end. A disjointness needs the
separation and the `genl` edges it closes under to be visible too, which is a scoped
check rather than a set test, so each reader asks it over its own ancestor set
(`membership/term-nogoods`).

### A defeat is scoped to its vantage

A nogood has **vantages**: the most general contexts that see every member, and for a
definitional clash the declaration as well. **Every reader decides each nogood it sees
from its own view** ([reference.md](reference.md#decisions), decisions 2 and 3): a
defeated member is disbelieved at the readers that decide against it and nowhere else,
and the network keeps it IN. A context's belief therefore depends on its own ancestor set
and on nothing a spec context holds. The families of
[Nogoods decided at the reader](#nogoods-decided-at-the-reader) are found at the reader,
in one context as across several. `preserving-nogoods` takes the most general contexts
that see the stored claim's own context and the reading that denies it, and the settle
records every inherited nogood whose members the network believes with its vantages in
the candidate index (`inherited/install-inherited!`), in one context as across several,
storing no verdict there: each reader at or below a vantage decides it.

```
CxA            (cat Rex)   :default
 └─ CxD        (dog Rex)   :monotonic       (genlCx CxD CxA)
(disjoint dog cat) is visible from both
```

CxD is the only context that sees both memberships, so CxD is the vantage. A read from
CxD finds `(dog Rex)` and not `(cat Rex)`. A read from CxA finds `(cat Rex)`, because CxA
does not see `(dog Rex)`.

**A reader sees the grounds as well as the members.** A definitional clash is its members
and what separates them — a `disjoint` declaration, the `genl` path up to a separated
type, a `functional` or `asymmetric` mark — so the most general context holding the whole
clash can sit below the members' maximal common descendant:

```
CxA  (t1 Pip) :monotonic     CxB  (t2 Pip) :default     CxDecl  (disjoint t1 t2)
CxW sees CxA and CxB
 ├─ CxX sees CxW
 └─ CxV sees CxW and CxDecl
```

CxW reads no separation and convicts nothing. CxV reads all three: CxV and every context
below it believe `(t1 Pip)` alone, while CxW and CxX believe both memberships. Each reader
reads the separation over its own ancestor set (`membership/term-nogoods`), so the readers
that see CxDecl decide the pair and no reader above them does, and
`membership/membership-vantages` names CxV as the most general context deciding it. No write
reads the contexts below CxW; `lein perf`'s `per-reading-vantages` holds an assert flat in
them. Two members stored in one context have that context as their lowest, and a
separation declared only below it is decided by the readers below that read it
(`reference_test/a-declaration-below-a-pair-stored-in-one-context-decides-it-there-in-every-order`).

**A vantage sees every member, and some clashes have more than two.** An `anti_transitive`
chain is a triple, and a context seeing two of its steps reads no clash:

```
CxA  (nearP Aa Bb)     CxB  (nearP Bb Cc)     CxC  (nearP Aa Cc)
CxAB sees CxA and CxB, CxBC sees CxB and CxC, CxAC sees CxA and CxC
 └─ CxW sees CxAB, CxBC and CxAC
```

CxW decides the chain, and CxAB, CxBC and CxAC each keep both steps they see: the chain
is a candidate a reader decides when it sees all three members
([Nogoods decided at the reader](#nogoods-decided-at-the-reader)), and
`reference_test/a-chain-in-three-contexts-is-decided-where-one-reader-sees-it-whole-in-every-order`
holds it in every arrival order. An inherited clash has more than two as well: a stored claim denied by
a known-true claim read by argument preservation rests on the general claim, the
declarations and every `genl` edge the reach travels, each possibly in its own context.
`inherit/denial-contexts` names those contexts, read from the whole KB, and
`preserving-nogoods` asks the clash from the most general contexts that see all of them ([inherit.md](inherit.md#a-contrary-claim-against-a-known-true-one-is-a-contradiction-and-is-reported)).

**A reader decides in rounds** (`decide/losers`, [reference.md](reference.md#the-function)
item 8). It reads the families of [Nogoods decided at the reader](#nogoods-decided-at-the-reader),
the inherited clashes whose vantage it sees among them. Each
round forces the reader's `except` targets and the losers so far OUT
(`jtms/grounded-in-region`), reads each member's class over that region
(`jtms/classes-in-region`), decides every nogood whose members the reader still believes,
and adds the unique weakest `:default` members. The region grows from round to round, and
a nogood with no member in it reads the beliefs and classes it read in the round before,
so a round after the first decides only the nogoods with a member in its region and keeps
the earlier verdict on the rest. A round whose new losers include a ground
(`tax/derives-from?`: a `genl` edge or a flat-cache entry) adds those alone. Once the
reader withdraws a ground or an equality supporter, each definitional nogood is re-asked at the reader before it is
decided (`clashes/reread-at`, which `res/*reread*` holds): the check the discovery ran is
asked against a detached copy of the taxonomy (`tax/detached-copy`), with
`res/*provisional*` answering what the rounds have withdrawn so far, so the closures it
walks are memoized in the copy and never in the live taxonomy, and the `genl?` answers,
filtered edges, separation frames and each member's violations one nogood reads serve the
rest of the round. A
nogood the reader no longer convicts stays dropped, since a check finds no more for seeing
less. The re-read reads the reader's withdrawal only through the grounds, the members and
the equality partition, whose scoped election decides which spellings the reader retires
(`res/without-retired`), so a later round re-asks the definitional nogoods only when it
withdraws another ground or equality supporter (`tax/equality-supporter?`). A loser
withdraws no equality supporter, since the equality relations are on the
forced-monotonic roster; an `except` withdraws one.
The rounds stop at the first that adds no loser, and no round takes a loser back.
The reader's answer holds its losers and its verdict on every nogood it decides
(`res/verdicts`).

```
CxUniverse   (genl chi thing) (genl dog thing) (genl cat thing)  (disjoint dog cat)
 ├─ CxA      (genl chi dog)                 :default
 └─ CxD      (not (genl chi dog))           :monotonic
      CxB sees CxA and CxD:  (chi Kit) :default   (cat Kit) :monotonic
```

CxB is the vantage of both nogoods, and CxB's rounds decide both: the edge against its
denial first, since the edge is a ground, and the edge goes OUT. CxB then withdraws a
ground, so it re-asks the membership clash (`clashes/reread-at`), finds no separation
between `chi` and `cat`, and decides nothing. A reader below CxB that sees the pair and
the edge decides the same way in its own rounds. CxB believes both memberships, and
`contradictions` reports nothing, in every arrival order and whatever number of passes the
settle runs (`reference_test/a-second-settle-pass-leaves-the-release-lattice-reading-unchanged`).

**A read applies a reader's verdicts through `res/hidden-fn`**, the predicate every
belief-filtered read with a concrete context asks for the visibility `except`
([contexts.md](contexts.md)). The predicate reads a handle as withdrawn from reader K in
three cases: a believed `except` visible from K hides it, K takes it OUT as the loser of a
nogood K decides, or every justification it has rests on a handle withdrawn for one of
those two reasons. `res/withdrawal` computes the third set as `jtms/grounded-in-region`
with the first two forced OUT, so a consequence follows the reader. A forward rule `(cat
?x) ⇒ (meows ?x)` stated in CxA stores `(meows Rex)` in CxA; a read from CxA finds it and
a read from CxD does not. Inside a re-read (`res/*provisional*`) the reader being
decided answers what its rounds have withdrawn so far instead. `believed?` takes a
context and applies the withdrawal, and a read with no context reads a sentex at its own
([A read with no reader](#a-read-with-no-reader)).

**The taxonomy's closures apply it too.** A `genl` or `genlCx` edge is held up by stored
supporters, and a scoped read of a relation asks the KB per supporter whether the reader
believes it (`res/supporter-believed?`, installed by `kb/attach-visibility!`). That
predicate reads the same two withdrawal kinds `hidden-fn` reads, so a context that
disbelieves `(genl chi dog)` stops reaching over the edge: `genl?`, `isa?`, `genls`, a
match that climbs the hierarchy and a `transitiveInArg` claim preserved along it all
answer there the way `believed?` of the edge answers. Without that the two halves would
disagree about one KB from one context — `believed?` false and `ask?` true — which is the
disagreement `res/believed-at?` exists to prevent.

The recursion that shape invites does not close. Every ancestor-set read inside the
withdrawal answer goes through `tax/context-up-global`: `except-hidden-fn`,
`visible-exception-index` and `withdrawal*` each name it, and the region walk is
`jtms/grounded-in-region`, which reads justifications and no taxonomy. So a filtered
`genlCx` walk asks a question the **unfiltered** genlCx closure answers, for the same
reason exception evaluation reads that closure ([taxonomy.md](taxonomy.md), "Reads are
scoped by the asking context").

`relation-filter-active?` stays the gate in front of all of it: a KB that stores no
`except` and holds no candidate of a decided family never asks the
predicate at all, and one whose
withdrawable handles support no edge of the relation being read does not either.

**The discovery reads no verdict.** A settle empties the inherited clashes before each
discovery (`discovery/clear-inherited!`), so a pair one reader's verdict hides from the context
that asks it is still found for a reader below that context whose view keeps it. The
discovery therefore reads the relation as the network holds it, and each reader re-asks
what a verdict of its own dissolves.

**A verdict binds no reader below the vantage against its own view.** A reader below the
vantage that sees a denial, an edge or an `except` dissolving the clash believes what the
vantage took OUT:

| where `(not (genl chi dog))` sits, with `(chi Kit)` and `(cat Kit)` in CxB | CxC below CxB believes `(chi Kit)` |
|---|---|
| CxC, below the vantage CxB | true |
| a CxD that CxB sees | true |

`scoped_defeat_test`'s release tests pin both rows in every arrival order, the retraction
of the denial and the `except`.

An `orthogonal` exempts its pair from every separation only at the readers that see it
([taxonomy.md](taxonomy.md)): written below a vantage, it releases the pair there and
below, and the vantage decides the pair as it reads it.

#### Vantages that disagree

A nogood can have several vantages, when the contexts that see every member have more than
one maximal element. Each one decides it from its own view, and two of them can defeat
different members: a vantage that reads one member's monotonic support as withdrawn ranks
that member lower than a vantage that reads the support whole.

```
CxUniverse
 ├─ CxA        (cat Rex) :default, and :monotonic through (mono_cat_src Rex)
 ├─ CxB        (dog Rex) :default, and :monotonic through (mono_dog_src Rex)
 ├─ CxHide1    (except (sentexHandle <(mono_cat_src Rex)>))
 └─ CxHide2    (except (sentexHandle <(mono_dog_src Rex)>))
CxW1  genlCx CxA, CxB, CxHide1      CxW2  genlCx CxA, CxB, CxHide2
CxZ   genlCx CxW1, CxW2
(disjoint dog cat) is visible from every context
```

CxW1 reads `(cat Rex)` as a default and `(dog Rex)` as monotonic, so it defeats `(cat
Rex)`; CxW2 reads the pair the other way and defeats `(dog Rex)`. A read from CxW1 finds
`(dog Rex)` and a read from CxW2 finds `(cat Rex)`. CxZ sees both `except`s, reads both
members as defaults, and ties: it believes both, and `(contradictions kb CxZ)` reports the
pair. No reader takes a verdict from a vantage; each reaches its own.

`contradictions` reports a nogood whose vantages defeated different members as a dilemma
with `:vantages`, the `{vantage handle}` map of what each vantage decided
(`clashes/read-clashes`), read with the other reports. `(contradictions kb context)` keeps an entry for a reader that believes every
member and sees a vantage that weighed it, which is the reading `believed?` gives that
reader for each member.

**A verdict blocks no firing.** Derivation blocking reads the `except` roster alone
(`res/except-hidden-fn`). A conclusion resting on a member a reader takes OUT is stored,
and the read withdraws it from that reader. An `unknown` or `exceptWhen` is asked at the
conclusion's placement context and reads that context's verdicts, and a verdict that
moves posts the re-check of the rules watching the member ([naf.md](naf.md)).

**The published window holds what a reader's verdict moved**
([The published window](#the-published-window)).

#### A read with no reader

A read that names no context answers belief at the handle's own context: what
`res/believed-at?` answers for the context the sentex is stored in, with that context's
verdicts applied and the `except` roster not applied. Every settle records it: the
readers `readings/reader-moves` reads keep the handles withdrawn where they are stored, and
their union is `:own-readings`' `:own-out`, which `res/own-hidden-fn` reads. `in?` and
`believed`, `types-of` and `isa?` with no context, the extent fns' `{:believed? true}`
option and `why-not` all read it. An unscoped read therefore never believes what no
context believes.

- **The unscoped closures and flat caches.** A supporter withdrawn at its own context
  leaves the `genl` and `genlCx` closures, the equality partition and the flat caches
  (`:own-readings`' `:own-out`, applied by `special/reconcile-belief-change`), so `genl?`,
  `disjoint?`, `same-class?`, `inverse-of` and every other taxonomy read with no context
  skip it. A verdict moves no label, so each settle pass reconciles the caches over the
  handles whose own-context belief moved (`special/reconcile-own-withdrawals!`) after its
  resolution, and treats them as it treats a relabel: a handle given back is revived, one
  withdrawn departs (its `genl` edges re-join a second route, and a firing that named it
  is re-routed for its reader, `reroute/lost-firing-seeds`), each posts the re-check of the
  rules watching it, and a mint it subsumed is drawn or withheld again. `settle-finish`
  repeats the reconcile, to a fixpoint of at most four rounds, before it files the reports
  and the window.
- **A read with no context and no reader to fan over** (`vantage/answers` with nothing to
  witness, `ask-within`) binds `res/*unscoped-own*`, under which `hidden-fn` of a variable
  context is `res/own-hidden-fn`. The engine's own unscoped joins bind nothing and read the
  network, verdict-free.
- **A variable context** reads jointly ([contexts.md](contexts.md)): an answer stands when
  some reader believes every fact it rests on, and post-hoc placement keeps a placement
  only where each supporter some reader can withdraw is believed.
- **`why-not`** answers `:defeated` for a loser its own context takes OUT, with the
  stored sentences opposing it under `:contradicted-by`. A sentex IN in the network and
  withdrawn where it is stored only by resting on a loser answers `:unsupported`, with the
  antecedents `in?` answers false for under `:missing`, or `:withdrawn`, with the losers
  its context decides under `:withdrawn-by` (`res/losers-seen`), when some justification's
  antecedents are each believed where they are stored.

`belief-status` reports the network label as `:in?` and the withdrawal from its context as
`:withdrawn?` and `:scoped-vantages`. A backward chainer drops a rule-derived answer its
query context takes OUT (`res/defeated-answer?`), so a rule cannot re-derive for that
reader the sentence the reader disbelieves.

#### The withdrawal cache

`:withdrawn` holds each reader's withdrawal and the roster the taxonomy's scoped reads
filter by (`res/supporter-filter-roster`), each entry with a watch: the handles its answer
reads. A reader's watch is its region, the `except` handles its ancestor set sees, and the
members and marks of the nogoods it decides
([Nogoods decided at the reader](#nogoods-decided-at-the-reader)). A reader that asks the
guarded firings placed above it again
([naf.md](naf.md#evaluated-in-the-placement-context-not-the-join)) keeps the guarded rules
it asked beside the watch. The roster's watch is
the forward consequence closure of every `except` target, standing nogood member and
candidate of a nogood a reader decides. At each point the settle moves the network,
`res/reconcile-withdrawn!` drops an entry whose watch meets a handle the touched window
recorded since the cache's mark, a handle one of that handle's justifications rests on, or
the conclusion of a justification resting on that handle. The mark is the one the last
reconcile or `res/clear-withdrawn!` took (`jtms/touch-mark`), before it moved the cache's
generation: an entry kept then was checked against every move before the mark, and an
entry installed since was computed after it. The next reconcile therefore checks an entry
a pass rebuilt against the moves after the last mark, and not against the earlier moves
the rebuild already read. It also drops an entry that asked a guarded
rule whose answer the moves can change (`res/guard-moves`): a re-check queued for the
rule (`res/note-guard-moves!`, from `special/mark-recheck`), a firing of it in the window,
or a handle in the window whose label moved on a predicate it watches. Every other entry
is kept. A gained or lost
justification puts its conclusion in the window, so those three reach every region member,
every justification into the region and every boundary label an answer reads.

The watch does not name the rosters, the supersession map, the meta-except count, the
`genlCx` generation, `decide/stamp` or the guarded rules stored. `reconcile-withdrawn!` compares those as a stamp, and a moved stamp
empties the cache (`res/clear-withdrawn!`), as every write of the inherited clashes does. A
settle clears and re-finds the inherited clashes, so a KB holding one empties the cache on
every settle. A kept entry is the answer a fresh recompute gives:
`order_independence_test/the-withdrawal-cache-answers-what-a-fresh-recompute-answers-in-every-order`
compares the two after every op of sampled arrival orders. The taxonomy's
supporter-visibility generation moves only when an entry is dropped or the cache emptied.

A forward chaining run between two settles reads the withdrawn consequences as they stood
at the last settle. `hidden-fn` asks the `except` targets themselves live.

#### The published window

A verdict moves belief with no relabel, so the touched window alone misses the flip.
`readings/reader-moves` adds those moves to the window `preview`, the consequence report and
the change feed read, as the belief each handle has at its own context.

A reader here is a context holding a handle of the forward consequence closure of the
standing members, `decide/reach-handles` (the candidates and the arity bindings) and the
firings of the guarded rules stored in a context with a context below it
(`res/guard-closure`). No other handle is withdrawn from any reader. `:own-readings` keeps, per such reader, the part of its
`res/defeat-reading` stored at that context and IN, and the watch that reading reads, with
an index from each watched handle to its readers. It keeps the closure too, which gains the
consequence closure of each handle entering `reach-handles` and of each conclusion in the
touched window resting on a closure member, and loses a handle whose record left.

**The bound.** A settle reads again only these readers:

- a reader whose watch holds one of `res/near-handles` of a handle in the touched window,
  the test `res/reconcile-withdrawn!` applies to a `:withdrawn` entry;
- a reader whose ancestor set holds the context of a handle that entered or left
  `reach-handles`. The candidate index part of `res/withdrawal-stamp` follows from those
  handles, their contexts and the taxonomy parts of the stamp, so a reader that sees none
  of them reads the same nogoods of the decided families;
- a reader of a handle the closure gained;
- a reader of a handle of the closure of a guarded rule whose answer at a reader moved,
  or of a guarded firing in the window (`res/guard-moves`).

A write whose candidates are k nogoods therefore reads the readers holding their closure,
and no other. Every reader is read again when the rest of `res/withdrawal-stamp` moves: a
declaration, a mark, a roster, the standing nogoods, or the `genlCx` or `genl` generation
reaches a reader through no handle. `lein perf`'s `verdict-window-write` holds a tuple its
own context convicts flat in the readers holding a withdrawn consequence elsewhere.

**Before and after.** The before-state is the last settle's reading of each reader. A hold
opened at the settle's start (`hold-belief!`) cannot give it: the write path moves the
candidate index, the marks and the taxonomy before the settle opens its hold, so a reader's
verdict has moved by then. Each reader read again is diffed against its last reading, and
the handles whose reading moved join the relabelled region and the supersession flips as
one `moved` / `was-in` pair. A moved handle outside the region was believed before when its
label is IN, it was not superseded when the window opened, and its last reading did not
withdraw it. A relabelled handle superseded when the window opened is left out of `was-in`
too, since `jtms/touched-in` records the label. The reading runs after
`res/reconcile-withdrawn!`, so it reads no `:withdrawn` entry the settle's last moves made
stale. An installed KB's first settle has no reading and publishes what its readers
withdraw as moved.

`feed_test/every-event-is-the-diff-of-own-context-belief-in-random-worlds` compares every
event with a diff of own-context belief over the whole KB, write by write and retraction by
retraction, and `feed_test/a-verdict-a-reader-reaches-arrives-in-every-order` holds a
consequence a reader's verdict withdraws and releases in `preview`, the consequence report
and the feed.

### Nogoods decided at the reader

`irreflexive`, `anti_symmetric`, `arity`, and most negation, `functional`,
`functionalInArg`, `asymmetric`, `anti_transitive`, `disjoint` and cover nogoods are
decided when a reader reads, not when a settle runs ([reference.md](reference.md#decisions), decision 16). The mechanism has four
parts, and a family decided this way adds one row to each (`vaelii.impl.decide`):

1. **A write-time candidate index.** `:nogood-candidates` holds, per family, the stored
   sentences that could be a member of one of its nogoods, recognized from the sentence's
   own arguments at the store and removal choke points (`decide/note-candidate!`). Its
   rows are a superset over every reader, so a family reads the unscoped closures there
   through one view (`decide/write-view`), and its reader half is handed none. Under
   `:self` is every ground binary self tuple. Under `:converse` is every ground binary
   tuple with a stored converse, found by a trie read of `(Q' b a)` under the tuple's own
   functor and under every predicate below an `anti_symmetric` mark on it or above it
   (`tuple/converse-functors`). A tuple of two symbols is read only while the KB holds an
   `anti_symmetric` mark, and the mark's arrival or a predicate `genl` edge bringing
   tuples under one offers the stored tuples to the index again. The index holds
   storage, not belief, so a converse arriving later, or a member reviving, finds its
   candidates without reading a tuple. `recover` rebuilds it with one fetch per stored
   record.
2. **Found at the reader.** `decide/nogoods-at` reads the candidates a reader's ancestor
   set sees and, for each, the marks the reader sees over its functor: a mark stated in
   the ancestor set, on the functor or on a predicate above it through the predicate
   `genl` edges stated there (`tax/genls-asserted-in`). Decision 10 forces those edges
   monotonic, so the stored edges are the reach. A length binding above a functor that
   binds none is read off the functor's global closure cut to the bound predicates
   (`arity/bound-above`), one cut for every reader of a settle, and the cut is checked
   against the edges stated in the ancestor set only when the ancestor set misses a
   context stating a `genl` edge, by one walk up from the functor that answers every
   predicate of the cut (`tax/genls-asserted-among`). A self tuple under a visible
   `irreflexive` mark is a one-member nogood. A converse pair under one visible
   `anti_symmetric` mark over both functors is a two-member nogood, unless both arguments
   are symbols and both members `:monotonic`, which
   `special/derive-antisymmetric-equalities` merges ([reference.md](reference.md#decisions),
   decision 6). The reader decides nothing of a merging pair and watches its members and
   marks, so a member's class moving re-decides the reader.
3. **Decided at the reader.** `decide/losers` decides every nogood whose members the
   reader believes, from the classes the reader reads (`decide/verdict`): the unique
   weakest member at `:default` loses, a `:default` tie is a dilemma, and an
   all-`:monotonic` nogood is a hard clash. It runs the rounds of
   [reference.md](reference.md#the-function) item 8. Each round forces the reader's
   `except` targets and the losers so far OUT (`jtms/grounded-in-region`), reads the
   classes over that region, and adds losers; the rounds stop at the first that adds none.
   The same rounds decide the settle's standing nogoods
   ([A defeat is scoped to its vantage](#a-defeat-is-scoped-to-its-vantage)). A loser joins
   the reader's withdrawal (`res/withdrawal`), so what rests only on it is withdrawn from
   that reader through the closure.
4. **Memoized per reader.** The losers ride the reader's `:withdrawn` entry, whose watch
   adds every member and mark the reader read, so a member or a mark that moves drops the
   entry. A mark, a candidate or a predicate edge arriving reaches the entry through the
   stamp instead: `decide/stamp` is the candidate index, the flat declaration caches with
   the contexts they are stated in (`tax/flat-contexts`) and the `genl` generation, and
   `res/withdrawal-stamp` carries it. A mark arriving therefore empties the cache and
   reads no tuple. The next read at a reader decides the nogoods that reader sees, which
   reads the candidates it sees once, and a warm read is one cache lookup. `lein perf`'s
   `irreflexive-mark-arrival` and `decided-warm-read` hold both.

`decide/live?` gates all four: a KB holding no candidate, or declaring no mark over one,
reads none of it, and `res/withdrawal` keeps its nil at three derefs.

**The arity family.** A binding is a roster sentence read as storage: `(arity P n)`, an
exact-arity class membership, a `variable_arity` membership or `(arityMin P m)`, kept per
predicate in the candidate index. `:arity` holds the stored tuples of every shape (a
functor and a length) that a stored binding of the functor, or of a predicate above it,
breaks at some context. The index tracks the handles of each shape up to 64 tuples and
reads a larger one off the functor posting when it becomes a candidate, so a binding
arriving over tuples of the right length reads none of them: `lein perf`'s
`arity-binding-arrival` holds it. A reader reads the bindings of a candidate's functor
that it sees, or, where there are none, the one length the predicates above it through
edges stated in its ancestor set agree on, and a candidate breaking that binding is a
one-member nogood whose marks are the bindings read. A reader reads that binding once per
candidate shape and the tuples of a shape it breaks alone, so a reader reads no record of
a tuple its functor's own length holds under a different length above it (`lein perf`'s
`held-shape-first-withdrawal`). A functor binding nothing reads the predicates above it
grouped by the exact lengths they store, the smallest group first, and stops at the second
length it sees. `:arity-pairs` holds the bindings of two predicates a `genl` edge relates
whose stored lengths differ, and a reader that sees both and the edges between them reads
them as one `:arity-descension` nogood. Where the ancestor set misses a context stating a
`genl` edge, the pairs of one lower predicate are checked off one walk up from it
(`tax/genls-asserted-among`), kept for every reader of the settle that states the same
contexts. A length arriving recomputes the candidates of the functors below it that did
not hold it yet, and a binding or a `genl` edge leaving those of every functor below it;
either changes the stamp ([taxonomy.md](taxonomy.md#arity)).

**The negation family.** A body stored in both polarities (`:opposed`) keeps an entry in
the candidate index: the handles and contexts of its stored `B` and `(not B)`, read with
two trie reads under a variable context whenever either polarity is stored or removed. A
pair of a `(not B)` and a `B` is a two-member nogood at every reader that sees both, in one
context or in two, and its members are under `:negation`;
a reader reads the entries and no body, so a `genlCx` edge arriving moves the stamp and
reads none.
`lein perf`'s `negation-reader-write` holds an unrelated write flat in the pairs stored, and
`negation-reader-warm-read` a warm read. A pair whose body is a `genl` edge or a type
membership (`(M t)`, from which a disjoint metatype reads a separation) is a ground of the
membership families, so a reader's rounds apply it first, and a membership nogood found
through the ground is read again once the reader withdraws it. A verdict of the reader's
pairs moves with no relabel when a pair forms or dissolves, when a member's class moves
and when a `genlCx` edge moves the joint views, and `readings/released-by-negations` posts
each such body's two sentences to the re-check queue and re-chains the rules watching
them, as `released-by-verdicts` does for a standing member.

**The tuple-mark family.** A tuple under a `functional`, `functionalInArg` or
`anti_transitive` mark on its functor or above it reads, when it is stored, the stored
tuples its own arguments name (`tuple/found-for`): for each mark the tuples of the
predicates below the mark that agree with it on the determinant, every position but the
marked one, one trie read of `(P a ?v)` or one intersection of argument roots; and for
`anti_transitive` the steps sharing an argument with it. A determinant holding two
fillers is kept with its members and their contexts, and a determinant already kept
takes a new tuple with no read, so an empty or a wide determinant is read once. A
determinant member is a candidate when a member with another filler sits in a context
some context sees together with its own, so fillers no context sees together cost no
reader anything; `lein perf`'s `functional-in-arg-empty-determinant-sweep` holds that
case flat. An `asymmetric` converse is a stored converse pair (`:converse`) read under
the `asymmetric` marks. A mark arriving, or a predicate `genl` edge bringing tuples under
one, offers the stored tuples beneath the marked predicate to the index again
(`special/offer-marked-existing`, `special/offer-marked-under-edge`). A reader reads a pair
under a mark on the determinant's predicate that it sees over both functors as a
`:functional` nogood, a chain under one `anti_transitive` mark over every functor as an
`:anti-transitive` one, and a converse pair under one `asymmetric` mark as an
`:asymmetric` one. Two symbol fillers both `:monotonic` merge
(`special/derive-functional-equalities`), and two fillers one class at the reader form no
nogood. Which contexts see two members together is read off the unscoped `genlCx`
closure, and a `genlCx` edge moving reads it again over the index (`tuple/sync-tuples`). `lein perf`'s `tuple-mark-determinant-write` holds a tuple's
arrival flat in the tuples of other determinants, and `tuple-mark-warm-read` a warm read.

**The membership families.** A `disjoint` nogood is two memberships of one term whose types
a separation the reader sees holds apart, and a cover nogood is a membership under a
cover's whole with a denial of each part or of a supertype of it; both are keyed by the
term. The index keeps each term holding two memberships, or a membership and a denial,
read off the term's unary roster once when the second arrives and kept in step after
(`membership/note-membership!`), and each pair of types a kept term holds. A term the read
finds holding denials and no membership is noted, so a further denial of it reads
nothing; `lein perf`'s `negation-load` holds a denial's arrival flat in the denials of its
term. The separations are
read again over those type pairs when a declaration moves them, and over the pairs holding
a type at or below a moved `genl` edge's lower end when an edge does
(`membership/sync-memberships`), so a declaration arriving reads no membership; `lein perf`'s
`membership-declaration-arrival` holds it flat in the memberships under the types it
separates. A term holding a pair the unscoped taxonomy separates, or a membership and a
denial under a stored cover, keeps its nogoods through that taxonomy, a superset of what
any reader reads, and its members are candidates. A reader keeps the nogoods whose
members it sees and whose grounds it reads: every ground context is in its ancestor set,
or the separations, covers and `genl` edges stated there convict the members
(`membership/term-nogoods`), read with no belief callback. A nogood the reader then decides is
read again, as the settle's standing ones are, once a round withdraws a ground it was
found through or an equality supporter (`res/*reread*`). An `orthogonal` exempts a pair at a reader
whose ancestor set states it, as `tax/disjoint?` over an ancestor set reads it. The
unscoped taxonomy the index keeps reads no exemption, so a pair only an `orthogonal`
spares is kept, marked `:spared?`, and read again over the reader's ancestor set.

**The reports.** `conflicts` and `contradictions` add the families' hard clashes and
dilemmas (`clashes/read-clashes`), built at the read: each context below a candidate's own
context decides the nogoods it reads, and a report names the most general contexts that
decided it so. Each nogood is decided at each context as that context's withdrawal
decided it (`res/verdicts`), so a nogood whose readers defeat different members is
reported once, with `:vantages`. A negation pair reports as a rebuttal: no `:kind`, and
the rebuttal priority. The answer is cached in `:withdrawn` with no watch, so every settle
point drops it, and a report whose members' classes and supports and whose vantages are
the last reading's is that reading's (`:read-reports`).

**The window.** A decided loser moves belief with no relabel, and the window reads it
per reader ([The published window](#the-published-window)).

**The family the settle finds.** An inherited nogood is found by the settle and decided
in the same rounds at each reader that sees a vantage of it
([A defeat is scoped to its vantage](#a-defeat-is-scoped-to-its-vantage)), beside these
families'. A decided loser is `:default`, and a sentence resting only on one is `:default`
too, so no member it would have been weighed against is weaker than it: such a nogood
defeats no member the reader believes.
`reference_test/an-irreflexive-loser-leaves-no-disjoint-pair-at-its-reader-in-every-order`
holds a loser whose consequence is a `disjoint` member.

### Declarations over related types

A `disjoint` over two types one of which reaches the other through `genl` is a one-member
nogood of the declaration, and a cover naming a part that a `disjoint` separates from its
whole is a two-member nogood of the cover and the `disjoint` ([reference.md](reference.md#decisions),
decision 8). The declarations are forced `:monotonic`, so each is a hard clash: `conflicts`
lists it, every member stays believed, and no belief moves.

```
(genl dogw animalw)  (disjoint dogw animalw)  (dogw Fido)          ; {(disjoint dogw animalw)}
(covering animalw dogw catw)  (disjoint dogw animalw)              ; {(covering …) (disjoint …)}
```

A cover states the edge from each part to its whole, so the `disjoint` of the second line
is over related types too and reports its one-member clash beside the cover's. Both are
found from the declarations' own arguments. The candidate index keeps every stored
`disjoint` and cover, the `disjoint`s whose arguments are related over the unscoped
closure (`:related-dj`), read again for the declarations naming a type at or below the
lower end of an edge that moved (`tax/moves-since`), and each cover paired with a
`disjoint` separating its whole from a part (`:cover-pairs`), kept at the store and
removal choke points. A KB whose `disjoint`s are all over unrelated types holds no row, so
`decide/live?` stays false for it. A reader reads a row whose declarations it sees, and a
`disjoint` whose arguments the `genl` edges stated in its ancestor set relate
(`related/related-nogoods`).

An `(orthogonal a b)` states that the two types may overlap and that neither subsumes
the other. It exempts its own pair from every form of disjointness
([taxonomy.md](taxonomy.md#disjointness)), so it is the same family's one-member clash, of
the `orthogonal` declaration, wherever a reader reads a `genl` edge between the two, the
two are one type, or the pair is still separated — through a separation of two
supertypes the declaration does not exempt.

```
(genl betaw alphaw)  (orthogonal alphaw betaw)                              ; {(orthogonal …)}
(disjoint upperw otherw)  (genl subw upperw)  (genl subv otherw)  (orthogonal subw subv)
                                                                            ; {(orthogonal …)}
(disjoint alphaw betaw)  (orthogonal alphaw betaw)                          ; no clash: exempt
```

The declaration is forced `:monotonic`, as `disjoint` is, so one written at `:default` is
held `:monotonic` too: the clash is a hard one `conflicts` lists, with the separating
declarations under `:grounds`, every member left believed, and the pair reading both
statuses (`:inconsistent`). The candidate index keeps every stored
`orthogonal`, and those some reader can read contradicted — over the unscoped `genl`
closure, or separated by `disjointness-test` with no exception read — under the `genl`
generation and `tax/separation-stamp` (`:related-orth`); either moving reads every one
again. A reader reads one it sees whose pair the `genl` edges stated in its ancestor set
relate, or `tax/disjoint?` over that ancestor set separates.
`reference_test/a-disjoint-over-related-types-is-a-hard-clash-of-the-declaration-in-every-order`
holds both in every arrival order.

### There is no second axis

Defeat-class is the only axis, and a default/default clash it cannot separate is reported
as a dilemma. The engine builds no specificity heuristic (a score from the size of a
type's `genl` up-closure):
[why a genl-derived ordering is inference about the knowledge rather than from
it](defenses.md#there-is-no-second-axis).

### Definitional constraints on the derivation path

arg types, disjointness and functionality hold of *derived* content as much as of
asserted content. A rule that concludes `(cat Rex)` where `(dog Rex)` is believed and
the two are declared disjoint has concluded something the KB says cannot be, so a check
that runs on only one path lets a rule produce what `assert` refuses.

`chain/place-conclusion` runs the same three checks `assert` does, and **does not
throw**: chaining is a fixpoint and cannot abort halfway through one without making
the resulting belief set depend on which rule fired first, and the engine's stance is
that contradictions are soft. A failing conclusion is *dropped* — no sentex, no
justification, nothing believed — logged at `:warn`, and recorded in
`(core/violations kb)` as `{:violation <kind> :sentence :context :rule :detail}`, the
kind naming which check refused (`:arg-type`, `:arg-genl`, `:inter-arg-type` and the rest
of the argument-constraint family). A disjointness or functionality clash is placed and
arbitrated rather than dropped ([Which entry point the content came
through](#which-entry-point-the-content-came-through)). An argument-constraint drop convicts on the *absence* of
a path to the declared type, so it is also remembered and re-asked once a `genl` edge or a
membership of the convicted term can have supplied one; placed then, its ledger entry is
withdrawn ([exceptions.md](exceptions.md), "A refused firing is remembered as bindings"). Two more kinds ride the same path: a completed firing
with **no placement context** is recorded as `:no-placement`, and a *derived*
`genl`/`genlCx` edge that would close a cycle through negation is dropped and recorded as
`:not-stratified`. A rule a **generator** minted and the rule checks refuse is dropped
the same way, under whichever refusal type the check threw. A conclusion naming a
reifiable application that has no constant yet is checked before the constant is minted,
so a dropped conclusion mints nothing, and a mint that refuses drops its conclusion as
`:mint-refused`, the refusal's own type under `:refusal` ([nat.md](nat.md), "Derivation
path").

One kind on this path drops nothing, and reports instead: `:non-confluent` is two
schematic equations disagreeing about a shared term.

`:context-edge-exposure-truncated` and `:genl-edge-revival-truncated` come from the merge
sweeps in `special` and in the settle, bounded by `tax/*exposure-instance-budget*`, and
nothing re-examines a merge past either cut ([equality.md](equality.md)).

The kinds are not only this path's. An aggregate prover that cannot reduce an extent
files `:aggregate`; the qualitative and metric-temporal networks file
`:qualitative-inconsistency`, `:metric-temporal-mixed-dimensions` and
`:metric-temporal-inconsistency` when a context's constraints cannot be satisfied; and
the sign arithmetic files `:sign-inconsistency` when they leave a quantity with no
possible sign at all. Each of those is a report and drops no conclusion. The whole roster,
kind by kind with the `:detail` keys each carries, is the set of tables in `core/violations`' docstring,
and `violation_roster_test` fails on a kind the engine files with no row there, on a row
naming a kind nothing files, and on a row whose `:detail` keys are not the ones the
entry builds.

`(core/violations kb)` is an **accumulating** ledger, not a per-run snapshot. Each
entry carries the run id from `(core/chain-stats kb)`, the ledger is capped at the
newest 1000 entries, and only `(core/clear-violations! kb)` empties it, so a bulk load's
drops survive the next assert.

The checks run only when the conclusion is **new** to its context. Re-deriving a
sentence already stored there adds a justification, not content — whatever it says was
admissible when it was first placed — so a second derivation cannot introduce a
violation that was not already there. `checks/args-problem` reads the memberships of
every constrained argument, a posting read, a record fetch and a belief test per type the
term holds, and forward chaining re-derives the same conclusion on every round of every
defaults pass, so a check per firing would repeat that read every round.

A conclusion is dropped only for a violation with **no opposing sentex**: an argument
constraint, an arity, a malformed special predicate, an unstratified derived edge. So
`violations` is the ledger of what cannot be represented, and a contested conclusion is
found in `contradictions` or `conflicts` instead.

A reader's rounds terminate because its losers grow monotonically and each withdraws a
member, deactivating its nogood.

### A clash is reported, never stored

Contradictions never fail a settle. A conflict is a nogood whose weakest members are all
`:monotonic`, and a dilemma one whose shared minimum is defeasible; `conflicts` and
`contradictions` return them as reports.

`(contradicts X Y)` is a **report form**, not a sentex. Nothing asserts it, no handle
resolves to it, and `(sentexes-matching kb '(contradicts ?a ?b) '?ctx)` is empty however
many clashes the KB holds (`constraint_nogood_test`; `resources/kb/CxCore.txt` says so of
the predicate). Stored, it would be a premise needing truth maintenance of its own, and it
would go stale the moment either side moved; a report is recomputed from current belief.

**A verdict lives exactly as long as its grounds do.** What makes two sentexes a pair is
the separation or the functionality the KB declares, and a known-true denial of it defeats
it: the pair stops being a pair, and the loser is believed again at every context that
reads the denial, whether the pair had been decided or stood as a dilemma. A membership
reported `:defeated` with an empty `:contradicted-by` would be a verdict that outlived its
grounds. A reader's rounds hold this by ordering: within one round a loser that withdraws
grounds (`tax/derives-from?`: an edge of a cached relation, or a flat-cache entry) is
taken before, and apart from, the verdicts resting on them, and the next round re-asks
the grounds (`clashes/reread-at`). Taking both at once would convict on a declaration the
same round disbelieves
([A defeat is scoped to its vantage](#a-defeat-is-scoped-to-its-vantage)).

`conflicts` and `contradictions` report the **same entry shape**, down to `:kind` and
every side's justifications (`clashes/clash-report`):

```clojure
{:nogood #{h1 h2} :handles [h1 h2] :priority int :kind kw-or-nil
 :sentence (contradicts X Y)
 :sides [{:handle :sentence :context :defeat-class :justifications [...]} ...]
 :grounds [{:handle :sentence :context} ...]
 :inherited {:sentence :context :claim handle :via [handle …]}   ; :kind :inherited only
 :vantages {vantage handle}}                                      ; a vantage disagreement only
```

`:kind` is the violation `:type` a definitional clash convicted on
(`checks/arbitrable-kinds`), `:inherited` for a preserving clash, and nil for a rebuttal.
`:inherited` is the one part of a report that is **not** a stored sentex, so it cannot be
a side: the claim nobody wrote, the context it was read in, the handle of the sentex it
was inherited from, and the handles that licensed carrying it there. Each of those
handles is also a member, so the sides carry their justifications and `why` explains the
reach. The two readings differ in *why* the set was left standing, not in what a caller
needs in order to act on it.

**`:grounds` names the declarations a definitional clash convicts through**, in content
order: the believed supporters of the flat-cache entries the conviction reads, among
those a vantage of the report sees (`clashes/clash-grounds`). For two memberships those
are the separating `disjoint` declarations, the disjoint metatype and its two
memberships, the `sibling_disjoint` parent and the separating cover; for tuples, the
`functional`, `functionalInArg`, `asymmetric` or `anti_transitive` mark; for a refuted
cover, the cover. No `genl` edge is named, so the list is bounded by the declarations and
not by the paths between them, and it is the same in every arrival order. A rebuttal and
an `:inherited` clash have none: their reasons are members. Retracting every ground
dissolves the clash. The grounds are read when a report is read, one supporter read per
declaration, and not carried by the report memo below, since a declaration can move under
a report whose members did not.

**`:sides` and `:handles` name the members in content order, and so does the list of
reports around them**
([why](defenses.md#tie-breaks-and-orderings-key-on-content-not-the-handle)). The sides
are ordered by sentence, then context, compared by `nm/compare-form`. Those two keys are
total, since sentence-plus-context identifies a sentex, so no handle enters the key;
`report_order_test` reads that line of `clash-report` and fails on a handle in it. Each
side's justifications follow `core/supporting-justifications`' content order.

**The ordering is the read's.** `clashes/read-clashes` builds the two vectors in the
order the candidate index answers in, and `clashes/ranked` orders a reading when it is
asked for; `conflicts`, `contradictions` and the preview's standing filter each call it,
and any further reader of `clashes/conflicts-of` or `clashes/contradictions-of` owes the
same call ([why the reading is sorted per read](defenses.md#a-clash-reading-is-sorted-at-the-read-not-on-the-settle-path)).
The two readings are one cached value (`::read-clashes` in `:withdrawn`), so a reader on
another thread cannot take one reading's conflicts beside another's contradictions. The
labeling solver re-sorts the dilemmas by priority then content for itself
(`solve_test/the-result-does-not-depend-on-the-order-the-nogoods-arrive-in`).

### The reports are rebuilt only where a member moved

The settle publishes no report. `read-clashes` builds the readings on the first read after
a settle point and caches them until the next one. A report is a function of its members —
their sentences, contexts, defeat classes and supporting justifications — plus `:kind`, the
vantages and a disagreement's verdicts, so `read-clashes` keeps each report it built in
`:read-reports` under those inputs and hands the same report back while none of them
moved; the memo holds only what the last reading reported. A settle therefore costs no
report, and a reading after it builds only the reports whose inputs moved
(`clash_reading_cost_test/a-read-builds-no-disagreement-report`).

### Where conviction is one-sided

A step read **through argument preservation** convicts one way only inside an
`anti_transitive` chain: the chain's steps are the ones `matches-visible` finds over the
marked predicate's spec closure, and a step that exists only because preservation reaches
it is not enumerated. Why discovery does not read preservation downward:
[defenses.md](defenses.md#discovery-does-not-read-argument-preservation-downward).

A stored claim denied by a claim read through preservation is not one-sided.
`preserving-nogoods` re-asks the stored facts a moved claim reaches, and the stored
extent of every predicate whose licence the settle otherwise moved
([The inherited-clash memo](#the-inherited-clash-memo)), so a general claim arriving
after the specific one forms the pair too. `(outranks animal cat)` beside `(outranks cat reptile)` under
`(asymmetric outranks)` is one `:inherited` nogood in either order, and the entry point
stores the second write
([inherit.md](inherit.md#a-contrary-claim-against-a-known-true-one-is-a-contradiction-and-is-reported)).

`clash_oracle_test` makes no `transitiveInArg` declaration, so it covers the visibility
shape and not this one.

### How a settle finds the clashes

No clash is found by re-running a check over what moved.  Each family's nogoods come off
the write-time candidate index, and each reader that sees one whole decides it
([Nogoods decided at the reader](#nogoods-decided-at-the-reader)).

What reaches a membership nogood with no relabel reaches it through the index or the
reader's stamp:

- **a declaration** moves `tax/separation-stamp`, and the index reads the separations
  again over every type pair the kept terms hold; **a `genl` edge** moving is logged at its
  lower end (`tax/moves-since`), and the index reads again only the pairs holding a type at
  or below it (`membership/sync-memberships`). Neither reads a membership, and the flat
  declaration caches and the `genl` generation are in `decide/stamp`, so every reader
  decides again. The index compares its stamp with the taxonomy's roster by roster on
  identity. An installed image holds the two as equal values read back apart, so the
  first read compares them by value once and takes the taxonomy's;
- **a `genlCx` edge** moves what each reader sees, and the `genlCx` generation is in
  `res/withdrawal-stamp`;
- **a membership or a denial** of a kept term joins it with no read, and the term's live
  handles are in `decide/stamp`.

`clash_oracle_test` compares a stream's reading, write by write, with the same writes
loaded from scratch, over the membership routes a clash arrives by.

## What a settle is built from

A settle composes 21 features. Each one requires some others to exist, and removing a
feature removes every feature that requires it. This section lists the features, what each
requires, the reserved words that reach each one, and what a removal takes with it. The
cost of each step is the next section.

### The dependency layers

`─►` means *requires*: the target's removal removes the source. `⇢` means *supplies*: the
target's removal leaves the source with no input and nothing broken; where two targets
supply one source, the removal of both does. The relation has no
cycle, because a cycle in it would be two features neither of which can be built first.

```
layer 5   published window ─► reader verdict, touched window
          withdrawal cache ⇢ reader verdict, visibility except
layer 4   reader verdict ─► decide/verdict        edge solver ⇢ decide/verdict
layer 3   decide/verdict ─► strength classes, deciding vantage
          decide/verdict ⇢ nogood discovery
layer 2   visibility except ─► context scoping    generators ─► forward chaining
          deciding vantage ─► context scoping
layer 1   touched window ─► region relabel        forward chaining ─► region relabel
          context scoping ─► genl/genlCx closures nogood discovery ─► genl/genlCx closures
          exceptWhen · NAF ─► recheck queue       supersession ─► equality partition
layer 0   region relabel, genl/genlCx closures, strength classes, recheck queue,
          equality partition ─► justification network ─► record store and index
```

| feature | code | reserved words | removing it |
|---|---|---|---|
| record store and index | `vaelii.impl.protocols` | none | removes everything |
| justification network | `vaelii.impl.jtms`, `vaelii.impl.dense-jtms` | none | removes everything above layer 0 |
| region relabel | `jtms/relabel-region*` | none | removes forward chaining, generators and the touched window |
| genl/genlCx closures | `vaelii.impl.taxonomy` | `genl` `genlCx` `isa` `genlInverse` | removes context scoping, nogood discovery and the arbitration bundle |
| context scoping | `tax/context-up` | `genlCx` `ist` | removes the visibility except, the deciding vantage and the arbitration bundle |
| strength classes | `jtms/region-classes` | `:monotonic` `:default` (assertion options) | removes `decide/verdict` and the reader verdict |
| recheck queue | `settle/drain-recheck!` | none | removes `exceptWhen` and NAF, its only fillers |
| equality partition | `tax/add-equality`, `tax/representative`, filled by `special/integrate-equality-sentex` | `rewriteOf` `sameAs` `equals` `different` | removes supersession |
| touched window | `jtms/touched`, and a reader's mark in it: `jtms/touch-mark`, `jtms/touched-since` | none | removes the published window; `preview`, the change feed and the cache reconcile diff the believed set instead, at O(KB) per write |
| forward chaining | `vaelii.impl.chain` | `implies` `set/forwardRule` `set/defaultRule` `set/backwardRule` `set/assumptionRule` `set/inertRule` | removes generators; backward proof still answers |
| generators | `vaelii.impl.chain` | `implies` `set/forwardRule` with a rule consequent | removes nothing |
| nogood discovery | `decide/nogoods-at`, `discovery/preserving-nogoods` | `not` `disjoint` `disjoint_metatype` `sibling_disjoint` `orthogonal` `functional` `functionalInArg` `asymmetric` `anti_transitive` `covering` `partition` `transitiveInArgInverse` `transitiveInArg` | leaves `decide/verdict` with no nogood to decide |
| `exceptWhen` · NAF | `recheck/exception-blocked-set` | `exceptWhen` `unknown` | removes nothing; `:blocked` stays empty |
| supersession | `special/refresh-supersessions` | `rewriteOf` `sameAs` | removes nothing; `:superseded` stays empty |
| visibility except | `res/withdrawal` | `except` `sentexHandle` | removes nothing |
| deciding vantage | a nogood's `:vantages`, recorded in the candidate index for an inherited clash | `genlCx` `ist` | removes `decide/verdict` and the reader verdict |
| `decide/verdict` | `decide/verdict` | `contradicts` (reported, never stored) `bravely` `cautiously` | removes the reader verdict |
| edge solver | `vaelii.impl.solve` | `set/hardConstraint` `set/softConstraint` | changes nothing for a KB on the built-in `decide/verdict` |
| reader verdict | `res/withdrawal`, over the families of `vaelii.impl.decide` | `genlCx` (the vantage) | removes the published window; every nogood stands believed |
| withdrawal cache | `:withdrawn`, filled by `res/withdrawal`, reconciled by `res/reconcile-withdrawn!` | none | removes nothing; each read at a reader computes its withdrawal again, the rounds of `decide/losers` included |
| published window | `readings/reader-moves`, `:own-readings` | none | removes the own-context reconcile, so the unscoped caches keep a handle its own context withdraws; `preview`, the consequence report and the change feed miss a move a verdict makes with no relabel |

Strength classes, the deciding vantage, `decide/verdict` and the reader verdict are the
**arbitration bundle**, and the bundle is the one region of the table where one removal takes several
features with it. Strength classes do not leave with arbitration: `core/defeat-class` is
public, and `vaelii.impl.inherit`, `vaelii.impl.chain` and `vaelii.impl.checks` read it for
supporter and declaration strength.

### A dependency no removal can separate

**A verdict requires strength classes.** `decide/verdict` takes the unique weakest member
of a nogood OUT at a reader. With no defeat-class the engine has no content-keyed
minimum, so a loser would be chosen on arrival order, which breaks order independence.

### The cycles a settle runs

The layers above have no cycle. The algorithm iterates in five places, each stated where
its mechanism is documented:

| cycle | what closes it | why it terminates |
|---|---|---|
| the exception loop | a blocked set moves belief, and belief moves what an exception query answers | a cycle through negation is refused at assert time; 16 passes bound it ([exceptions.md](exceptions.md#blocking-and-the-tms)) |
| a reader's rounds | a loser withdraws a region at the reader, and a withdrawn ground can dissolve a nogood | a round only adds losers, and a withdrawal only removes belief, so a round retires nogoods and never forms one ([the resolution rounds](#the-resolution-rounds)) |
| a support cycle | `A` justified by `B` and `B` by `A` | `region-fixpoint` starts from nothing IN inside the region and only adds ([Locality](#2-locality)) |
| the class equation | a node's defeat-class reads its antecedents' classes | `region-classes` starts every member at `:default` and applies a monotone operator ([Strength propagates](#strength-propagates-from-the-antecedents)) |
| a `genl` or `genlCx` loop | an edge that would close a cycle in the closure | refused, or dropped and recorded when derived ([exceptions.md](exceptions.md#stratification)) |

### No switch removes a feature

Every feature above runs on every KB. Each optional feature sits behind an emptiness check
instead: a KB storing no `exceptWhen`, no merge, no clash declaration or no `except` pays a
set read for that feature per settle. No option on the KB handle moves belief; the
reasoning image stamps the one process switch that does, `VAELII_ASSERTIVE_ARG_TYPES`
([storage.md](storage.md#the-reasoning-image)).

## The runtime of a settle

Invariant 2 states that a relabel costs its region. A settle does more than relabel, and
each of its other steps is bounded by a different quantity: the standing contradiction
set, the rules a trigger reaches, a sweep budget, or the whole store. This section lists
the steps in the order `settle*` runs them, gives the quantity that bounds each one, and
names the gate that holds the bound. The last part lists the steps where the bound is not
the region.

### The runtime view

`n` is the store, `r` the relabelled region (`jtms/touched`), `q` the rules the recheck
queue holds, and `c` the readers a move reaches.

```
write entry point (assert / retract)                          bound
 ├─ canonicalize · checks · index · record · JTMS node        O(1) per fact
 ├─ chain: join each rule keyed on the fact's predicate       O(rules on the predicate × join)
 └─ add-justification → relabel the affected region           O(edges in r)

settle*
 ├─ 1  clear-inherited!, again at the head of each pass       O(1); empties `:withdrawn`
 │                                                            when a clash was held
 ├─ 2  the reconcile a caller's relabel owes                  O(r)
 └─ passes, until one queues, revives and releases nothing, at most 16
     ├─ 3  class-moved-merge-seeds (only under a merge mark)  O(r)
     ├─ 4  discover-inherited!: one discovery, no round
     │     └─ preserving-nogoods                              O(1) gate; else O(standing + r), asks O(r)
     ├─    reader-moves · reconcile-own-withdrawals!          O(c)
     ├─ 5  drain-recheck!                                     O(q)
     ├─ 6  revived-seeds · refresh-beliefs over them          O(r)
     ├─ 7  exception-blocked-set                              one level-6 query per trigger-reachable firing
     └─ 8  set-blocked · sweep · re-chain released firings    O(released firings);
                                                              a blanket re-join is O(fact extent) per rule

settle-finish
 ├─ restore-depths (only after a deferred batch)              O(V + E) of the taxonomy, once
 ├─ refresh-beliefs (only when belief moved)                  O(caches a supporter in r feeds)
 ├─ refresh-supersessions (only after an except or an         O(data the except reaches + classes moved)
 │   equality edge moved in belief)
 ├─ reconcile-withdrawn!                                      O(|touched since its mark| × watches)
 └─ reader-moves                                              O(readers a move reaches); every reader
                                                              when the rest of the stamp moved or
                                                              on a rebuild

recover                                                       O(n): one settle, r = every sentex
```

Inside every relabel, the two least fixpoints are `region-fixpoint` for `:in` and
`region-classes` for the defeat-classes. Each is a worklist over the region's edges, so
each is O(edges in r)
([Locality](#2-locality) has the measurement).

A settle materializes the region `passes + 1` times, which `settle_region_cost_test` pins
as a count. On the dense network each read copies the touched bitmap into a set, so that
count is a multiplier on O(r), and on a `recover` it is a multiplier on O(n).

### The resolution rounds

Step 4 of the runtime view is `discover-inherited!`, which runs no round: the network records no defeat.
It empties the inherited clashes, asks `preserving-nogoods` once, and records every
nogood found whose members the network believes, with its vantages, in the candidate
index, where every reader at or below a vantage decides it in its own rounds
([A defeat is scoped to its vantage](#a-defeat-is-scoped-to-its-vantage)). The hard
clashes and dilemmas are read at the reader (`clashes/read-clashes`).

The discovery reads `discovery/discovery-view`: a detached copy of the taxonomy with every
handle withdrawn at its own context back at its network label, and caches and a candidate
index of its own. The copy's declarations and `genl` generation differ from the live
taxonomy's, so an index both stamped would be synced again (`decide/synced`) each time a
read inside the discovery passed from the copy to the live taxonomy's visibility callback. A
reading's edges and declaration are members of its nogood, so a verdict that took one
out of the unscoped caches would hide the reading from the next discovery, which would
give the member back, and the next one would take it out again. A reader's verdicts on
the other families still apply at the askers, through the scoped reads, so a ground those
families withdraw first is withdrawn from the reading too, as the reference's rounds
withdraw a ground before the clash read through it.

A reader's rounds (`decide/losers`, [reference.md](reference.md#the-function) item 8) add
losers grounds first and alone
([A clash is reported, never stored](#a-clash-is-reported-never-stored)), and terminate:
each round adds a loser the reader believed and none takes one back. A sentence first believed after a round's defeat released an
`unknown` or `exceptWhen` guard is `:default`
([Strength propagates from the antecedents](#strength-propagates-from-the-antecedents)),
so it cannot defeat a `:monotonic` member, and a later round's new nogoods take OUT only
`:default` sentences ([reference.md](reference.md#decisions), decision 14). The hard clashes and the dilemmas are collected at the round
that defeats nothing, so a clash that stands beside other rounds' work is counted once.
No round flips an `except` where CxCore declares it: an `except` is held `:monotonic` and
its denial OUT ([The forced-monotonic roster](#the-forced-monotonic-roster)), so no
resolution defeats one.

### What `settle-finish` reconciles

`settle-finish` runs once, after the last pass, in this order:

1. `restore-depths`, the depth repair a `with-deferred-settle` batch owes.
2. `refresh-beliefs` over the region, only when belief moved: a defeat, a revival, a
   standing nogood, a pass that moved the blocked set, or a relabel before the settle
   (`belief-moved?`). Those are the only label flips a settle sees. The last is
   `preview`'s: `suspend-premise` and the rollback's `add-premise` flip labels with no
   defeat, block or write, so `preview` binds `settle/*relabelled-before?*`, and the
   settle also reconciles at its start, as after a revival, before the passes read the
   closures. A declaration that arrives or leaves reaches the caches
   through `special`'s integrate hook on the write path, so a settle that flipped no label
   leaves the caches consistent. `restore-depths` runs again after the reconcile, since
   the reconcile can open or close a cycle
   ([taxonomy.md](taxonomy.md#what-a-batch-does-to-the-depth-potential)). An equality
   supporter a reconcile found disbelieved and this one finds believed met its arrival
   with nothing to restate, so its class takes the arrival's re-check and migration here
   (`special/believed-again-sweeps`), and the supporter and its twins go to `settle`'s
   re-seed ([equality.md](equality.md#what-a-merge-does)).
3. `refresh-supersessions`, only after an `except` moved, or an equality edge that the
   roster does not hold moved in belief. The write path reconciles every supersession a
   stored or removed sentence moves, so a settle that moved no equality premise reconciles
   none ([equality.md](equality.md#what-a-merge-does)).
4. `refresh-beliefs` again whenever a supersession entry changed since the last settle,
   over the region plus those data (`special/take-supersession-moves!`). A merge
   supersedes a `genl` or `disjoint` declaration with no label moving, and step 2 read
   the region alone. The spellings an un-merge gave back go to `settle`'s re-seed
   ([the other half](#the-other-half-a-spelling-an-un-merge-gives-back)).
5. The own-context reconcile (`special/reconcile-own-withdrawals!`, after
   `res/reconcile-withdrawn!`) to a fixpoint of at most four rounds
   ([A read with no reader](#a-read-with-no-reader)). Off on a rebuild.
6. `res/reconcile-withdrawn!`, the last read of the window before it is cleared
   ([the withdrawal cache](#the-withdrawal-cache)).
7. The window: the region, the supersession flips, the twins step 2 stored, and the
   handles a reader's verdict moved at their own context (`reader-moves`,
   [The published window](#the-published-window)),
   handed to `*touched-sink*`, `*touched-in-sink*` and the change feed. `reader-moves`
   records its readings on every settle. The sets are built only when a sink is bound or a listener is
   registered, and the feed is skipped on a rebuild, whose region is the whole KB.
8. `reset-touched!`.

`jtms/touched` is read once, into a delay every step shares, because the dense network
copies its bitmap into a set on each read.

### Where the time goes, measured

`lein bench-settlephases [n] [memory|disk|both] [defeats=<k>]` charges each settle's wall
clock to the cost centre running at that instant (`vaelii.impl.settle-phases`). The reading below is n=60,000 facts (104,157 sentexes,
52,074 justifications). The split is a ratio between centres in one run and holds across
n=20,000–60,000; the harness reports absolute milliseconds as untrusted on a shared machine.

| centre | additive load | `recover` replay | contradiction-dense load |
|---|---|---|---|
| `:chaining` — the generative join | **48–51%** | 0% | 32% |
| `:outside` — canonicalization, checks, index, minting | 42–44% | 6–11% | 29% |
| `:belief` — relabel and `add-justification` | 0.5% | **87% memory, 90% disk** | 5% |
| `:discovery` — the inherited family's discovery | ~1% | ~0% | 2% |
| `:finish` + `:glue` | 6–8% | 3–4% | **33%** |
| relabelled region, p50 | 2 | 104,157 | 2 |

A centre is charged its **self-time**, the interval while its span is on top of the stack,
so nested centres are not counted twice and the six buckets sum to the run. `:belief`
holds the relabels, the reconcile a caller's relabel owes and `recovery/rebuild-tms`'
replay; `:finish` is `settle-finish`, where the readers' decisions of the families a
reader decides are read;
`:glue` is the settle loop outside every span, and `:outside` the time between settles.
`add-justification` carries no probe of its own: its time goes to the span its caller
opened. A span on a timing run costs two `System/nanoTime` reads and two unsynchronized
mutations, which the single writer permits. `settle-phases/stop` returns the run totals
and one record per settle with its region size and pass count, since one root-edge
retraction moves the whole graph and a mean over settles hides it.

Three shapes follow from the table:

- **A clean load spends its time writing and chaining, not believing.** The per-assert
  region is 2 nodes, so the belief fixpoint is 0.5% of the run. The per-fact write path
  is [storage.md](storage.md#what-a-bulk-load-costs)'s table: 43.4 µs per fact at one
  million facts, with the one deferred settle under the measurement floor.
- **A `recover` spends its time believing.** Its region is the store, and on `:disk-log`
  the justification fetch lands in the replay's `:belief` span, which is why the durable
  share is higher. A `:disk-snapshot` open skips this step when it installs the
  [reasoning image](storage.md#the-reasoning-image).
- **A contradiction-dense load spends its extra time reading the decided handles.** The
  load seeded 50 contradictions (`defeats=50`), negation pairs in `CxUniverse` decided at
  their readers. No settle lifts or re-decides them, so the median region stays 2 and
  `:discovery` is 2%. Each later settle pays about 0.05 ms more at p50 than on the additive
  load, in `:glue` and `:finish`: the withdrawal cache's stamp and reconcile and
  `reader-moves`, asked once per settle while any reader-decided candidate is stored. It
  is the same at 400 decided pairs as at 50, and an unrelated write reads none of the
  pairs (`negation-reader-write`).

The exception loop is measured separately in
[exceptions.md](exceptions.md#the-fixpoint-question-measured): the blocked set moved in
**0** passes on every settle of the starter and stories load, and in at most **1** in every
`except_test` scenario. On `except_recheck_test`'s workload, where a
second rule makes the exception hold on every firing, step 7 costs **1.0** level-6
evaluation per assert and the whole settle **2.0**, flat from n=25 to n=200.
`except_recheck_test` pins the growth of that count, not its value.

### Where the scaling arguments hold

`lein perf` asserts each scaling claim as a growth ratio between two sizes, never as a
duration. `bench/vaelii/bench/perf.clj` states the method, and each check there carries
its `:claim`, `:sizes` and `:max-ratio`. The checks sort into five groups by the quantity
the claim bounds a step by. A sixth group lists the steps whose bound is the store, which
no check holds.

**Flat.** The step costs its region, or what it returns, and not the quantity the check
grows. The ratio bound is 2.0× across a 6× to 128× size step unless the row names
another. These checks hold invariant 2 end to end:

| step | `lein perf` checks |
|---|---|
| a write that reaches its own region: a fact derived through a defeasible rule, a negative fact with no positive twin, a membership, a length binding, a fact of a predicate with a declared arity, a durable append, a fact into an existing context NAT, a retraction naming no NAT | `defeasible-load`, `negation-load`, `membership-check`, `bound-type-load`, `arity-reach-trigger`, `durable-fact-append`, `context-nat-existing-context` (3.0×), `retract-nat-scaling` |
| a region delivered to a feed listener | `feed-listener-scaling` |
| a `genl` edge deep in a chain, and one `genl` edge or `inverse` declaration defeated and revived beside n `disjoint` declarations (the relabel and `refresh-beliefs`) | `taxonomy-depth`, `taxonomy-belief-flip`, `flat-cache-belief-flip` |
| a write on a KB whose marks the fact does not reach | `unrelated-fact-under-marked-kb-fanout`, `constraint-exposure-shared-arg`, `constraint-genl-edge-gate` (2.5×) |
| a membership or a `genl` edge into a `sibling_disjoint` clique, in the clique's size | `disjoint-clique-membership`, `sibling-disjoint-new-spec` |
| a `genl` or `genlCx` edge, in the graph, the excepted rules, the firings and the readers it does not reach, and in the spec closures of the rules its stratification walk reaches | `genl-edge-negation-recheck`, `edge-stratification-unreached`, `edge-stratification-walk`, `genl-defeat-rejoin` (4.0×), `genl-crossing-many` (3.0×), `genlcx-edge-reader-fan` (3.0×), `retract-context-cycle-scaling`, `retract-context-cycle-beside-cycle`, `assert-context-edge-beside-cycle` |
| an un-merge of one class beside standing merges it does not touch, a merging assert in a deferred batch, a write beside the subsumed mints the KB withholds, and the settle after a `genl` edge re-asking the declarations waiting on a deeper hierarchy | `unmerge-over-standing-merges` (3.0×), `deferred-merge-batch` (3.0×), `mint-withdrawal-under-busy-term`, `settle-beside-withheld-mints`, `mint-release-after-genl-move` |
| a recover's rebuilds, per claim, declaration or fact each re-reads: the inherited discovery's questions, over the live taxonomy and over a detached copy, the nogoods its first reader re-reads, the waiting declarations, the lifts | `recover-inherited-discovery`, `recover-discovery-own-out`, `recover-discovery-separated-term`, `declaration-rebuild`, `lift-rebuild` |
| an `exceptWhen` roster gate, a write beside believed `except`s it does not reach ([the withdrawal cache](#the-withdrawal-cache)), the first read after a two-pass settle, a write beside refused firings ([the kind roster](exceptions.md#a-refused-firing-is-remembered-as-bindings)), a retraction releasing a firing beside a guarded rule's firings ([what is re-chained](exceptions.md#re-chaining-what-was-released-not-what-was-touched)), a first read below an `exceptWhen` rule's context ([asked at every reader](naf.md#evaluated-in-the-placement-context-not-the-join)), and a scoped read beside what the `except`s hide | `exception-roster-gate`, `assert-over-standing-excepts` (3.0×), `read-after-two-pass-settle` (3.0×), `assert-beside-naf-refusals`, `released-refusal-beside-guarded-firings` (4.0×), `guarded-firings-read-below`, `visibility-reading` |
| the families decided at the reader ([Nogoods decided at the reader](#nogoods-decided-at-the-reader)): a mark, a binding or a declaration arriving over its candidates and the first read after it, a write beside the pairs a reader decides, a warm read at a reader, a reader's first withdrawal beside the candidate tuples its binding holds, a vantage below the members' maximum, the join naming a chain's contexts, a brave or cautious ask between writes, and an ask of the candidate index after an image install | `irreflexive-mark-arrival` (3.0×), `arity-binding-arrival` (3.0×), `membership-declaration-arrival`, `tuple-mark-determinant-write`, `negation-reader-write`, `verdict-window-write`, `decided-warm-read`, `held-shape-first-withdrawal`, `negation-reader-warm-read`, `tuple-mark-warm-read`, `per-reading-vantages`, `chain-join`, `brave-ask-between-writes` (3.0×), `installed-image-reads` |
| retrieval: an argument after a variable, a compound, an intersection or an overlay posting, a columnar insert, a closure already asked, an open `disjoint` goal, a membership of a busy term, and a plan | `arg-root-retrieval`, `compound-probe`, `intersect-selectivity`, `overlay-selectivity`, `columnar-fanout`, `closure-membership`, `disjoint-enumeration`, `membership-read-under-busy-term`, `plan-scaling` |
| solving and the qualitative calculi | `solve-rule-grounding`, `label-beside-unrelated-facts`, `qcn-network-residency`, `qcn-arrival-over-standing-firings` (3.5×), `qcn-arrival-beside-an-unmoved-network` (2.5×) |

**Flat past a cap.** A budgeted merge sweep implicates every instance below a type or
inside an ancestor set, which is the extent rather than the region. The sweep stops at
`tax/*exposure-instance-budget*` instances (8192; the checks bind it to 100) and files a
notice naming its trigger, so the cost is flat once the extent is larger than the budget
and linear in the extent below it: `constraint-exposure-context-edge`,
`functional-in-arg-empty-determinant-sweep` and `constraint-genl-mark-descent`, each 2.0×
past the budget. A `genl` edge whose closure holds more than `inherit/crossing-closure-cap`
terms (512) moves every predicate preserved along `genl` with no read per term:
`genl-crossing-wide`, 3.0× past the cap.

**Linear in the standing set.** `k` is the standing set: the nogoods, merges or withdrawn
firings the KB holds. No settle carries a verdict forward. `clear-inherited!` empties the
withdrawal cache on every settle while an inherited clash is held, and a write that moves
`res/withdrawal-stamp` empties it too, so the next read at a reader decides every nogood
that reader sees again (`decide/losers`). Belief is computed from current state and never
carried over, which is invariant 1, and the cost of that is an O(k) term on such a write.
The checks bound the per-member cost, so a regression to a full re-derivation of the set
on every settle fails them:

| claim | `lein perf` check | growth | bound |
|---|---|---|---|
| standing definitional clashes, per assert | `clash-arbitration` | 32× | under 15× |
| standing `P`/`¬P` dilemmas, per assert | `negation-arbitration` | 8× | under 11× |
| standing inherited dilemmas, per assert | `inherited-clash-arbitration` | 32× | under 10× |
| standing inherited clashes split across contexts, per unrelated assert | `inherited-clash-arbitration-split` | 512× | under 90× |
| carried inherited-clash entries, per unrelated retract | `inherited-entry-retraction` | 32× | under 10× |
| standing merges, per unrelated retract | `retract-merge-scaling` | 32× | under 18× |
| standing merges, per `except` of one merge asserted and retracted | `except-merge-scaling` | 128× | under 28× |
| standing clashes, per `genl` edge separating nothing | `taxonomy-edge-arbitration` | 100× | under 35× |
| standing dilemmas, per `genlCx` edge reaching nothing | `context-edge-arbitration` | 100× | under 32× |
| `contradictions`, which orders the standing set it returns | `standing-clash-reading` | 32× | under 175× |
| firings a reader below a vantage reads as withdrawn, per settle's scan of them (`reroute/lost-firing-seeds`) | `lost-firing-scan` | 8× | under 20× |

**Grows with a structure the step walks.** The step walks something the fact or the
question names, and the claim is that it walks that structure once rather than once per
pair:

| claim | `lein perf` check | growth | bound |
|---|---|---|---|
| the hierarchy above a predicate, per membership assert | `membership-under-depth` | 32× | under 12× |
| a `disjoint_metatype`'s members, per membership assert | `disjoint-metatype-membership` | 8× | under 12× |
| the vocabulary (2.8× while the stored facts grow 8×), per `kb-quality` | `quality-report-scaling` | 8× | under 4× |
| the declarations, per declarations census | `quality-declaration-census` | 8× | under 15× |
| the super-predicates, per declarations census | `quality-declaration-depth` | 32× | under 45× |
| the claims reaching one term, per ask | `inherit-reach-memo` | 8× | under 12× |
| the routes between two terms, per preservation support | `witness-route-search` | 8× | under 12× |
| the instants of a metric network, per arriving constraint | `metric-closure-warm-start` | 8× | under 35× |
| the links of a sign chain, per ask after a write | `sign-chain-rebuild` | 32× | under 100× |

**Baseline.** `qcn-chain-load` and `qcn-arrival-over-composed-exceptions` carry no
`:max-ratio`. Each is measured at both sizes and printed with its growth, and neither is
judged: each is the before-reading for a cost that grows by design.

**Proportional to the store by construction.** No perf check bounds these steps, because
their region is the store:

- **`recover`**, whose single settle relabels every sentex. The reasoning image is the
  mitigation, not a scaling argument.
- **A root edge.** The affected region of a `genl` edge at the top of the taxonomy is its
  whole consequence closure, so O(r) is O(n) for that write. Locality bounds a write by
  what depends on it, and some writes have everything depending on them.
- **A blanket re-join** in step 8, for a rule whose refusal record overflowed
  `chain/max-refusals-per-rule` (4096 entries) or a context-visibility transition. Each
  such rule joins over its fact extent once per productive pass.
- **`restore-depths`**, O(V + E) of the taxonomy once per `with-deferred-settle` batch.

### What neither gate sees

`lein perf` reads ratios, so a constant added to every write moves both readings and
passes. `assert_cost_test` pins the index operations seventeen fixed workloads cost (twelve
asserts and five retractions), and
`settle_region_cost_test` pins how often a settle materializes its region and what it
re-derives; those counts are the gate for a constant. No gate watches the phase split
above: `lein bench-settlephases` reports it, and a change that moves time between centres
without changing a ratio or a count passes both gates.

## The `Solver` protocol (`vaelii.impl.types.solve`)

The external solver is a plug-in behind a protocol, defined in `vaelii.impl.types.solve`;
`vaelii.impl.solve` builds the `Program` and holds the local solver:

```clojure
(defprotocol Solver
  (solve [solver program]
    ;; -> {:defeat #{handle...} :violated [nogood...]}
    ))
```

A `Program` carries five fields: `assumptions` (the contested defeasible handles, never
known-true), `fixed` (known-true background referenced by a contradiction, assumed and
not decided), `contradictions` (nogoods with priorities and sentences), `content`
(`{handle {:sentence s :context c}}`, so a tie-break keys on what an assumption says
rather than on its handle), and `cardinalities` (at-most / at-least bounds over contested
heads, which only `solve-context` fills, from `asp/atMost` / `asp/atLeast` rules). A
backend renders it to ASP:

- default nodes → choice/`{a}` atoms;
- `:monotonic` `fixed` nodes → **omitted** (assumed true, never sent);
- contradictions → **weak constraints** with priorities, so the program is always SAT and
  the violated weak constraints are the reported result.

### Only `:default` content reaches a solver

A settle hands no nogood to a solver: `decide/verdict` answers a defeat, a dilemma or a
hard clash. Labeling is the solver's one caller
([why that holds the split](defenses.md#a-settle-hands-no-nogood-to-a-solver)).
`label/dilemma-program` builds its `Program` from the dilemmas, whose tied minimum is
defeasible, and `solved-labeling` keeps the program's assumptions minus the solver's
`:defeat`, so a defeat outside the assumptions moves nothing.

Two solvers ship. The default is `local-solver`, a deterministic stub that satisfies
contradictions highest-priority-first by defeating the greatest-`content-key` contested
member and reports any nogood it cannot satisfy. `vaelii.impl.asp.edge/edge-solver`
renders the Program to ASPIF and solves it with clingo or clasp; install it with
`(core/set-solver kb :asp)`. It falls back to the stub when no backend is reachable.
Where the stub walks contradictions one at a time, ASP optimizes globally: given two
nogoods sharing a member it defeats the shared one. See [asp.md](asp.md).

## API

```clojure
(assert kb S ctx {:strength :monotonic})   ; known-true; never defeated, never solved
(assert kb S ctx)                           ; :default (the common case)
(conflicts kb)                              ; the irreducible known-true clashes, as reports
(contradictions kb)                         ; the dilemmas, as reports
(violations kb)                             ; derived conclusions dropped as inadmissible
(preview kb {:add […] :remove […]})         ; the belief a batch would move, then rolled back
(set-solver kb :asp)                        ; the real answer-set backend, by name
(set-solver kb solver)                      ; or any Solver value
```

Every refusal `assert` throws carries an `ex-info` `:type`;
[troubleshooting.md](troubleshooting.md#i-have-a-type-and-do-not-know-what-it-means)
holds the vocabulary and the page that owns each keyword.

## Where the layer stops

- A violation with **no opposing sentex** is dropped and reported, never arbitrated: an
  argument constraint, a malformed special predicate, an unstratified derived
  edge ([Definitional constraints on the derivation
  path](#definitional-constraints-on-the-derivation-path)).
- NAF is not a nogood. `unknown` / `thereExists` in a rule antecedent is re-evaluated on
  the `exceptWhen` triggers and stores nothing ([naf.md](naf.md)). A `Justification` has
  **no out-list**: an existential NAF negates a pattern, which has no single handle for an
  out-list to hold.
- A default/default clash is reported as a dilemma and never arbitrated
  ([There is no second axis](#there-is-no-second-axis)), so the engine orders no two
  equally strong rebuttals.
- A settle commits to one optimal answer set, so `in?` alone does not distinguish a forced
  belief from a pick between equals. `vaelii.impl.asp.label/classify` enumerates the
  optima to recover the distinction, and `label/classify-local` does so region-locally
  with no backend ([labeling.md](labeling.md), [asp.md](asp.md)); belief itself still
  commits.
- Cardinality/aggregate contradictions are not expressed; a nogood is a flat set.
- **An equality is not defeasible by its own negation.** Once `(rewriteOf Pref Dep)`
  merges the two, every sentence naming `Dep` is rewritten — including
  `(not (rewriteOf Pref Dep))`, which is stored as a claim about `Pref` alone and so
  clashes with nothing and defeats nothing. The ways an equality stops being believed are
  retracting it and withdrawing what a *derived* one rests on; both un-merge, and both are
  re-seeded ("The other half" above).
- **A firing names one witness, so a second route is re-derived rather than recorded.** A
  justification names one path for each reachability it rests on: the `genl` path a
  subsumed match climbed, the `genlCx` path its placement is seen over, and the path a
  `transitiveInArg` claim travelled. A route arriving after the firing that the witness
  rule names instead re-joins the firing over itself, and the justification it adds
  **replaces** the one over the older route (`special/drop-replaced-routes!`): the same
  informant, conclusion and bindings, and antecedents that differ only in believed `genl`
  and `genlCx` edges. The store then holds what the order bringing the route first holds,
  and `why` answers the same in both (`late_route_test`). The argument-type entailment
  replaces its route the same way. Four things take a named path away, and each starts a
  re-derivation over a surviving route:

  | what takes the path | where | what re-derives |
  |---|---|---|
  | a retraction of an edge | the network | the re-join of the facts under the edge, from what the sweep collected (`special/resubsumption-seeds`) |
  | a network defeat of an edge | the network | the same re-join, from the edges that went IN ⇒ OUT in the settle (`settle/departed-seeds`) |
  | a reader's verdict against an edge | each reader that takes it OUT | the firing again, at each reader that still reaches, with every witness search asked from that reader (`reroute/lost-firing-seeds`, `chain/*witness-view*`) |
  | an `except` of an edge | the excepting context and below | the same, per reader |

  The argument-type entailment and the equality a descended `functional` or
  `anti_symmetric` mark derives name a `genl` route the same way (`checks/edge-support`),
  and the first two rows re-derive them too: a retraction draws each derivation the sweep
  deleted again after the teardown, and a network defeat draws each one the edge took OUT
  (`special/rederive-descended`, [argtypes.md](argtypes.md)).

  A reader's verdict and an `except` leave the edge IN in the network, so no relabel starts:
  the settle asks each reader at or below a vantage or an excepting context for the firings
  it reads as withdrawn only because an edge of a path they name is withdrawn there, whose
  sentence it believes through no other sentex, and whose path ends it still reaches. Such a
  firing is chained again from its antecedent facts with the reader as the witness view, so
  the path found is one the reader reads, and placement is decided from that path's
  contexts as for any firing.

  The preservation witness is the route whose most specific asserting context is the most
  general available ([inherit.md](inherit.md)), so a clash that denies an edge of the
  specific route costs a reader nothing: the conclusion is placed above that route and does
  not rest on it. A clash that denies an edge of the **named** route withdraws the firing at
  the clash's vantage and below, and the re-derivation above puts it back. Two shapes show
  where it lands. The first is a clash in the specific route's own context:

  ```
  CxUniverse   (genl mid dog) (genl chi mid)   the long route, named
               (largerThan dog cat)  (transitiveInArgInverse largerThan 1 genl)
               forward rule (largerThan ?x ?y) ⇒ (noted ?x ?y)
   └─ CxA      (genl chi dog)                  the short route
               (not (genl chi mid))  :monotonic
  ```

  CxA reaches `chi` up to `dog` over its own edge and reads the CxUniverse firing as
  withdrawn. The settle re-derives `(noted chi cat)` over the short route, which places it
  in CxA as a sentex of its own — the firing the short-route-first order stores anyway.

  The second is a pair of routes that **tie** on generality, where the shorter one is
  named:

  ```
  CxUniverse   (largerThan dog cat)  (transitiveInArgInverse largerThan 1 genl)
               forward rule (largerThan ?x ?y) ⇒ (noted ?x ?y)
   └─ CxA      (genl chi dog)  and  (genl chi mid) (genl mid dog)   both routes
        └─ CxB (not (genl chi dog))  :monotonic
  ```

  Both routes lie in CxA, so the one-edge route is the witness and `(noted chi cat)` is
  stored in CxA. CxB is the vantage of the clash over that edge and reads that
  justification as withdrawn; the re-derivation from CxB names the two-edge route, which
  places the conclusion in CxA again, so it lands as a **second justification** of the same
  sentex and CxB reads the sentex through it.

  Replacement stops at three places, each of which changes what is stored and not what is
  believed. A re-derivation for one reader, as in the tie example, keeps both
  justifications, because the readers above the vantage still read the first. An older
  route with an edge OUT is kept, so an edge defeated and then revived leaves the firing
  with the route it had and the route the re-derivation named. And the equality a
  descended `functional` or `anti_symmetric` mark derives keeps the route it first named:
  a pair already merged is not derived again, so a later shorter route adds no
  justification to replace it with.

  **Routes stated in sibling contexts are each named, and none is re-derived.** The
  witness searches return every route no other route covers — a route covers another
  when each of its asserting contexts is seen from one of the other's — and the join
  makes a firing of each ([inherit.md](inherit.md), "Placement follows the reasons";
  [contexts.md](contexts.md#the-consumers-and-what-each-of-them-may-reach) for a
  subsumed match). Two contexts neither of which sees the other cannot rank their
  routes, and each route places the conclusion in a reader the other does not reach:

  ```
  CxUniverse   (aRel high val)  (transitiveInArgInverse aRel 1 genl)
               forward rule (aRel ?x ?y) ⇒ (noted ?x ?y)
   ├─ CxA      (genl low mid) (genl mid high)
   ├─ CxB      (genl low high)
   └─ CxD      sees CxA and CxB
  ```

  `(noted low val)` is stored in CxA over the CxA route and in CxB over the CxB route,
  whichever arrived first, and a knock of a CxA edge — at CxA or scoped to CxD — leaves
  CxB's firing and CxD's reading of it standing. The four rows of the table above apply
  to each route alone: a knock takes the path one firing names, and a reader that still
  reaches over the same route's other supporters re-derives as described.
  `second_route_test` builds these shapes in every order, with and without each knock, and
  [defenses.md](defenses.md#routes-in-sibling-contexts-each-carry-a-firing) gives why one
  named sibling route would not do.

  What this leaves is history in the store. A firing re-derived for a reader outlives the
  defeat or the `except` that prompted it, since lifting either makes the original firing
  readable again and takes nothing the re-derivation made; every reader of the re-derived
  firing also reads the original one, so no belief depends on it, and `sentexes-in-context`
  and the handle count do. And the scan runs on every settle pass while a standing nogood, an
  `except` or a reader-decided candidate stands, one withdrawal per reader below it and one
  check per firing withdrawn there — linear in those firings (`lein perf`'s
  `lost-firing-scan`), and nothing when the KB holds none. A pass reads a reader again only
  when its withdrawal entry was recomputed, or the window holds a witness edge or a sentex
  of a sentence its last scan found re-routable; the readers themselves are memoized on
  the candidate index and the rosters. So an unrelated write scans no reader and reads no
  candidate (`negation-reader-write`). The covering test that decides which routes place a firing leaves a
  surplus of the same kind, a firing placed below another it is read beside, in a lattice
  that splits one route across sibling contexts
  ([defenses.md](defenses.md#routes-in-sibling-contexts-each-carry-a-firing) gives the
  shape and its count).

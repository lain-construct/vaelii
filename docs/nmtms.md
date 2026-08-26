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
one.** `core/put-premise-mark` writes both halves together — `jtms/add-premise` into the
network and `p/mark-premise` into the record store, where every backend keeps it as the
sentex's own `:strength` field and nothing else. The record is what `recover` replays
(`rebuild-tms` reads `p/premise-strength`, never the network), so it is the copy that
survives a restart and the copy an import writes. The network's copy exists because the
class fixpoint reads it once per in-region node per worklist pop, under the dense
representation's exclusive write stamp: on the disk store that read is a lock and a slot
decode, and on a server store a round trip, so the resident copy is what keeps
[locality](#2-locality) a claim about every representation. It is also the only copy
`preview` can move — a suspended premise is suspended in the network alone, which is
what makes that retraction reversible without writing a frame.

### Strength propagates from the antecedents

A justification confers **`min(its own strength, the weakest of its antecedents'
classes)`**, where a rule's own strength is read off its defeasibility:

- a **bare rule** confers `:monotonic` — it adds no defeasibility of its own, so the
  conclusion is capped by whatever it rests on;
- a **`set/defaultRule`** confers `:default` — it introduces defeasibility, so its
  conclusions are always `:default`.

A conclusion is therefore no stronger than the weakest thing it rests on: a bare rule
over a merely-default premise concludes a *default*, the same bare rule over known-true
facts concludes `:monotonic`. **The taxonomy edges a firing names are grounds like the
facts** — a `genl` edge a subsumed match climbed, a `genlCx` edge the conclusion's context
reads the rule or the facts over ([contexts.md](contexts.md)) — and cap it the same way.
The **informant is excluded** from the cap.

A rule's own class (`:strength` — `opts :strength` at the door, what `defeat-class` answers
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
firing named, the conclusion comes back as a re-derivation at a fresh handle.

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

The region is also **the answer to a question callers ask**, which is why `settle`
publishes it rather than discarding it. Three readers want the same thing — a
consequence preview, a consequence report, and a change feed
([preview.md](preview.md), [feed.md](feed.md)) — and each of them would otherwise diff
the believed set, which is O(KB) per write and flat in nothing. `settle-finish` decides
once what the settle moved (the relabelled regions plus the flips no relabel records)
and hands that one answer to all three. What that region collects is a **superset** of the
handles whose belief flipped, on purpose:
[why](defenses.md#the-touched-window-is-a-superset-not-the-flip-set).

Measured, on an in-memory graph of N premise→conclusion pairs (no store in the way).
Each cell is a whole-graph relabel against the region-scoped one, so the pair reads as
what locality is worth at that size:

| nodes | `add-justification` | `defeat` | `clear-defeats!` | `sweep!` (2 nodes) |
|-------|--------------------|----------|------------------|--------------------|
| 500   | ~760µs / **~18µs**  | ~3,100µs / **~9µs** | ~2,800µs / **~2µs** | ~150µs / **~38µs** |
| 1000  | ~1,300µs / **~20µs** | ~5,600µs / **~9µs** | ~4,600µs / **~2µs** | ~340µs / **~40µs** |
| 2000  | ~2,100µs / **~20µs** | ~8,200µs / **~9µs** | ~8,100µs / **~1µs** | ~540µs / **~41µs** |
| 4000  | ~4,000µs / **~20µs** | ~17,000µs / **~8µs** | ~16,000µs / **~1µs** | ~1,200µs / **~48µs** |
| 8000  | —                  | —                | —                | ~2,500µs / **~40µs** |
| 16000 | —                  | —                | —                | ~5,600µs / **~46µs** |

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
- `relabel` (the whole-graph version) has **no engine caller at all**. The assert /
  retract / settle path relabels regions, and a rebuild composes the region relabels its
  own adds run rather than closing with a global pass (`core/rebuild-tms`), because a
  region relabel over the affected closure is equal to a global one. What `relabel` is
  for is the differential oracle: a whole-graph operation both representations implement,
  so the two can be compared on one.

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
each door's docstring says what a stored-but-disbelieved answer is for. `believed-…` takes
the KB, because belief is a question about the KB — and it filters with `in?`, which drops a
superseded spelling along with a defeated one, so a believed door means what
`kb/sentexes-matching` means. A door is a wrapper and never a rewrite: one call to the
protocol method it names, the same laziness, the same count-aware path, so it adds no index
operation. The cardinalities, the vocabulary roster and the watched-rule roster carry one
door each, and each says why there is no second.

`lein lint`'s **E16** is what makes it a boundary rather than a habit: a raw index read
anywhere under `src/` but the implementers fails, and the roster in that check is the one
place an exception is written down. The implementers are the doors themselves, the protocol,
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

**The seam is the representation, not the algorithm.** Both run the same least fixpoint
over the same affected region, because that is the semantics of belief here and not an
implementation detail; what differs is where a node's premise flag, depth and adjacency
live. `jtms_dense_oracle_test` compares the two in full after every step of randomized
operation streams; plain `lein test` runs the whole engine through the default dense one,
and `VAELII_TEST_TMS=reference lein test` through the persistent-map baseline.

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

**No stored antecedent vector is in arrival order**, because belief reads it as a set and
every *report* reads it as a list. Three of the seven builders get there by **sorting on
content** (`kb/antecedent-order`) — forward chaining's two placement sites and
`special/derive-equality`, the three handed a vector whose order is an arrival. The order
is the sentence then the context — a **structural** key, walked in place by
`nm/compare-form` rather than printed, so no ambient `*print-length*` can elide two long
sentences to one prefix and drop the tie back onto arrival — and the informant is ordered with the rest
rather than pinned to a position (the record names it in its own `:informant` slot, and
symbol informants like `rewriteOf` are no part of the vector at all). Nothing reads a
position — `valid?` and `has-justification?` read the set, and `why` lifts the rule out by
identity.

**The other four build the vector positionally instead, and the position is a role.**
`special/deduce-lift` writes `[fact, declaration]`, `special/justify-twin!` writes
`[original, equality edge]`, and `special/entail-arg-type` writes `[fact, declaration,
genl edges…]` — each slot filled by what that supporter *is* to the derivation, so there is
no arrival to sort out; the tail of the third is `checks/edge-support`, a shortest
**visible** path expanding in name order. The fourth, `io.import/import-justifications!`,
remaps a dumped vector handle for handle, carrying the exporting KB's order across.

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
is a `get-sentex` per antecedent. A rule handle is an antecedent of every
firing it licenses, so `dependent-justifications` pays that multiple on the whole history:
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

**Recovery starts unblocked**, because it starts from an empty network: nothing about an
exception is stored, so the blocked set cannot be read back from the durable store, and
`core/rebuild-tms` has nothing to clear. The window between the rebuild and the caller's
re-evaluation believes an excepted conclusion; the next settle withdraws it, and it
*replaces* the set rather than merging into it — merging could only ever add, leaving a
block standing for a justification whose exception no longer holds (the bug
[taxonomy.md](taxonomy.md) records for the transitive closures). The whole-graph
`relabel` clears both the blocked set and the supersession map for that same reason.
`retract!` prunes the blocked set of swept justification ids for the same reason too: a
stale id must not survive to be reapplied.

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
   Three sources:
   - every believed `(not X)` paired with a believed `X` **when some context sees
     both** (`negation-nogoods`), asked each round;

     Two narrowings. **Which bodies could pair at all** is the `:opposed` coincidence
     set — the bodies stored in *both* polarities, maintained O(1) at the store and
     removal choke points — so a KB with no contradiction does one emptiness read.
     **What each of those bodies pairs** is memoized per body, re-derived only for the
     bodies a settle could have moved. Three things move a body's pairing and no one of
     them sees the other two: a relabel (`jtms/touched`), a store or a removal
     (`kb/note-opposed!` — the removal case only this covers), and a `genlCx` edge, which
     can make standing pairs jointly visible without going near either side; the last is
     answered by recording each entry's visibility **verdict** (`common-descendant?` of
     one context from each polarity), so a context edge that leaves every recorded verdict
     standing re-derives nothing. Why the memo rather than a query per pair per settle:
     [why](defenses.md#the-settle-memoizes-standing-clashes).
   - the **definitional clashes** — disjointness, functionality, asymmetry — each of
     which convicts by naming a second believed sentex, which is a nogood in exactly
     the same sense (`constraint-nogoods`). Discovered by re-running the checks over
     the settle's moved region, so a pair is a function of current belief rather than
     an accumulation, and priority sits **above** every rebuttal: these rank 3–4 where
     a rebuttal ranks 1–2. A pair whose members and vocabulary did not move has its
     answer **carried forward** — the separations, predicate properties and disjoint
     metatypes' membership compared as **values**, and the `genl` closure (too big to
     compare) weighed per pair by stamping the two supertype closures a `disjoint?`
     reads, while a `genlCx` edge retires the whole carry. Why the memo, and how the
     carry stays sound: [why](defenses.md#the-settle-memoizes-standing-clashes).

   - a stored claim against a **known-true claim reached by argument preservation**
     (`preserving-nogoods`), where the second side of the pair was never stored at all.
     `(largerThan dog cat)` asserted `{:strength :monotonic}` reaches `(largerThan
     chihuahua maine_coon)`, and a stored `(not (largerThan chihuahua maine_coon))`
     denies a claim with no handle — `:opposed` holds bodies stored in *both* polarities
     and this body is stored in one. The members are the stored claim together with
     everything the reading rests on: the general claim, the declaration that permits the
     move, the relation edges the reach travelled, and any `(transitive R)` or
     `(symmetric …)` the reading hangs on besides. That is what makes it a nogood in the
     ordinary sense — an inherited claim has no sentex to defeat *instead of* its
     reasons — and it is the whole of the belief consequence, since `decide-nogood` then
     weighs the set as it weighs any other and the weakest member decides.
     [inherit.md](inherit.md) has the readings that follow, and why a `:default` general
     claim produces no pair at all. Priority is the rebuttal range: two claims disagree
     about the world, and no declaration of what the vocabulary means has been violated.
     Discovery is the settle's region, the pairs already standing (`:preserved-clashes`,
     which is `:clashes`' job done for a candidate rather than for a pair), and the
     extents of the predicates whose *licence* the region moved — the one channel neither
     of the first two can see, since a `genl` edge changes what reaches whose tuple
     without either side of the pair going near the region. Gated on `kb`'s `:preserving`
     roster, maintained at the same choke points as `:opposed` and from the sentence's
     shape alone, so a KB declaring no preservation is told so by one `empty?` rather
     than by an index read on the path every assert runs.

   The argument constraints (`arg` / `genlArg` / `interArg`) are deliberately
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
3. Resolve each nogood from its members' **defeat-classes** (`decide-nogood`), read over
   the whole member set rather than over two — a nogood is a set that must not hold in
   full, and `antiTransitive` forms one over three sentexes:
   - **a unique weakest member** → defeat it. No solver. (Monotonic beats default.)
   - **a minimum shared by several, and defeasible** → a **dilemma**. Every member stays
     believed at `:default` and the set is reported by `contradictions`. Nothing is
     arbitrated.
   - **a minimum shared by several `:monotonic` members** → irreducible; report it in
     `conflicts` (never throw).
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

### A revived datum is a datum the agenda has not seen

Step 1's revival is a **relabel**, and a relabel is only half of what a revival owes. It
brings back everything that is still stored — the defeated default, and the conclusions
resting on it, which a defeat withdraws without sweeping because they stay groundable.
What it cannot bring back is a conclusion that was never derived, and while a datum is
OUT there is a whole class of those: `chain/*matcher*` is belief filtered, so an OUT
datum is not a match, and a rule's *other* antecedent arriving meanwhile joins against
nothing and attempts no firing at all.

Nothing else in the settle can find that firing afterwards. It holds no justification,
so it is in no blocked set for `released-rules` to read; it reached no placement, so it
left no entry for `released-refusals` to re-ask ([exceptions.md](exceptions.md)). And
the record that *would* cover it is the wrong shape — one entry per refused firing is
bounded by what a rule declined to place, where one entry per **non-match** is bounded
by nothing. So the trigger is read where the belief moved rather than where a firing was
declined: `settle` re-seeds the revived datums onto the chaining agenda and the ordinary
fixpoint does the rest.

**Which datums those are is the whole of the cost question**, because a relabelled
region is mostly datums that did not move, and everything the window *created* reads as
newly believed too. The JTMS keeps three sets per window, cleared together when `settle`
finishes with them:

| | |
|---|---|
| `touched` | the relabelled regions — a superset of every handle whose belief could have moved |
| `touched-in` | of those, the ones already believed when the window first relabelled them |
| `touched-new` | the ones whose **node this window created** |

`jtms/revived` is `touched` minus both, filtered to what is believed now. The middle
column is what the change feed and `preview` already read to say which way each handle
moved ([feed.md](feed.md)); the third exists for this and only this. Without it every
asserted fact and every conclusion drawn from one would be re-seeded, since each is in
its settle's region, believed at the end of it and not at the start — which is a second
forward chain over the whole window, on the hottest path in the engine. The distinction
exists only at the moment of creation: by the time the relabel runs, a brand-new node and
one that has been OUT for a hundred settles are both unbelieved nodes about to become
believed, and nothing in the graph tells them apart.

The seeds are **datums**, so re-chaining one costs what asserting it costs — a join per
rule keyed by its predicate. Seeding the *rules* instead, which is the granularity the
three exception triggers work at, joins each rule over its whole extent, and here that is
a different asymptotic rather than a constant: re-chaining one datum of a two-antecedent
rule is linear in the partner's extent where re-chaining the rule is linear in the
product. Measured on that rule at n facts a side, both arms deriving nothing new because
every conclusion is already placed:

| | one datum | the rule | |
|---|---|---|---|
| n=80 (6,400 conclusions) | ~3 ms | ~220 ms | ~76x |
| n=240 (57,600 conclusions) | ~8 ms | ~2 s | ~240x |

So the gap widens with the KB rather than sitting at a constant, which is the answer to
whether the re-check triggers want to be one mechanism: they are one *idea* over
several different populations — the rules a taxonomy edge queued, an aggregate's moved
value, a refused firing's recorded bindings, a relabelled revival, and the spelling an
un-merge gives back — each with an instrument narrow enough for its own, and a single
pass would have to fall back on the widest of them. That is the coarse re-join
[exceptions.md](exceptions.md) measures at 4.9x through the other door.

They split on granularity, and the table above is why. The three that can name a
**datum** — a released refusal's re-derived conclusion, a relabelled revival, and an
un-merged spelling — hand it to `settle/rechain-seeds` and pay what asserting it pays.
The two that cannot name one — a rule queued with `:all` by a taxonomy edge, and an
aggregate whose bound value moved — have only the rule to go on, so they take the
extent-wide re-join through `rechain-exception-rules` and are kept as narrow as possible
at the trigger instead.

A datum is seeded once per settle however many passes run, and a datum that revives and
is defeated again inside one settle is never seeded at all: the set is read after the
resolve, so it describes where the pass landed rather than what it passed through.

A pass that revived something is **productive** even when the blocked set stands still,
for the same reason an aggregate's is: there is no block to move, and without that the
loop would converge having derived nothing.

A **rebuild** stands aside (`settle/*rebuilding?*`): `recover` relabels the whole graph,
so most of what it believes reads as newly believed, and none of it is owed a
re-derivation because the stored justifications it replays already carry everything that
was derived.

#### The other half: a spelling an un-merge gives back

One kind of revival is not in the region at all, and it needs a second channel rather
than a wider net. A datum displaced by an equality merge is OUT while its **twin** joins
in its place, so a partner arriving during the merge concludes at the twin's spelling.
Stop believing the equality — retract it, or withdraw what a derived one rests on — and
the twin is swept while the displaced spelling comes back. The conclusion has to be made
again at the surviving spelling, or the KB believes both antecedents of a forward rule
and holds neither spelling of what they conclude.

Supersession is a belief change with **no relabel behind it**, and deliberately so: a
superseded datum stays in `:in` for `valid?`'s purposes, because its twin is justified
*by it* and forcing it OUT structurally would leave the merge believing neither spelling
([equality.md](equality.md)). So the flip is in none of the three window sets, and
`jtms/revived` cannot be taught to see it.

`special/refresh-supersessions` is where the answer exists — `settle-finish` already
brackets it to tell a caller which way each handle moved — and by then the loop has
converged. So the spellings it gives back go into `settle/*unmerged-sink*`, and **`settle`
re-seeds them and settles again**, the way `core/retract!` already settles twice around
its own re-derivation. Rounds are bounded by `max-unmerge-rounds`; two is the shape of
every real case, and a third would be a bug reported rather than a hang.

Two other designs — moving the reconcile into the settle loop, and a re-enter signal from
`settle-finish` — lose to this one on what they cost elsewhere:
[why](defenses.md#an-un-merge-re-seeds-through-a-second-channel).

### Which door the content came through

One logical situation, one representation: the nogood above, however the content
arrived. The line between refusing and arbitrating is read off the **opposing claim's
defeat class** — the line `checks/asymmetry-problem` draws — and not off which path the
content came in on:

| where the clash arrives | opposing `:monotonic` | opposing `:default` |
|---|---|---|
| a **rule firing** (`place-conclusion`) | placed, then defeated — the loser has a `why-not` | placed; a represented dilemma |
| an **`assert`**, asymmetry / anti-transitivity | refused | admitted; a represented dilemma |
| an **`assert`**, disjointness / functionality | refused | refused, unless the KB arbitrates |
| an **`assert`**, irreflexivity / non-mergeable antisymmetry | refused | refused — there is no opposing sentex, so no pair to arbitrate |

Anti-transitivity opposes **two** claims rather than one, so the column it reads is the
*weakest* of the two chain steps (`checks/opposing-class`): a chain that is known true
throughout refuses the direct step, and a chain with one defeasible step is arbitrated —
where that step, being the unique weakest member, is what the arbitration defeats.

A self tuple `(P a a)` of an `irreflexive` `P`, and a converse no equality could
reconcile under an `antiSymmetric` `P`, are the last row: neither names a second believed
sentex to weigh, so neither is arbitrable and both refuse under every policy. A late
`(irreflexive P)` over a stored self tuple is therefore the `arity` case rather than the
`asymmetric` one — the tuple stands and the mark reports, since a lone-tuple conviction
promoted to a nogood would make belief depend on how many settles had run.

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
is told no, and nobody is being told no here. `antiSymmetric` is the same shape: a
believed converse `(P b a)` beside `(P a b)` forces `(equals a b)` and merges rather than
refuses, `special/derive-antisymmetric-equalities` and `antisym-equate-existing` reaching
it from the fact side and the declaration side under either policy.

Three paths that *mint* content keep refusing either way, because each has somewhere
else to be and nothing to stand behind: the decontextualization lift's copy, the
equality migration's twin, and the gate on what `abduce` may assume
(`checks/constraint-violation`).

### A nogood is a set, and `antiTransitive` is where that stops being academic

`(antiTransitive P)` says a two-step chain forbids the direct step: `(P a b) ∧ (P b c) ⇒
¬(P a c)`. The three cannot all hold, and **no two of them are the clash** — so the
conviction is one nogood with three members rather than three pairs, and the machinery
reads it as the set it is:

- **Discovery** asks each member's own question (`checks/antitransitivity-problems`), and
  a violation names the *other two* in `:opposing-handles` where the pairwise kinds name
  one in `:opposing-handle`. Every member convicts the set — the tuple as the closing
  step, as the first step, and as the second step, which is `chain-triples`' three roles —
  because the discovery walks the sentexes a settle *moved*, and a triple only two of
  whose members could convict it would be found or missed according to which arrived last.
- **Decision** is `settle/decide-nogood`, unchanged in substance and read over the whole
  member set: the **unique weakest** member is defeated, a minimum shared by several
  defeasible members is a dilemma reported whole, and all-monotonic is the irreducible
  conflict. Over two members that is a pairwise decision term for term; over three it says
  what a pairwise engine could not — three equal defaults are one three-sided dilemma,
  and nothing here picks a loser among them.
- **Reporting** follows: `contradictions` hands back one entry whose `:sides` are three,
  and `(contradicts …)` names all three sentences in content order. A caller
  destructuring `:handles` as a pair is reading a coincidence.

The mark is read **up** the predicate hierarchy like every other constraint mark, so
`(antiTransitive parentOf)` convicts a chain spelled in `fatherOf`; the steps are probed
at the marked predicate, so a chain written half at each spelling is one chain. Two
things it deliberately does not do: a step reachable **only** by argument preservation is
not enumerated (that reading is one-sided — see below — and a triple only one of whose
members convicts is one the discovery finds by arrival order), and a self tuple `(P a a)`
— its own whole chain, naming no second sentex — is admitted, exactly as an `asymmetric`
predicate's is. `antiTransitive` does not imply `irreflexive`; the KB that wants the self
tuple refused declares the mark that refuses it.

Its disjointness with `transitive` holds beside all that: no predicate is declared both
([taxonomy.md](taxonomy.md)).

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

There is a single axis, defeat-class, and a default/default clash it cannot separate is
reported as a dilemma rather than decided. The tempting second axis is a **specificity
heuristic** — score by the size of a type's `genl` up-closure and let the more specific
member win a tie — and the engine does not build it:
[why a genl-derived ordering is inference about the knowledge rather than from
it](defenses.md#there-is-no-second-axis).

### Definitional constraints on the derivation path

arg types, disjointness and functionality hold of *derived* content as much as of
asserted content. A rule that concludes `(cat Rex)` where `(dog Rex)` is believed and
the two are declared disjoint has concluded something the KB says cannot be, so a check
that runs on only one path lets a rule quietly produce what `assert` refuses.

`chain/place-conclusion` runs the same three checks `assert` does, and **does not
throw**: chaining is a fixpoint and cannot abort halfway through one without making
the resulting belief set depend on which rule fired first, and the engine's stance is
that contradictions are soft. A failing conclusion is *dropped* — no sentex, no
justification, nothing believed — logged at `:warn`, and recorded in
`(core/violations kb)` as `{:violation <kind> :sentence :context :rule :detail}`, the
kind naming which check refused (`:arg-type`, `:disjoint`, `:functional` and the rest of
the argument-constraint family). Two more kinds ride the same path: a completed firing
with **no placement context** is recorded as `:no-placement`, and a *derived*
`genl`/`genlCx` edge that would close a cycle through negation is dropped and recorded as
`:not-stratified`. A rule a **generator** minted and the rule checks refuse is dropped
the same way, under whichever refusal type the check threw.

Seven kinds on this path drop nothing, and report instead. `:arity` is an arity binding
arriving after facts that do not conform to it, and `:non-confluent` two schematic
equations disagreeing about a shared term. Three of the rest say a **bounded sweep did
not finish**, so bounded work never reads as full coverage: `:exposure-truncated` means
clashes went *unreported*, `:arbitration-truncated` means content a declaration
implicates went *undecided*, so a pair that would have been defeated stands believed
until a later settle surfaces it, and `:arity-truncated` means wrong-length facts went
*unreported* — the `:arity` reach walks the whole spec subtree a binding descends to and
the cone a `genlCx` edge opens, and past the budget the predicates it never reached, and
the ones it never got as far as looking *for*, hold facts neither refused nor
named. They do not cover the same triggers — the disjointness sweeps are the
type-separating declarations and the constraint sweeps the three tuple marks, and the
`genl` edge that carries a mark down is read by both — and each is
one entry per settle rather than one per trigger. What bounds those sweeps is
`settle/*exposure-instance-budget*` ([taxonomy.md](taxonomy.md)).

The other two bound the **report** rather than the sweep, and both mean *found, examined
and not named*, which is a different thing to act on from a sweep that stopped early. A
binding descending a wide subtree convicts more predicates than one settle may file
without evicting everything else from a ledger of 1,000, so the pass files at most eight
`:arity` entries and one `:arity-report-truncated` counting what the cap left out; and
`:constraint-exposure-truncated` says one cross-context constraint pass found more
clashing pairs than it will file, naming whichever bound it met — its cut walk or the
entry cap.

The kinds are not only this path's. An aggregate prover that cannot reduce an extent
files `:aggregate`; the qualitative and metric-temporal networks file
`:qualitative-inconsistency`, `:metric-temporal-mixed-dimensions` and
`:metric-temporal-inconsistency` when a context's constraints cannot be satisfied; and
the sign arithmetic files `:sign-inconsistency` when they leave a quantity with no
possible sign at all — all of them reports, none of them a dropped conclusion. The whole roster, kind by kind with
the `:detail` keys each carries, is the set of tables in `core/violations`' docstring,
and `violation_roster_test` fails on a kind the engine files with no row there, on a row
naming a kind nothing files, and on a row whose `:detail` keys are not the ones the
entry builds.

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
clashes the KB holds — `resources/kb/CxCore.txt` says as much of the predicate
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
 :sides [{:handle :sentence :context :defeat-class :justifications [...]} ...]
 :inherited {:sentence :context :claim handle :via [handle …]}}   ; :kind :inherited only
```

`:inherited` is the one part of a report that is **not** a stored sentex, so it cannot be
a side: the claim nobody wrote, the context it was read in, the handle of the sentex it
was inherited from, and the handles that licensed carrying it there. Every one of those
handles is also a member, so the sides carry them with their own justifications and `why`
explains the reach rather than asserting it. The key is absent on every other kind.

The two differ in *why* the pair was left standing — a defeasible tie the engine
declines to break, or a known-true clash it has no grounds to break — not in what a
caller needs in order to act on one. The known-true case is where the engine has
declined hardest and the application has the most to do, so giving it less material
than the easier case had it backwards.

**`:sides` and `:handles` name the pair in content order, and so does the list of reports
around them** — the same rule the sentence inside `(contradicts X Y)` follows, reaching
the reading a caller actually holds. A nogood is a *set* and the reports are held in a
hash set keyed by handle, so both need linearizing and neither may be linearized on the
handle:
[why](defenses.md#tie-breaks-and-orderings-key-on-content-not-the-handle).

The sides are ordered by sentence, then by context (one sentence can clash with itself
across two contexts) — a **structural** key, compared by `nm/compare-form` rather than
printed. Those two keys are **total**, so there is no third and no handle enters the key
at all: sentence-plus-context is what identifies a sentex, and two sides agreeing on both
are one canonical sentex and one handle, which is not a pair. `report_order_test` reads
that line of `clash-report` and fails on a handle in it. `:handles` is `:sides`' handles
in that order, so the two agree. `conflicts` and `contradictions` take that same key —
sentence, then context — over the reports themselves, and need no handle either, since a
report is already ordered inside.

**The ordering is the read's, not the settle's**, and that is a claim about where the
guarantee lives rather than about whether it holds. `settle` stores the two vectors in
arrival order and `settle/ranked` orders a reading at the point it is asked for;
`conflicts`, `contradictions` and the preview's standing filter each call it, and any
further reader of `settle/conflicts-of` or `settle/contradictions-of` owes the same call.
The two readings and the memo behind them sit in **one** atom, written once per settle:
they describe one settle, and the read doors run on threads beside the writer, so three
atoms would let a reader take one settle's conflicts beside another's contradictions. The
alternative home is the settle path, which a mutation always runs — so ordering there
charges every assert O(standing log standing) comparisons for a reading nobody asked for:
~1.6 ms per assert against 800 standing dilemmas, where ordering at the read costs ~1.1
ms. A reading is asked for far more rarely than a KB is written to.

The sort key rides each report's metadata, built once when the report is built and
carried through the memo, so ordering a reading compares prepared keys instead of
rebuilding every side's per comparison. Nothing inside the engine leans on the stored
order: the labeling solver re-sorts the dilemmas by priority then content for itself,
because an earlier choice constrains every later one
(`vaelii.impl.solve`, and `solve_test/the-result-does-not-depend-on-the-order-the-nogoods-arrive-in`).

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
and 46.5x with the carry-forward removed as well — a couple of microseconds of
bookkeeping per standing pair against tens of microseconds to re-derive one.

That carry is only sound because the region covers every input to a report, and one of
them is not belief: a **redundant justification** moves a conclusion's *reason* without
moving its label, and `add-just*` notes the consequence as touched even on that fast path
(as does `touched-in`) so the report is rebuilt where only the reason changed —
[why the window is a superset rather than the flip
set](defenses.md#the-touched-window-is-a-superset-not-the-flip-set).

Ω(standing) per settle is inherent, though, and no memo removes it: the readings *are*
the whole standing set, so publishing them costs what they are. What the memo buys is
that the per-pair term stays bookkeeping rather than a re-derivation of the checks.

### Who asks the pair's question

Discovery re-checks the sentexes the settle **moved**, and the checks are scoped to the
context they are asked in — a context is convicted only on grounds it can see
([contexts.md](contexts.md)). Where each side of a pair convicts the other that is
enough: whichever side arrives second finds the pair, so the answer does not depend on
which arrived first.

A pair whose halves sit either side of a `genlCx` edge convicts one way only.
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
`:refuse` it stays the reporting path's business — an entry in `violations` naming the
contexts the pair is visible from, with belief untouched. Under `:arbitrate` every route
agrees and the pair is weighed wherever it can be seen whole.

**Every arbitrable kind is reported there, each by its own entry kind.** Disjointness is
the exposure pass (`:disjoint`, above); `functional`, `asymmetric` and `anti-transitive`
are a second pass beside it, and the two differ in what they have to look at rather than
in what they say. A separation reaches back over every instance below the types it
separates, so the disjointness pass sweeps every trigger; a tuple-mark clash needs **both
halves stated**, so on an ordinary write — a region holding facts and no declaration —
its candidates are the moved region's own binary facts and it sweeps nothing.

**Three triggers reach past the region, and they have to.** A `genlCx` edge moves
*visibility*, so a pair whose halves are already stored and already believed becomes
jointly visible without either half being relabelled — neither is in the region, and
reporting the same knowledge only when the edges happened to arrive before the facts is
precisely the arrival-order dependence the pass exists to remove. So an edge in the
region reaches out over the cone it newly sees (`constraint-facts-in-cone`, the
binary-fact parallel of the disjointness pass's `members-in-cone`) and spends the same
`*exposure-instance-budget*` doing it. Past the cap the cost is the cap:
`perf`'s `constraint-exposure-context-edge` holds it there. A `genl` edge moves the
**mark** instead, down to a subtree that carried none, and reaches the subtree's facts —
gated on a mark actually being above it, since `genl` is the commonest edge in an
ontology and one under nothing marked must cost a property read and no more.

**And the mark's own sentence is a trigger, for the same reason.** A late `(functional
P)`, `(asymmetric P)` or `(antiTransitive P)` moves nothing but the mark, so both halves
of every pair beneath `P` sit outside the region — the declaration's arrival order
deciding whether the KB says anything at all. What it implicates is what a `genl` edge
carrying the same mark down implicates, the spec subtree's facts, so the two share an
arm: a mark stands above its own predicate, so the `marks-above?` gate that lets an edge
through lets the declaration through too. Under `:arbitrate` that reach is
`clash-candidates`' sweep and the pair is *weighed*; under `:refuse` it is this pass and
the pair is *named*.

The two answers are different things and the policy is what chooses between them, so
what is order-independent is that the clash is **accounted for** — refused at the door,
weighed into `contradictions`, or named here — and never that every arrival order picks
the same account. A late declaration is not refused: turning away the sentence that says
what the predicate *means* would leave every later use of `P` unconstrained on the
strength of one fact written earlier, which is the failure recorded above
`checks/arbitrable-kinds` for `arity`, one relation over. It is not arbitrated under
`:refuse` either, since `:refuse` is precisely the policy that says a declaration does
not move belief it was not asked to move. `(disjoint A B)` arriving over an
already-clashing pair takes the same three decisions and takes them the same way
(`exposure-candidates`, through `declaration-reach`); the KB owes one answer to "the
declaration came last" whichever declaration it is.

**A candidate a trigger reached is asked from its own context as well as from the
vantages.** The vantages are the contexts *beyond* a sentex's own, which is right for a
candidate the region holds — that one was asked from its own context at the door, and
asking again every settle re-runs a check whose answer has not moved. A candidate a
trigger reached is the opposite case: the mark over its predicate, or what its context
sees, arrived after the door answered. Its own context is the vantage the door would use
today, and for a same-context pair beneath a late mark it is the only vantage there is.

The second pass is **`:refuse`-only**, gated before any root is read, and behind an O(1)
check that the KB declares either property at all. Under `:arbitrate` the vantages are
already asked, so reporting there as well would have the ledger and `contradictions`
both claim one clash — which is also why a pair *this settle arbitrated* is excluded
from both passes. Each entry names the predicate, the `[sentence context]` halves — two
for a pair, three for an `anti-transitive` chain — and the contexts the whole set is
jointly visible from; the halves are ordered structurally by `nm/compare-form` rather
than by which side the region held, so the same knowledge in either arrival order files
the same entry once.

**One sentence stated in two visible contexts is two sentexes**, and a claim that denies
it denies both. The same membership in a general context and in one that sees it can
carry different strengths and different support, so `checks/disjoint-problems` names one
pair per opposing *sentex* rather than per opposing type, and the asymmetric arm does the
same for the converse. `functional-problems` counted its clashes that way from the start.
The asymmetric arm therefore reads its converse twice: `inherit/surviving` answers what is
inherited — one claim per tuple, the strongest — and the sentexes literally stating the
converse are read beside it and merged on the handle.

### Where conviction is one-sided

One shape convicts one way only, **through argument preservation** — and it is the only
one. (`asymmetry-problems` keys *self* on the sentence's own context, `home`, and never
on the vantage it is asked from, which is what keeps `(P a a)` written in a general
context and again in one that sees it a real pair: key it on the asker and the twin
**stored in the vantage** is thrown away as though it were the candidate, and the pair
is reported or not according to which of the two contexts was written last. At the door
the two contexts are one.) `(outranks animal
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

`clash_oracle_test` excludes this shape and says so — no `transitiveInArg` declaration is
made there — and covers the visibility one.

`antiTransitive` stops at the same line rather than crossing it: its chain steps are the
ones `matches-visible` finds over the marked predicate's spec closure, and a step that
exists **only** because preservation reaches it is not enumerated. Reading it would buy a
third one-sided shape — this time inside a nogood whose members have to convict each
other symmetrically — where the fan the mark already needs is symmetric as it stands.

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

`asp_label_test` covers both directions —
[why the guard matters more than a wrong answer would](defenses.md#the-solver-split-is-guarded-in-both-directions).

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
`:disjunction-too-wide` `:not-assertible` `:arity` `:arg-type` `:arg-genl` `:arg-position` `:inter-arg-type`
`:arg-constraint-kind` `:arg-variable` `:disjoint` `:functional` `:asymmetric` `:not-stratified`
`:exception-not-closed`, plus the two about the *request* rather than the knowledge —
`:shape` (the context is not a symbol, the sentence is not an s-expression, or it is a
vector — which is how a query spells a conjunction, so one spelling would store a
sentence and ask a join) and `:unknown-option` (a non-map `opts`, an `opts` key `assert`
does not read, or a `:strength` that is not an assertable class).

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
- **An equality is not defeasible by its own negation.** Once `(rewriteOf Pref Dep)`
  merges the two, every sentence naming `Dep` is rewritten — including
  `(not (rewriteOf Pref Dep))`, which is stored as a claim about `Pref` alone and so
  clashes with nothing and defeats nothing. The ways an equality stops being believed are
  retracting it and withdrawing what a *derived* one rests on; both un-merge, and both are
  re-seeded ("The other half" above).

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
defeat of the witness in the network, and after a scoped defeat or an `except` of it at each
reader that still reaches ("Where the layer stops" states what the re-derivation leaves
stored).

Decision 8 of [reference.md](reference.md#decisions) reverses the refusals this
section describes: no clash is refused, and order independence holds over the writes
offered rather than the writes stored.

**The invariant is over beliefs, and the store is held to it only where the entry point
lets it be.** `assert` answers a writer, and it answers from the KB in front of it: a
sentence that violates a definitional constraint the KB reads *now* is refused now, and
nothing records that it was offered. Under `:refuse` that is the whole of the policy — a
writer is told no about any clash the KB can see — so the same three sentences in two
different orders can leave two different stores, and the orders that store agree about
every belief. Under `:arbitrate` the refusal is narrowed to what no later assertion could
change, which is the next paragraph.

**What a refusal may rest on.** Under `:arbitrate` a definitional clash refuses only when
*both* halves of it are known-true: the sentex the newcomer opposes, and the **derivation**
that makes the two a pair — the separation between two types, the functionality
declared of a predicate, or the cover declared of a whole, together with the `genl` steps
each is read over (`checks/grounds-class`, `taxonomy/disjointness-class`). A pair resting on a `:default`
link is a pair a later denial of that link retires, after which the sentence is believed
like any other; refusing it would throw away, on the strength of what had not been written
yet, content that the KB goes on to hold. So the derivation's class bounds the refusal, the
way the *weakest* step of an `anti_transitive` chain bounds a refusal there rather than its
endpoints. A clash every link of which is known-true is one no assertion can retire, and it
still refuses.

The shipped upper ontology declares its own separations and functionalities known-true
(`resources/kb/upper/`, `(set/monotonic (disjoint …))`), so a clash between two types it
separates directly refuses exactly as it did. What moves is a clash reached over a
defeasible `genl` edge, which is the case
[a defeat is scoped to its vantage](#a-defeat-is-scoped-to-its-vantage) is about.

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

**Every method is in one of eight roles, and the protocol says which.** The network is
one function — `label(graph, attributes, blocked, defeated) -> (in, groundable, classes)`,
with `believed = in - superseded` — so a method either supplies an argument, reads a
result, or edits the domain. `jtms-protocol/roles` writes the division as data and
`jtms_protocol_test` holds it. The division is of what a method *touches*, never of what a
network may be implemented without: every mutation relabels, so every role's mutators
write the output role's state.

The three sets a caller replaces whole each settle are three roles rather than one,
because they enter belief at three different points:

| override | enters at | moves | decided by |
|---|---|---|---|
| `blocked` | inside `valid?`, so a blocked justification supports nothing | `in` **and** `groundable`, so an excepted conclusion is swept | the `exceptWhen` re-evaluation, bounded by the recheck queue's triggers |
| `defeated` | inside the fixpoint, as a datum forced OUT | `in` only, so a defeated datum revives when the defeat clears | nogood discovery, bounded by `:opposed` intersected with the moved bodies |
| `superseded` | subtracted at the read, after both fixpoints | neither — the datum stays in `in` so its rewritten twin keeps its justification | the equality closure |

None of the three is computed by the network, which holds no KB. Each method applies a set
it was handed, so its cost is the region that set seeds and never the cost of deciding the
set. A **fourth** place belief is decided is not on the protocol at all: a scoped defeat
and a visibility `except` are applied per reading context above it, over
`jtms/grounded-in-region`, and the network's labels do not move for either (*[A defeat is
scoped to its vantage](#a-defeat-is-scoped-to-its-vantage)*).

The eighth role, `:hold`, is the settle's and not the fixpoint's. A settle lifts every
standing defeat before it re-decides any, so for a reader on another thread it holds the
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
answer in with `set-blocked`, which *replaces* the set rather than adding to it, as the
defeated set is replaced. A block therefore holds only while its exception holds now,
whatever order the exceptions were discovered in.

Blocking is **not** defeat. A defeated *datum* is forced OUT but keeps its support and
stays `groundable`, so it can revive. A blocked *justification* is invalid: it supports
nothing, confers no defeat-class (`node-class` never reads a blocked justification's
strength), and does not make its consequence groundable, so the retraction sweep deletes
an excepted conclusion ([exceptions.md](exceptions.md#garbage-collection-not-defeat)).

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
delete every datum in the retracted datum's consequence closure that ends OUT and
ungroundable. A defeated datum keeps its support and is retained for revival, and a
datum with another derivation survives. The closure it marks **is** the region it
relabels, so the two walk the graph once between them, and the sweep reads the
`:groundable` set that relabel just recomputed.

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

1. `clear-defeats!`, which relabels the previously-defeated region, then
   `clear-scoped-defeats!`. Previously-defeated defaults return, so revival can happen.
2. Find the active **nogoods**: sets of believed sentexes that cannot all hold. Three
   sources:
   - every believed `(not X)` paired with a believed `X` **when some context sees
     both** (`negation-nogoods`), asked each round. Only bodies stored in both
     polarities (`:opposed`, maintained O(1) at the store and removal choke points) are
     looked at, so a KB with no contradiction does one emptiness read, and each such
     body's pairing is memoized and re-derived only where the settle could have moved it
     ([The negation memo](#the-negation-memo),
     [why](defenses.md#the-settle-memoizes-standing-clashes)).
   - the **definitional clashes** (`constraint-nogoods`): a disjointness, cover,
     functional, asymmetric or anti-transitive violation (`checks/arbitrable-kinds`)
     convicts by naming other believed sentexes, which is a nogood in the same sense.
     Discovered by re-running the checks over the settle's moved region, so a pair is a
     function of current belief. Priority sits **above** every rebuttal: 3–4 against 1–2. A pair whose
     members and vocabulary did not move has its answer **carried forward**: the
     separations, predicate properties and disjoint metatypes' membership are compared as
     values, the `genl` closure is weighed per pair by stamping the edges out of the two
     supertype closures a `disjoint?` reads, and a `genlCx` edge retires the whole carry
     ([why](defenses.md#the-settle-memoizes-standing-clashes)).
   - a stored claim against a **known-true claim reached by argument preservation**
     (`preserving-nogoods`), whose second side was never stored. `(largerThan dog cat)`
     asserted `{:strength :monotonic}` reaches `(largerThan chihuahua maine_coon)`, and a
     stored `(not (largerThan chihuahua maine_coon))` denies a claim with no handle. The
     members are the stored claim and everything the reading rests on: the general claim,
     the declaration that permits the move, the relation edges the reach travelled, and
     any `(transitive R)` or `(symmetric …)` the reading hangs on. An inherited claim has
     no sentex to defeat instead of its reasons, so `decide-nogood` weighs that set as it
     weighs any other. Priority is the rebuttal range. Discovery reads the settle's
     region and what it re-opens, since a `genl` edge changes what reaches whose tuple
     without either side going near the region, and carries a standing clash whose
     inputs did not move ([The inherited-clash memo](#the-inherited-clash-memo)). A KB
     whose `:preserving` roster is empty pays one `empty?`. [inherit.md](inherit.md) has the readings, and why a
     `:default` general claim produces no pair.

   The argument constraints and `arity` are not nogood sources; the table in
   [What qualifies as a nogood](#what-qualifies-as-a-nogood) gives the reason for each.
3. Resolve each nogood from its members' **defeat-classes** (`decide-nogood`), read over
   the whole member set:
   - **a unique weakest member** → defeat it. No solver. (Monotonic beats default.)
   - **a minimum shared by several, and defeasible** → a **dilemma**. Every member stays
     believed at `:default` and the set is reported by `contradictions`.
   - **a minimum shared by several `:monotonic` members** → irreducible; report it in
     `conflicts` (never throw).
4. Loop until no active nogood remains.

Steps 1 and 3 run region-locally; step 2 does not. A relabel is a belief fixpoint over
the consequence justifications, held to the affected region by [Locality](#2-locality).
Step 2 reads no justification edge: it asks whether some context sees both a believed `P`
and a believed `(not P)`, a walk over the `genlCx` lattice, so a `P` and a `(not P)` many
contexts apart pair on the same terms as two in one context. Its cost is bounded by the
`:opposed` set and the change, not by a region. Locality is by **range**, and range cuts
across the eight roles:

| range | what is in it | bounded by |
|---|---|---|
| support-graph-local | labels, `groundable`, the class fixpoint, applying a defeat, the sweep | the affected region |
| lattice-ranged | nogood discovery — does some context see both a believed `P` and a believed `¬P` | `:opposed` intersected with the moved bodies |
| query-ranged | the `exceptWhen` re-evaluation that fills `blocked` | the recheck queue's triggers |
| reader-ranged | a scoped defeat, a visibility `except`, and the conclusions resting only on one | the forced-OUT set's forward closure, per reading context, cached per reader between settles |

A protocol method's locality claim is about applying a set, never about computing one.

A default/default clash is **not** decided: defeat-class is the only axis
([There is no second axis](#there-is-no-second-axis)). Where one rule names the other's
case, [`exceptWhen`](exceptions.md) settles it structurally and no contradiction forms.
Where neither does (the Nixon diamond), the clash is a dilemma the engine reports.

No nogood the settle discovers reaches the `Solver` below: `decide-nogood` returns a
defeat, a dilemma or a hard clash, never a contested set, so `resolve-contradictions`'
solver branch has no shipped caller (`solve_test` drives the stub as a unit). The solver
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
| `negation-nogoods` | the believed `P` and the believed `(not P)` | joint visibility — `tax/maximal-common-descendant-contexts` of one context from each polarity | no member supports the visibility verdict, and defeating either side removes one of the two claims the pair was about |
| `constraint-nogoods` | the clashing sentexes alone. The entry is keyed on the **handle set**, and the separations, predicate properties and disjoint metatypes are `clash-vocabulary`, read through and never members | the separating declaration and the `genl` closure | no defeat this nogood licenses can unmake the reading that convicted |
| `preserving-nogoods` | the stored claim **and its reasons** — the general claim, the declaration permitting the move, the relation edges the reach travelled, any `(transitive R)` the reading hangs on | the same reasons, which here *are* members | defeating a reason withdraws the reach, which is what the pair was about, and the reason stays defeated |
| **not** `arity` | would be the offending sentex plus the `(arity P n)` declaration | `declared-arity`, a cache that follows belief | defeating the declaration unmakes the conviction while the offending sentex stands, so the clash is decided once and never again. It reports instead ([taxonomy.md](taxonomy.md#what-each-constraint-does-in-each-arrival-order)) |
| **not** `arg` / `genlArg` / `interArg` | there is no second sentex | the **absence** of a path — an open-world NAF judgement | nothing to weigh and no class to compare. A refusal at the entry point, a drop on the derivation path |

`nogood_admissibility_test` pins the first three rows: a definitional clash's `:nogood`
set holds the clashing sentexes and not the declaration that convicted them, and an
inherited clash's holds its reasons.

### The negation memo

`negation-nogoods` keeps `{:vocab :by-body :views :dirty}` in `(reasoning/negations kb)`.
Each opposed body's entry holds its nogoods and the contexts each polarity is believed in
(`body-nogoods`). A settle re-derives the bodies three inputs name, and carries every
other entry forward:

- **the relabelled region** (`jtms/touched`, read through each touched handle's record).
  It covers an arrival, and a belief change with no store behind it: a second
  justification from a `:monotonic` premise lifts a conclusion's class and moves a
  standing pair's `:priority` with nothing written about either side.
- **`:dirty`**, the bodies a store or removal posted (`kb/note-opposed!`). Only this
  covers a removal: the retracted record is gone by the time the settle looks, so its
  handle cannot name its body.
- **a `genlCx` move.** Joint visibility is read through that closure, so an edge can make
  a standing pair visible without touching either side. `:views` records, per context
  pair an entry crosses, `tax/maximal-common-descendant-contexts`; when the relation's
  generation moved, `moved-verdicts` re-reads those verdicts and `bodies-crossing` names
  the entries whose verdict changed. A context edge that leaves every verdict standing
  re-derives nothing
  ([why not a generation counter](defenses.md#a-context-edge-re-derives-the-negation-pairs-whose-verdict-moved-not-every-pair)).
  `:views` is pruned only on a full re-derivation.

A supersession flip is a fourth belief change that neither the region nor `:dirty` sees:
`in?` subtracts the superseded set, so a spelling an equality merge displaces stops
pairing while its label stays. `settle-finish` posts the flipped handles' bodies to
`:dirty` (`note-supersession-flips!`), and the next settle re-derives them. Displacing a
body normally carries its entry unchanged, since the twins are written on the
representative's body; the hand-off matters only when the displaced body is re-derived
during the merge window, which drops the entry. `negation_oracle_test` does not generate
that shape.

The carry is sound because a carried entry's pairs and `:priority` are functions of two
handles' belief and defeat classes, which move only inside a relabelled region. A carried
entry is not live: a member defeated later in the same settle leaves it standing, so
`resolve-contradictions` filters every nogood on belief (`live-vantages`) before deciding.
An entry with a polarity believed nowhere is dropped, since only a relabel can revive it.
The `:opposed` set cannot miss a symmetric pair: `sentex/sentex` normalizes the body
before the `not` wraps it, so both polarities key under one body.

`scan` carries the region's record reads across one settle's defeat rounds: the region
only grows between rounds, so each round reads the records of the handles the previous
round did not see. The memo is written back by compare-and-set, carrying every `:dirty`
post that landed during the re-derivation and dropping those bodies' entries, since
`note-opposed!` writes the same atom from the store and removal choke points. An empty
`:opposed` resets the memo to `{}`; with no `:vocab` stamp the next settle re-derives the
whole opposed set, as it does on a fresh KB and after `recover`.
`*incremental-negations*` bound false re-derives every opposed body on every call, the
reference `negation_oracle_test` compares against step by step.

### The inherited-clash memo

`preserving-nogoods` keeps `{:stamp :entries :seen}` in `(reasoning/preserved-clashes
kb)`. `:entries` maps a stored claim to its last answer (`settle/preserving-entry`): the
nogoods, every context asked, and the defeat-class of every member. `:seen` holds each
asker's withdrawn set as that answer read it. A settle republishes the entries, which is
O(standing) bookkeeping, and asks again only where an input moved:

- **a member.** An entry is asked again when a member other than the stored claim is OUT
  or holds another class, which also covers a supersession flip no region shows. The
  stored claim's own belief is not an input, since its question reads the tuple's other
  claims. An entry whose stored claim is OUT publishes nothing and stays, because
  `clear-defeats!` revives every loser at the next settle.
- **the reading's vocabulary.** A handle in the region, or one whose withdrawal at an
  asker moved (`res/withdrawn-set` against `:seen`), re-opens the whole stored extent of
  every predicate a non-claim channel of `inherit/moved-channels` names: a declaration, a
  relation edge the reach can cross, a `(transitive R)` or a mark. A `genl` edge between
  predicates re-opens every preserved predicate above either end.
- **a claim.** A moved claim re-opens the stored facts it reaches
  (`inherit/claim-reach-extent`), and not the extent, when it can change an answer:
  believed and known-true, since `clashing-claim` reads known-true claims alone, or of a
  predicate holding an entry asked from vantages, whose set `inherit/denial-contexts`
  reads off claims of every class. A known-true claim leaving is a member of every entry
  it answers, and a scoped defeat never withdraws known-true content.
- **the stamp.** The `genlCx` generation, the contexts each flat-cache entry is asserted
  from (`tax/flat-contexts`) and the `except` roster, compared as one value. A retraction
  in the region re-asks every entry too, since its record is gone.

A stored claim asked and finding no clash is kept as an entry with no nogoods in two
cases. While `inherit/denial-contexts` names a claim that would deny it in a reader seeing
both, the `genlCx` edge that makes such a reader moves the stamp and asks it again; this is
the negation memo's body stored in both polarities and seen jointly nowhere. While an asker
reads something withdrawn, the next settle clears the scoped defeats, and its withdrawal
diff asks the claim again. A stored claim with no entry has no clash in any reader the
lattice could add, and the region and the re-opened facts are the writes that can give it
one.

`*incremental-preserving*` bound false carries nothing and re-opens the whole extent for
every moved claim, the reference `inherited_clash_oracle_test` compares against step by
step; its streams do not generate the supersession shape. `lein perf`'s
`inherited-clash-arbitration` and `inherited-clash-arbitration-split` hold the per-assert
cost against the standing set.

### A revived datum is a datum the agenda has not seen

Step 1's revival is a **relabel**, which brings back everything still stored: the
defeated default, and the conclusions resting on it, which a defeat withdraws without
sweeping because they stay groundable. A relabel cannot bring back a conclusion that was
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
*created* reads as newly believed too. The JTMS keeps three sets per window, cleared
together when `settle` finishes with them:

| | |
|---|---|
| `touched` | the relabelled regions: a superset of every handle whose belief could have moved |
| `touched-in` | of those, the ones already believed when the window first relabelled them |
| `touched-new` | the ones whose **node this window created** |

`jtms/revived` is `touched` minus both, filtered to what is believed now. The change feed
and `preview` read `touched-in` to say which way each handle moved ([feed.md](feed.md));
`touched-new` exists only for `revived`. Without it every asserted fact and every
conclusion drawn from one would be re-seeded, since each is in its settle's region,
believed at the end of it and not at the start, and the window would be chained twice.
The distinction exists only at the moment of creation: by the time the relabel runs, a
new node and one that has been OUT for a hundred settles are both unbelieved nodes about
to become believed.

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
aggregate's is, or the loop would converge having derived nothing. A **rebuild** stands
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

`special/refresh-supersessions`, which `settle-finish` brackets to tell a caller which
way each handle moved, is where the flip is known, and by then the loop has converged.
So the spellings it gives back go into `settle/*unmerged-sink*`, and **`settle` re-seeds
them and settles again**, as `core/retract!` settles twice around its own re-derivation.
Rounds are bounded by `max-unmerge-rounds` (8); two is the structure of every real case,
and reaching the eighth is logged as a bug rather than looping. Two other designs, moving
the reconcile into the settle loop and a re-enter signal from `settle-finish`, cost more
elsewhere: [why](defenses.md#an-un-merge-re-seeds-through-a-second-channel).

### The set-membership states a node can hold

A node carries two independent descriptions, one persistent and one per-settle. Its
**belief state** is read from the datum-keyed sets `:in` and `:groundable`, the
`:defeated` set and the `:superseded` map, and it survives across settles. Its **window
position** is read from `:touched`, `:touched-in` and `:touched-new`, and
`reset-touched!` clears those three at `settle-finish`, so a window position exists only
during the settle that wrote it. `:blocked` is keyed by justification id rather than by
datum, so it names no node state of its own; a block reaches a node through `valid?`,
which reads it in both fixpoints.

One asymmetry between the two fixpoints generates the belief states. `relabel-region*`
computes `:in` by forcing the `:defeated` set OUT and computes `:groundable` by forcing
nothing OUT. Both pass the same `:blocked` set to `valid?`. So a defeat is the only thing
that holds a node in `:groundable` while keeping it out of `:in`, and a block or a lost
derivation removes a node from both. A defeated node stays groundable and returns when
`clear-defeats!` empties the set; a node with no groundable derivation is the sweep's
target.

Reported belief — the answer `in?` gives — is `:in` minus `:superseded`, because a
superseded spelling stays in `:in` to keep its rewritten twin's justification valid even
though it no longer matches. Writing a node's membership as (in, groundable, defeated,
superseded), the invariants `:in ⊆ :groundable`, `defeated ⇒ not :in` and
`superseded ⇒ :in` leave five belief states:

| belief state | in | groundable | defeated | superseded | `in?` |
|---|:--:|:--:|:--:|:--:|:--:|
| believed | ● | ● | | | yes |
| superseded | ● | ● | | ● | no |
| defeated | | ● | ● | | no |
| held OUT by a defeat | | ● | | | no |
| no groundable derivation | | | | | no |

A `believed` node is a premise or a datum with a valid justification. A node `held OUT by
a defeat` has every derivation running through a defeated supporter, so it is OUT now and
returns when that defeat clears. A node with `no groundable derivation` has no premise and
no derivation even with defeats ignored: a retraction sweep deletes it, and one still
present in `:nodes` is one a sweep has not yet reached.

Crossed with the window position the most recent settle left the node in, eighteen of
the twenty pairs occur:

| belief state \ window | boundary | revival slot | touched-in | touched-new |
|---|:--:|:--:|:--:|:--:|
| believed | ✓ | ✓ | ✓ | ✓ |
| superseded | ✓ | ✓ | ✓ | ✓ |
| defeated | — | ✓ | ✓ | ✓ |
| held OUT by a defeat | — | ✓ | ✓ | ✓ (a rebuild only) |
| no groundable derivation | ✓ | ✓ | ✓ | ✓ |

The **revival slot** is `:touched` without `:touched-in` or `:touched-new` — a datum this
settle relabelled that was neither believed at the settle's start nor created by it.
`jtms/revived` reads that slot filtered to what is believed now, so a believed node in the
revival slot is a `revived` one. A believed node created this settle sits under
`touched-new`, and a believed node the settle relabelled without moving its label sits
under `touched-in`.

One mechanism rules out the two absent pairs, and a second confines a third pair to a
rebuild:

- A **defeated** node and a node **held OUT by a defeat** are never boundary nodes.
  `clear-defeats!` resettles the previously-defeated set every settle and `defeat`
  resettles the newly-defeated set, so a defeated node is relabelled every settle it stays
  defeated. `affected-region` is that node's forward consequence closure, so every node the
  defeat holds OUT is relabelled with it.
- A node **held OUT by a defeat** is `touched-new` only in a rebuild. On the write path,
  creating a node's TMS node needs a justification whose antecedents matched, and the
  matcher reads only believed antecedents (`chain/*matcher*`), so a datum enters at
  creation with valid support and lands believed; it reaches the held-OUT state only when
  a later defeat lands on a supporter of a node that already had a TMS node.
  `recovery/rebuild-tms` creates a node for every stored sentex with no matcher, and
  `recover`'s first settle runs in the same window, so a conclusion resting on a default
  that settle defeats is held OUT and `touched-new`.

A node in the revival slot under the defeated or held-OUT state is one the
`clear-defeats!` pass returned to `:in` for the round and the re-defeat then put back OUT.

### Which entry point the content came through

One logical situation, one representation: the nogood above, however the content
arrived. The line between refusing and arbitrating is read off the **opposing claim's
defeat class** — the line `checks/asymmetry-problem` draws — and not off which path the
content came in on:

| where the clash arrives | opposing `:monotonic` | opposing `:default` |
|---|---|---|
| a **rule firing** (`place-conclusion`) | placed, then defeated — the loser has a `why-not` | placed; a represented dilemma |
| an **`assert`**, asymmetry / anti-transitivity | refused | admitted; a represented dilemma |
| an **`assert`**, disjointness / functionality / a refuted cover | refused, unless the KB arbitrates *and* the derivation is defeasible | refused, unless the KB arbitrates |
| an **`assert`**, irreflexivity / non-mergeable antisymmetry | refused | refused — there is no opposing sentex, so no pair to arbitrate |

Disjointness, functionality and a refuted cover read a **second** class beside the
column, and only under `:arbitrate`: the class of the derivation that makes the members a
nogood — the separating declaration, the functionality mark or the cover, and the `genl`
steps each is read over (`checks/grounds-class`). Both have to be known-true for the
refusal, so a known-true opposing claim separated by a `:default` declaration, or reached
over a `:default` `genl` edge, is arbitrated rather than refused. The shipped upper ontology declares its own
known-true, so a clash between two types it separates directly reads the column alone.

That second read is the one read on the assert path that walks a graph, where the rest of
the entry point does set lookups. `taxonomy/disjointness-class` prices each separated pair
the two closures share with two `reach-strength` calls, and each is a widest-bottleneck
walk over the visible `genl` adjacency that settles a node once — so the read costs the
**ancestry** it convicts over and not the derivations through it. The two are not the same
size: a type with two parents has two routes to each supertype and one eight such levels
up has 256, while the node count grows by two a level. `lein perf`'s
`refusal-grounds-reading` is the gate, and it is the only check that reaches this read at
all — every other arbitrating check holds its memberships `:default`, so the refusal stops
at the column and never asks the second question. 4096× the derivations of one separation
costs under 3×; the same answer read off `taxonomy/disjointness-witnesses`, which yields
one witness per ancestor path, reads 4155× and 482 ms for one decision.

Anti-transitivity opposes **two** claims rather than one, so the column it reads is the
*weakest* of the two chain steps (`checks/opposing-class`): a chain that is known true
throughout refuses the direct step, and a chain with one defeasible step is arbitrated —
where that step, being the unique weakest member, is what the arbitration defeats.

A self tuple `(P a a)` of an `irreflexive` `P`, and a converse no equality could
reconcile under an `anti_symmetric` `P`, are the last row: neither names a second believed
sentex to weigh, so neither is arbitrable and both refuse under every policy. A late
`(irreflexive P)` over a stored self tuple is therefore the `arity` case rather than the
`asymmetric` one — the tuple stands and the mark reports, since a lone-tuple conviction
promoted to a nogood would make belief depend on how many settles had run. A late
`(anti_symmetric P)` over a stored converse pair of two numbers does the same.
`settle/report-unarbitrable-reach!` files the report: one `:irreflexive` or
`:anti-symmetric` entry per marked predicate, reached from the declaration, from a `genl`
edge below the marked predicate, or from a `genlCx` edge into the fact's sight, and read
from the fact's own context as the entry point reads it.

A firing has no caller to refuse, so there the choice is between dropping the
conclusion — no sentex, no justification, and `why-not` reduced to `:not-stored` — and
placing it for `settle` to weigh. Placing it is what gives the loser a reason, so that
is unconditional. Whether a *writer* is told no is a different question, a policy of
the application rather than of the engine, and it is answered per KB by `open-kb`'s
**`:constraints`** — `:refuse` (the default) has `assert` refuse a disjoint, functional or
cover clash at any strength, `:arbitrate` refuses only against known-true content. A KB
naming neither reads the process default `checks/*arbitrate-constraints?*`
(`VAELII_ARBITRATE_CONSTRAINTS=1`), which is what lets a whole suite run under one
policy; `checks/arbitrating?` is the one read of both.

The **retroactive** half is not policy, and neither is the vantage. A declaration
arriving *after* the content it convicts — what an import routinely does — reaches back
under either policy (`settle/declaration-parts`): the weaker side is defeated, or an
equal-strength set is reported by `contradictions`, so belief does not depend on whether
the schema or the facts arrived first, and a recover of the same records, whose region is
every stored sentex, decides the same pairs. A pair only a common descendant context sees
is likewise weighed there under either policy (`settle/clash-askers`), since neither
writer could see the far half and so neither is being told no. What the policy decides is
the *writer's* answer alone: under `:refuse` the entry point still refuses the same fact
asserted one line later, and a refused write never enters the KB. Which sentences count
as a declaration for that purpose is [taxonomy.md](taxonomy.md). A term **joining** a
disjoint metatype is one, and the only one the taxonomy rather than the sentence
identifies (`settle/metatype-member?`).

A settle whose region already holds every stored sentex skips the sweep. The sweep
yields only believed positive sentexes, and such a region holds every one, so the sweep
adds no candidate; run, it would spend its budget and file `:arbitration-truncated` for
the one settle that decided everything. Two settles have such a region. A recover's first
settle follows `rebuild-tms` under `settle/*whole-store-region?*`, which `clash-candidates`
takes when the region is also at least the store's size. A load into an empty KB closes
on the other, since its one deferred settle moves every sentex the store holds; there
`settle/region-holds-store?` counts the region's handles that name a stored record
against the store's sentex count. The handles are counted rather than the believed
region, which leaves out a stored denial or an OUT sentex: the starter stores one denial,
and its closing settle's sweeps, run, reach 66,054 instances against the 8,192 budget
(`starter_test/the-starter-loads-with-no-violation`). Recover's
second settle, whose region is only what re-recording the refusals moved, runs the sweep,
as every settle over part of a store does.

**One retroactive half is not policy at all**, and it is the exception that says what the
policy is about. `(functional P)` arriving after two symbol values for the same first
argument does not convict either of them — it *merges* them, which is an inference rather
than a refusal, so `special/equate-existing` runs it under both policies exactly as
`derive-functional-equalities` runs the same inference on the arriving fact
([equality.md](equality.md)). What `:refuse` and `:arbitrate` decide is whether a writer
is told no, and nobody is being told no here. `anti_symmetric` is the same shape: a
believed converse `(P b a)` beside `(P a b)` forces `(equals a b)` and merges rather than
refuses, `special/derive-antisymmetric-equalities` and `antisym-equate-existing` reaching
it from the fact side and the declaration side under either policy.

Three paths that *mint* content keep refusing either way, because each has somewhere
else to be and nothing to stand behind: the decontextualization lift's copy, the
equality migration's twin, and the gate on what `abduce` may assume
(`checks/constraint-violation`).

### A nogood is a set: `anti_transitive` has three members

`(anti_transitive P)` says a two-step chain forbids the direct step: `(P a b) ∧ (P b c) ⇒
¬(P a c)`. The three cannot all hold and no two of them are the clash, so the conviction
is one nogood with three members:

- **Discovery** asks each member's own question (`checks/antitransitivity-problems`). A
  violation names the other two in `:opposing-handles`, where a pairwise kind names one.
  Every member convicts the set — as the closing step, the first step and the second step
  (`chain-triples`' three roles) — because discovery walks the sentexes a settle moved,
  and a triple only two of whose members convicted would be found or missed by arrival
  order.
- **Decision** is `decide-nogood` over the whole member set: a unique weakest member is
  defeated, a defeasible minimum shared by several is a dilemma, and all-monotonic is a
  conflict. Three equal defaults are one three-sided dilemma.
- **Reporting**: `contradictions` returns one entry whose `:sides` are three, and
  `(contradicts …)` names all three sentences in content order. `:handles` is not a pair.

The mark is read **up** the predicate hierarchy like every other constraint mark, so
`(anti_transitive parentOf)` convicts a chain spelled in `fatherOf`; the steps are probed
at the marked predicate, so a chain written half at each spelling is one chain. A step
reachable **only** by argument preservation is not enumerated, since that reading is
one-sided ([Where conviction is one-sided](#where-conviction-is-one-sided)). A self tuple
`(P a a)`, its own whole chain, is admitted, as an `asymmetric` predicate's is:
`anti_transitive` does not imply `irreflexive`. No predicate is declared both
`anti_transitive` and `transitive` ([taxonomy.md](taxonomy.md)).

### Which contexts can contradict each other

Two beliefs clash when **some context sees both**: their contexts have a non-empty common
down-closure (`tax/maximal-common-descendant-contexts`). Asking whether one context
`sees?` the other catches only a comparable pair and exempts every sibling pair; two
incomparable contexts can share a descendant, and from there `X` and `(not X)` are both
visible. The common-descendant test generalises `sees?` (if K sees Y, K is itself a
common descendant), so it detects everything `sees?` would. `negation-nogoods` memoizes
the test per call, keyed by the context pair.

A **definitional** clash reads the same rule from the other end. A disjointness needs the
separation and the `genl` edges it closes under to be visible too, which is a scoped
check rather than a set test, so the common descendant is where that check is *asked
from* (`settle/clash-askers`).

### A defeat is scoped to its vantage

A nogood is decided at its **vantage**: a context that sees every member, and for a
definitional clash the declaration as well. `negation-nogoods` takes the maximal common
descendants of the two members' contexts, `clash-nogoods` takes the contexts the check
convicted from (`clash-askers`) and keeps the most general of them, and
`preserving-nogoods` does the same over the stored claim's own context and the vantages of
the reading that denies it. The defeated member is
disbelieved at the vantage and in every context below it, and nowhere else. A context's
belief therefore depends on its own ancestor set and on nothing a spec context holds.

```
CxA            (cat Rex)   :default
 └─ CxD        (dog Rex)   :monotonic       (genlCx CxD CxA)
(disjoint dog cat) is visible from both
```

CxD is the only context that sees both memberships, so CxD is the vantage. A read from
CxD finds `(dog Rex)` and not `(cat Rex)`. A read from CxA finds `(cat Rex)`, because CxA
does not see `(dog Rex)`.

**A vantage sees the grounds as well as the members.** A definitional clash is its members
and what separates them — a `disjoint` declaration, the `genl` path up to a separated
type, a `functional` or `asymmetric` mark — so the most general context holding the whole
clash can sit below the members' maximal common descendant:

```
CxA  (t1 Pip) :monotonic     CxB  (t2 Pip) :default     CxDecl  (disjoint t1 t2)
CxW sees CxA and CxB
 ├─ CxX sees CxW
 └─ CxV sees CxW and CxDecl
```

CxW reads no separation and convicts nothing. CxV reads all three and is the vantage:
CxV and every context below it believe `(t1 Pip)` alone, while CxW and CxX believe both
memberships. `settle/clash-vantages` groups the common descendants of the members'
contexts by what each reads of the grounds (`ground-reading`) and asks from the most
general context of each group, which is where that reading first comes into view. Without
this, CxV would believe both memberships of a pair it sees separated, and would believe
one of them in the KB that differs only by CxW also seeing CxDecl. When the members'
maximal common descendants already read every ground the KB holds, nothing below them can
read more, and the common descendants are never enumerated. Otherwise the readers asked are
the common descendants that see a ground context the maxima do not see
(`tax/ground-contexts`, every context asserting a `genl` edge or a flat-cache entry). A
reading is a function of the ground contexts a reader sees, so a reader that sees none
beyond its maximum's reads what its maximum reads. The cost is the contexts below such a
ground, which is CxV above, and not the lattice below CxW; `lein perf`'s
`per-reading-vantages` holds it flat in the contexts below the maximum.

**A vantage sees every member, and some clashes have more than two.** An `anti_transitive`
chain is a triple, and a context seeing two of its steps reads no clash:

```
CxA  (nearP Aa Bb)     CxB  (nearP Bb Cc)     CxC  (nearP Aa Cc)
CxAB sees CxA and CxB, CxBC sees CxB and CxC, CxAC sees CxA and CxC
 └─ CxW sees CxAB, CxBC and CxAC
```

CxW is the vantage, and CxAB, CxBC and CxAC each keep both steps they see.
`settle/chain-contexts` names the pairs of contexts holding a chain's other two steps, a
join of the argument postings on the term two steps share, and `group-vantages` takes the
common descendants of all three contexts where `partner-contexts` gives it one partner
context at a time. An inherited clash has more than two as well: a stored claim denied by
a known-true claim read by argument preservation rests on the general claim, the
declarations and every `genl` edge the reach travels, each possibly in its own context.
`inherit/denial-contexts` names those contexts, read from the whole KB, and
`preserving-nogoods` asks the clash from the most general contexts that see all of them ([inherit.md](inherit.md#a-contrary-claim-against-a-known-true-one-is-a-contradiction-and-is-reported)).

`settle/global-defeat?` separates two cases:

- **The vantage is the defeated member's own context**, or shares a `genlCx` component
  with it. Every reader of the member is at or below the vantage, so the defeat goes into
  the network's defeated set (`jtms/defeat`). A clash inside one context, and a clash
  whose weaker side sits in the more specific context, are both this case.
- **The vantage is strictly below the defeated member's context.** The member stays IN in
  the network, and the pair `[vantage handle]` goes into the KB's `:scoped-defeats`
  roster: a **scoped defeat**. The settle empties the roster at its start and re-decides
  it, as `clear-defeats!` empties the network's set, so a scoped defeat is computed from
  current state and order independence holds for it on the same terms.

**A read applies a scoped defeat through `res/hidden-fn`**, the predicate every
belief-filtered read with a concrete context asks for the visibility `except`
([contexts.md](contexts.md)). The predicate reads a handle as withdrawn from reader K in
three cases: a believed `except` visible from K hides it, it is scoped-defeated at a
vantage K sees, or every justification it has rests on a handle withdrawn for one of
those two reasons. `res/withdrawal` computes the third set as `jtms/grounded-in-region`
with the first two forced OUT, so a consequence follows the reader. A forward rule `(cat
?x) ⇒ (meows ?x)` stated in CxA stores `(meows Rex)` in CxA; a read from CxA finds it and
a read from CxD does not. The raw label `in?` is the network's and does not move, and
`believed?` takes a context and applies the withdrawal.

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
`except` and holds no scoped defeat never asks the predicate at all, and one whose
withdrawable handles support no edge of the relation being read does not either.

**The weighing happens at the vantage too.** `live-vantages` asks which vantages
read every member as believed, and `decide-nogood` compares the classes each of them
reads. `jtms/classes-in-region` recomputes a class over the withdrawn region, so a member
whose monotonic support the vantage withdraws ranks as a default there.

**And on the hierarchy that vantage reads.** A definitional clash is a clash *through* the
taxonomy — `(chi Kit)` and `(cat Kit)` oppose each other because `chi` is under `dog` and
`dog` is separated from `cat` — so the grounds are a second thing the vantage has to read,
beside the members. A settle empties the scoped defeats before it discovers
(`clear-scoped-defeats!`, so a defeat whose nogood no longer stands is not re-applied), and
its discovery therefore reads the relation as the KB holds it globally. The resolution is
where the two are brought back together, in two steps:

- A **scoped defeat is applied before a global one, and alone.** It changes what its
  vantage reads rather than what the network holds, so it can retire a pair the same round
  was about to convict on. A round that takes both convicts against the hierarchy that
  stood before the edge went, which no reader reads afterwards.
- From the **second round on, each definitional nogood is re-asked at each of its
  vantages** (`reads-clash?`), through the entry point the discovery asked. A vantage that
  no longer reads the clash decides nothing. The first round is the one the discovery ran
  for, so a settle that resolves in one round re-asks nothing.

```
CxUniverse   (genl chi thing) (genl dog thing) (genl cat thing)  (disjoint dog cat)
 └─ CxA      (genl chi dog)                 :default
      └─ CxB (not (genl chi dog))           :monotonic   ← the vantage
             (chi Kit)  (cat Kit)
```

CxB disbelieves the edge, so from CxB `chi` is not a `dog` and the two memberships of `Kit`
clash with nothing; no other context holds both. Both are believed at CxB and
`contradictions` reports nothing, in every arrival order that stores the three sentences.
The *entry point* is a separate reading: `(chi Kit)` offered while `(cat Kit)` is
known-true and the denial is not yet written is refused under `:refuse`, on what the KB
says at that moment, and offered again after the denial it is stored. Under `:arbitrate`
it is admitted from the start, since the `(genl chi dog)` edge that makes the pair is
`:default`, and the known-true side wins until the denial arrives. A refusal answers a writer
(`checks/arbitrating?`); belief answers the KB at rest.

**A verdict reaches every context below its vantage, including a context that reads the
clash released.** A *release* is what takes a clash out of one reader's view while the
members stay visible: a denial of a `genl` edge on the separating path, or an `except`
of a member. Move the denial into a `CxC` below CxB, and CxB convicts on a separation it
reads and CxC does not: CxC reads `(chi Kit)` as defeated. The two positions a reader
below the members can hold answer differently:

- **Below a ground the vantage cannot see**, a reader reads a clash the vantage does not,
  and the most general such reader is a vantage of its own
  ([above](#a-defeat-is-scoped-to-its-vantage)). Its verdict adds to what the readers
  below it read.
- **Below a release the vantage cannot see**, a reader reads no clash and still takes the
  vantage's verdict. The release decides what that reader reads of the taxonomy, and
  nothing about the members' belief.

The cost is that a reader's belief depends on where a release sits relative to the
vantage, and not only on the sentences the reader sees:

| where `(not (genl chi dog))` sits | CxC believes `(chi Kit)` | CxC reads `chi` disjoint from `cat` |
|---|---|---|
| CxC, below the vantage CxB | false | false |
| a CxD that CxB sees | true | false |

CxC sees the same sentences in both KBs. An `except` in CxC of the known-true `(cat Kit)`
costs the same way: CxC believes neither membership. `scoped_defeat_test`'s release
tests pin both rows in every arrival order, the retraction of the denial and the
`except`. A verdict that stopped at a release would turn a defeat at the loser's own
context into a scoped one wherever a release sat below it, and re-ask every standing
clash at every release reader on every settle
([why not](defenses.md#a-verdict-is-not-withdrawn-below-its-vantage)).

A `siblingDisjointException` never sits below a vantage that reads its pair as a clash:
the exception is read over the whole KB ([taxonomy.md](taxonomy.md)), so it releases the
pair at every reader, the vantage included, wherever it is written.

#### Vantages that disagree

A nogood can have several vantages, when the contexts that see every member have more than
one maximal element. Each one decides it, and two of them can defeat different members: a
vantage that reads one member's monotonic support as withdrawn ranks that member lower
than a vantage that reads the support whole.

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
Rex)`; CxW2 reads the pair the other way and defeats `(dog Rex)`. Each verdict holds at its
own vantage and below, so a read from CxW1 finds `(dog Rex)` and a read from CxW2 finds
`(cat Rex)`.

CxZ sees both vantages, and one nogood does not convict two members. **A reader that sees
two vantages which defeated different members takes neither verdict**: it reads every
member as believed, and the nogood is a represented dilemma in `contradictions`, the same
answer a single vantage gives a defeasible tie it cannot rank. `settle` records the
disagreeing verdicts in `:vantage-disagreements`, `{vantage handle}` per nogood, and
`res/undecided-pairs` turns that into the `[vantage handle]` pairs a reader reads no
verdict from. A defeat of the same handle at a vantage outside the disagreement still
reaches that reader.

A vantage that cannot rank the pair decides nothing, and an abstention undoes no verdict:
a reader below a vantage that defeated a member and a vantage that tied reads the defeat.
So the reader arity of `contradictions` keeps an entry only for a reader that believes
every member, which is the reading `believed?` gives that reader for each of them, and
only for a reader at or below a vantage that weighed it, since a reader that sees the
members and not what separates them has no clash in view.

A vantage that is a member's own context is always the **unique** maximal vantage — every
context that sees the whole nogood descends from it — so its defeat is the network's and no
second vantage is left to disagree with it. A disagreement is therefore always between
scoped defeats.

`contradictions` reports such a nogood with `:vantages`, the `{vantage handle}` map of
what each vantage decided, and reads it off the roster rather than off the settle that
weighed it, so a later settle whose region does not reach the pair leaves the report
standing. `(contradictions kb context)` reports what stands for one reader: it keeps the
entry for a reader that sees two disagreeing vantages and drops it for a reader that sees
one, whose clash is decided. `belief-status` from CxZ therefore answers `:withdrawn? false` and an
empty `:scoped-vantages` for both members, while from CxW1 it names CxW1 for `(cat Rex)`.

**A scoped defeat blocks no firing.** Derivation blocking reads the `except` roster alone
(`res/except-hidden-fn`). The settle re-decides a scoped defeat on every settle, and a
block on it would sweep a firing and re-derive it on each one. A conclusion resting on a
scoped-defeated handle is stored, and the read above withdraws it from every reader at or
below the vantage.

**A caller holding no reader reads a sentex at its own context.** `res/believed-at?`
answers belief as a context reads it, with the scoped defeats applied and the `except`
roster not applied, and the extent fns' `{:believed? true}` option and `why-not` of a
handle ask it of the sentex's own context. A sentex that is IN in the network and
withdrawn where it is stored gets `why-not`'s `:withdrawn` reason, with the scoped
defeats its context sees under `:withdrawn-by`, and `belief-status` reports the
withdrawal from any context as `:withdrawn?` and `:scoped-vantages`. A backward chainer
drops a rule-derived answer that is scoped-defeated at a vantage its query context sees
(`res/defeated-answer?`), so a rule cannot re-derive for that reader the sentence the
settle disbelieved there.

**The published window holds what a scoped defeat moved.** A scoped defeat moves belief
with no relabel, so the touched window alone would miss the flip. `settle*` reads the
scoped defeats' consequence closure, and which of its handles their own context read as
withdrawn, before it clears the roster (`*scoped-before*`). `settle-finish` adds the
closure before and after the settle to the window it hands `preview`, the consequence
report and the change feed, and its `was-in` reads each handle as its own context read
it. Those three readers judge belief now the same way, so a firing stored below a vantage
reads as removed when the scoped defeat lands and as added when it lifts.

`clash-askers` asks the vantages under both constraint policies, so a definitional
clash a common descendant sees is decided there whichever policy the KB names, and the
defeat reaches that descendant and below.

#### The withdrawal cache

`:withdrawn` holds each reader's withdrawal and the roster the taxonomy's scoped reads
filter by (`res/supporter-filter-roster`), each entry with a watch: the handles its answer
reads. A reader's watch is its region and the `except` handles its ancestor set sees. The
roster's watch is the forward consequence closure of every `except` target and
scoped-defeated handle. At each point the settle moves the network,
`res/reconcile-withdrawn!` drops an entry whose watch meets a handle in the touched window,
a handle one of that handle's justifications rests on, or the conclusion of a
justification resting on that handle. Every other entry is kept. A gained or lost
justification puts its conclusion in the window, so those three reach every region member,
every justification into the region and every boundary label an answer reads.

The watch does not name the rosters, the supersession map, the meta-except count or the
`genlCx` generation. `reconcile-withdrawn!` compares those as a stamp, and a moved stamp
empties the cache (`res/clear-withdrawn!`), as every write of the scoped-defeat roster
does. A settle clears and re-decides the scoped defeats, so a KB holding one empties the
cache on every settle. A kept entry is the answer a fresh recompute gives:
`order_independence_test/the-withdrawal-cache-answers-what-a-fresh-recompute-answers-in-every-order`
compares the two after every op of sampled arrival orders. The taxonomy's
supporter-visibility generation moves only when an entry is dropped or the cache emptied.

A forward chaining run between two settles reads the withdrawn consequences as they stood
at the last settle. `hidden-fn` asks the `except` targets themselves live.

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

Six kinds on this path drop nothing, and report instead. `:arity` is an arity binding
arriving after facts that do not conform to it, and `:non-confluent` two schematic
equations disagreeing about a shared term. Three say a **bounded sweep stopped**, so bounded
work never reads as full coverage. Each files one entry per settle, and
`tax/*exposure-instance-budget*` bounds each sweep ([taxonomy.md](taxonomy.md), "No cut is
silent"):

- `:arbitration-truncated`: content a declaration implicates went *undecided*, so a pair
  that would have been defeated stands believed until a later settle's sweep, which
  resumes past the cut, reaches it ([taxonomy.md](taxonomy.md), "What a declaration
  reaches back over");
- `:arity-truncated`: wrong-length facts went *unreported*, past the budget of the spec
  subtree a binding descends to or the ancestor set a `genlCx` edge opens;
- `:partner-sweep-truncated`: a *vantage* went unasked. Partner discovery reads one
  argument root, except for a `functionalInArg` mark whose determinant is no single root,
  where it sweeps an extent. A context that would have seen a pair is then not consulted,
  and no `:triggers` count can include the pairs lost. The prefix is stable, so only a
  larger budget reaches past it.

The sixth, `:arity-report-truncated`, bounds the **report** and means *found, examined
and not named*. A binding descending a wide subtree convicts more predicates than one
settle may file into a ledger of 1,000, so the pass files at most eight `:arity` entries
and one `:arity-report-truncated` counting what the cap left out.

`:context-edge-exposure-truncated` and `:genl-edge-revival-truncated` come from the merge
sweeps in `special` and in the settle, not from the arbitration sweep, and nothing re-examines
a merge past either cut ([equality.md](equality.md)).

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

The loop terminates because the defeated set grows monotonically and each defeat
turns a member OUT, deactivating its nogood.

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
grounds. The resolution holds this by ordering: within one round a defeat that withdraws
grounds (`tax/derives-from?`: an edge of a cached relation, or a flat-cache entry) is
applied before, and apart from, the verdicts resting on them, and the next round re-asks
the grounds (`reads-clash?`). Taking both at once would convict on a declaration the same
round disbelieves, and `jtms/clear-defeats!` re-believes that declaration at the top of
every settle, so the verdict would be re-taken for as long as both records stood. A scoped
defeat is taken first and alone for the same reason
([A defeat is scoped to its vantage](#a-defeat-is-scoped-to-its-vantage)).

`conflicts` and `contradictions` report the **same entry shape**, down to `:kind` and
every side's justifications (`settle/clash-report`):

```clojure
{:nogood #{h1 h2} :handles [h1 h2] :priority int :kind kw-or-nil
 :sentence (contradicts X Y)
 :sides [{:handle :sentence :context :defeat-class :justifications [...]} ...]
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

**`:sides` and `:handles` name the members in content order, and so does the list of
reports around them**
([why](defenses.md#tie-breaks-and-orderings-key-on-content-not-the-handle)). The sides
are ordered by sentence, then context, compared by `nm/compare-form`. Those two keys are
total, since sentence-plus-context identifies a sentex, so no handle enters the key;
`report_order_test` reads that line of `clash-report` and fails on a handle in it. Each
side's justifications follow `core/supporting-justifications`' content order.

**The ordering is the read's, not the settle's.** `settle` stores the two vectors in
arrival order, and `settle/ranked` orders a reading when it is asked for; `conflicts`,
`contradictions` and the preview's standing filter each call it, and any further reader
of `settle/conflicts-of` or `settle/contradictions-of` owes the same call. The sort key is
built once per report and carried on its metadata through the memo
([why not on the settle path](defenses.md#a-clash-reading-is-sorted-at-the-read-not-on-the-settle-path)).
The two readings
and the report memo sit in **one** atom (`:clash-readings`), written once per settle, so a
reader on another thread cannot take one settle's conflicts beside another's
contradictions. The labeling solver re-sorts the dilemmas by priority then content for
itself (`solve_test/the-result-does-not-depend-on-the-order-the-nogoods-arrive-in`).

A vantage disagreement's report is built at the read from `:vantage-disagreements`
(`settle/disagreement-reports`) rather than published by the settle, so a settle whose
region does not reach the pair leaves it standing. It is cached in `:withdrawn` until the
next point the settle moves belief or either roster.

### The reports are rebuilt only where the region moved

A report is a function of its members — their sentences, contexts, defeat classes and
supporting justifications — plus `:kind` and the vantages. So `record-clashes!` carries a
member set's previous report forward when no member is in the settle's region and its
`:kind` and vantages match; the memo is rebuilt from each settle's answer and holds only
what stands. The readings are republished every settle, so rebuilding every report would
cost an assert time proportional to the standing clashes. `lein perf`'s
`clash-arbitration` is the gate: across a **32x** rise in standing clashes an assert costs
9.5x more with both memos, 12.3x with this one removed, and 46.5x with the carry-forward
removed as well.

The carry is sound only because the region covers every input to a report, and one of
them is not belief: a **redundant justification** moves a conclusion's reason without
moving its label, and `add-just*` notes the consequence as touched on that fast path (as
does `touched-in`), so the report is rebuilt where only the reason changed
([why the window is a superset rather than the flip
set](defenses.md#the-touched-window-is-a-superset-not-the-flip-set)).

Ω(standing) per settle remains: the readings are the whole standing set, so publishing
them costs what they are. The memo keeps the per-pair term to bookkeeping rather than a
re-derivation of the checks.

### Who asks the pair's question

Discovery re-checks the sentexes the settle **moved**, and a check convicts only on
grounds the context it is asked in can see ([contexts.md](contexts.md)). Where each side
of a pair convicts the other, whichever side arrives second finds the pair. A pair whose
halves sit either side of a `genlCx` edge convicts one way only: `(animal X)` in a general
context and `(plant X)` in one that sees it are each admissible where they are written,
and only the seeing side has both in view. Asked from the arriving sentex's own context
alone, the same three sentences would land on a defeat or on two coexisting claims
according to the order they were written in, and with unequal strengths that is a
difference in belief.

So each candidate is asked from its own context and from every **vantage** of a pair it
could form (`settle/clash-askers`). How a vantage is chosen, and why its defeat reaches
only the contexts at and below it, is [A defeat is scoped to its
vantage](#a-defeat-is-scoped-to-its-vantage). The pairs a candidate could form are read
off the argument roots, one posting per term and position: its term's other memberships
for a separation, its term's denials of the parts for a cover, the other fillers of the
slot for a `functional` predicate, the converse of an `asymmetric` claim, and the steps of
an `anti_transitive` chain (`settle/partner-contexts`, `settle/chain-contexts`). The vantages run under both
constraint policies: a pair split across a visibility edge is the clash neither writer
could see, so weighing it tells no writer no. Every arbitrable kind takes this route:
disjointness, `functional`, `asymmetric`, `anti-transitive` and the `covering` /
`partition` cover.

For a candidate the region holds, the own-context question repeats the one the entry
point asked. For a candidate a trigger reached, the mark over its predicate or what its
context sees arrived after the entry point answered, and for a same-context pair beneath a
late mark the own context is the only vantage there is.

**A pair no vantage was asked about yet** is one the arbitration sweep's budget has not
reached. The settle files no ledger entry naming it: `:arbitration-truncated` counts the
sweeps that stopped, a later settle's sweep resumes past the cut, and
`core/exposed-clashes` names every jointly-visible pair on demand. Why there is no
second, reporting sweep: [defenses.md](defenses.md#a-clash-the-settle-has-not-decided-is-counted-not-named).

**Three triggers reach past the region**, since each moves no member of the pairs it puts
in question. A `genlCx` edge moves *visibility*: a pair whose halves are stored and
believed becomes jointly visible with neither half relabelled. The edge reaches over the
ancestor set its sub newly sees (`constraint-facts-in-ancestors`, the tuple-mark
counterpart of `members-in-ancestors`) within `*exposure-instance-budget*`, and `perf`'s
`constraint-exposure-context-edge` holds its cost at the cap. A `genl` edge carries a mark
down to a subtree that held none and reaches the subtree's facts, only while a mark stands
above it, since `genl` is the commonest edge in an ontology. A late `(functional P)`,
`(asymmetric P)` or `(anti_transitive P)` moves nothing but the mark, and reaches the same
subtree facts through the same `marks-above?` gate, since a mark stands above its own
predicate. All three are `clash-candidates`' sweep, run under either policy, and a pair
they reach is *weighed*.

What is order-independent is that the clash is **accounted for**: refused at the entry
point, weighed into `contradictions`, left standing in `conflicts`, or named in
`violations`. Every arrival order need not pick the same account. A late declaration is not
refused, since refusing the sentence that says what the predicate *means* would leave
every later use of `P` unconstrained on the strength of one fact written earlier: the
failure recorded above `checks/arbitrable-kinds` for `arity`. `(disjoint A B)` arriving
over an already-clashing pair is decided the same way (`declaration-parts`, through
`declaration-reach`).

**One sentence stated in two visible contexts is two sentexes**, and a claim that denies
it denies both. The two can carry different strengths and different support, so
`checks/disjoint-problems` and `functional-problems` name one pair per opposing *sentex*
rather than per opposing type, and the asymmetric arm does the same for the converse. The
asymmetric arm therefore reads its converse twice: `inherit/surviving` answers what is
inherited, one claim per tuple, and the sentexes stating the converse are read beside it
and merged on the handle. `asymmetry-problems` keys the candidate's own sentex on its
stored context (`home`) and not on the asker, so `(P a a)` written in a general context
and again in one that sees it stays a pair whichever was written last.

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
refuses the second write only when the general claim and its reading are known-true
([inherit.md](inherit.md#a-contrary-claim-against-a-known-true-one-is-a-contradiction-and-is-reported)).

`clash_oracle_test` makes no `transitiveInArg` declaration, so it covers the visibility
shape and not this one.

### How a settle finds the clashes

`settle/constraint-nogoods` runs once per resolution pass, behind two set-emptiness gates
(`separations?`, `tuple-marks?`); a KB declaring no separation and no tuple mark skips it
and drops the memo. Past the gates, `clash-nogoods` asks `checks/arbitrable-violations`,
the check the assert entry point runs, of each candidate from each of its askers. The
candidates are:

- the settle's region, and what each declaration in it implicates
  (`declaration-parts`, [Which entry point the content came
  through](#which-entry-point-the-content-came-through));
- the memberships a retracted sibling-disjointness exception re-arms
  ([taxonomy.md](taxonomy.md));
- both members of every pair already known to clash, the `:clashes` memo;
- the handles `clash-dirty` names, which a spelling's belief or reading moved through with
  no relabel (below).

A `:clashes` pair stays while both records are stored, defeated or not, so a revival is
reported again. A pair leaves only when it is re-derived with both members believed and
no clash between them, while no scoped defeat stands. A pair re-derived clean while one
stands goes into the memo's `:held` set and is asked again by the next pass, because a
clean reading can rest on a scoped defeat of a ground, and the next settle clears the
roster and re-decides it. Without the hold, retracting a denial of `(genl chi dog)`
written after the pair's verdict leaves the pair unasked, and both memberships stay
believed (`scoped_defeat_test/retracting-a-release-below-the-vantage-returns-every-reader`).
`contradictions` is recomputed every settle and a region holds only
what that settle moved, so without the memo a standing dilemma whose members sat still
would be reported once and then drop out on the next unrelated assert.

`could-clash?` drops every candidate that cannot pair before a check runs: a membership
whose term's argument-1 root holds one sentex, and a fact under no tuple mark. The sweeps
over declarations share one `*exposure-instance-budget*`, and the budget is debited by the
enumeration and not by the survivors, so a trigger whose filter rejects every term still
stops at the budget.

**A known pair is carried forward** unless this settle could have changed its answer:
one of its members moved, the vocabulary moved, or the `genl` relation moved in a way the
pair reads. A member moved when the region holds it or `clash-dirty` does. Two changes
reach a pair with no relabel, and `clash-dirty` names the handles of both:

- **a supersession flip.** `settle-finish` posts the flipped handles to the memo's
  `:dirty` (`note-supersession-flips!`, the negation memo's input). `settle-finish`
  gives an un-merge's spellings back after the passes, so the settle's next round reads
  them from `:dirty`.
- **a move of the equality partition.** The checks read through `res/without-retired`, so
  a merge or un-merge changes which spellings a reader retires. A merge retires a spelling
  without superseding it when no restatement is stored, so a pair can form or dissolve
  with neither member relabelled or superseded. The partition records the classes of both
  ends of each edge a supporter joins, leaves, or moves in or out of belief on
  (`tax/take-equality-moves!`), and `clash-dirty` adds every stored sentex naming one of
  those terms. A settle whose partition did not move reads one empty key.

`clash_oracle_test/a-merge-and-its-retraction-move-the-pairs-the-spellings-form` holds
both directions.

`clash-vocabulary` is the vocabulary as one value, compared whole:

- the `functionalInArg` **table**, keyed by position. Retracting `(functionalInArg P 1)`
  while `(functionalInArg P 2)` stands leaves `P` in the predicate roster, and a pair
  convicted only through position 1 would carry forward stale;
- each disjoint metatype's **members**. `(disjoint_metatype M)` stays while `(M b_t)`
  leaves, and the pair `(a_t X)` / `(b_t X)` stops being separated with no declaration
  written and neither member in the region;
- the sibling-disjointness exceptions, so an exception arriving or leaving re-derives every
  known pair;
- the `genlCx` generation, since which contexts can convict a pair is a question about
  the whole context relation.

The `genl` relation is weighed per pair instead. A pair of unary memberships is decided by
`tax/disjoint?` of its two types, which reads each type's supertype closure and, in the
metatype, sibling and partition arms, the `genl` edges between two of those supertypes.
A type standing under two types one of those arms separates loses the separation when an
edge relates the two, and neither member's closure moves. So `settle/genl-view` stamps each member's
type with every supertype mapped to that supertype's direct parents — the `genl` edges out
of the closure, which are every edge `disjoint?` can read for it — and a pair whose two
stamps stand is carried. Edges rather than each supertype's own closure: the same
information for this question, without a closure per supertype per pair on a deep
hierarchy. The stamp is global, because the readers are the askers and not the members. A
member's context `ctx` is seen by every asker that convicts through it, so
`parents(s, ctx) ⊆ parents(s, k) ⊆ parents(s)` for each supertype `s` and asker `k`.
Where the two ends are equal for every supertype, every asker reads the same edges; where
one differs the pair re-derives. Any other shape re-derives whenever an edge moves.

**One entry per handle set**, and a function of the set's content: the members' sentences
are ordered by `nm/compare-form`, and where two members convict on different `:kind`s the
entry is chosen by `:kind` then `:sentence`. A region holding both sides of a pair finds it
twice, and which sides a region holds depends on arrival order, so an entry keyed on the
walk would report one clash or two by that order; `constraint_nogood_test`'s permutation
cases pin the content keying. The entry's `:vantages` are the most general of the askers
that convicted.

Bound to `false`, `settle/*incremental-clashes*` makes every believed sentex a candidate
on every settle and carries nothing. That is the definition the region, the gate and the
carry approximate, at O(believed) checks per settle, and `clash_oracle_test` compares the
default against it.

## What a settle is built from

A settle composes 21 features. Each one requires some others to exist, and removing a
feature removes every feature that requires it. This section lists the features, what each
requires, the reserved words that reach each one, and what a removal takes with it. The
cost of each step is the next section.

### The dependency layers

`─►` means *requires*: the target's removal removes the source. `⇢` means *supplies*: the
target's removal leaves the source with no input and nothing broken. The relation has no
cycle, because a cycle in it would be two features neither of which can be built first.

```
layer 5   scoped defeat ─► defeat                 :groundable ⇢ defeat   (equal to :in without it)
layer 4   defeat ─► decide-nogood                 edge solver ⇢ decide-nogood
layer 3   decide-nogood ─► strength classes, deciding vantage
          decide-nogood ⇢ nogood discovery
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
| strength classes | `jtms/region-classes` | `:monotonic` `:default` (assertion options) | removes decide-nogood, defeat and scoped defeat |
| recheck queue | `settle/drain-recheck!` | none | removes `exceptWhen` and NAF, its only fillers |
| equality partition | `vaelii.impl.special` | `rewriteOf` `sameAs` `equals` `different` | removes supersession |
| touched window | `jtms/touched` | none | removes nothing; `preview`, the change feed and the cache reconcile diff the believed set instead, at O(KB) per write |
| forward chaining | `vaelii.impl.chain` | `implies` `set/forwardRule` `set/defaultRule` `set/backwardRule` `set/assumptionRule` `set/inertRule` | removes generators; backward proof still answers |
| generators | `vaelii.impl.chain` | `implies` `set/forwardRule` with a rule consequent | removes nothing |
| nogood discovery | `settle/constraint-nogoods`, `negation-nogoods`, `preserving-nogoods` | `not` `disjoint` `disjoint_metatype` `sibling_disjoint` `siblingDisjointException` `functional` `functionalInArg` `asymmetric` `anti_transitive` `covering` `partition` `transitiveInArg` `transitiveInArgInverse` | leaves decide-nogood with no nogood to decide |
| `exceptWhen` · NAF | `settle/exception-blocked-set` | `exceptWhen` `unknown` | removes nothing; `:blocked` stays empty |
| supersession | `special/refresh-supersessions` | `rewriteOf` `sameAs` | removes nothing; `:superseded` stays empty |
| visibility except | `res/withdrawal` | `except` `sentexHandle` | removes nothing |
| deciding vantage | a nogood's `:vantages`, filtered by `settle/live-vantages` | `genlCx` `ist` | removes decide-nogood, defeat and scoped defeat |
| decide-nogood | `settle/decide-nogood` | `contradicts` (reported, never stored) `bravely` `cautiously` | removes defeat and scoped defeat |
| defeat | `jtms/defeat`, called once, in `settle/resolve-contradictions` | none | removes scoped defeat; `:groundable` equals `:in` |
| edge solver | `vaelii.impl.solve` | `set/hardConstraint` `set/softConstraint` | changes nothing for a KB on the built-in `decide-nogood` |
| scoped defeat | `reasoning/scoped-defeats` | `genlCx` (the vantage) | removes nothing; every defeat is network-wide |
| `:groundable` | `jtms/relabel-region*`, second `region-fixpoint` call | none | depends on defeat; see below |

Strength classes, the deciding vantage, decide-nogood and defeat are the **arbitration
bundle**, and the bundle is the one region of the table where one removal takes several
features with it. Strength classes do not leave with arbitration: `core/defeat-class` is
public, and `vaelii.impl.inherit`, `vaelii.impl.chain` and `vaelii.impl.checks` read it for
supporter and declaration strength.

### Two dependencies no removal can separate

- **Defeat requires strength classes.** `decide-nogood` defeats the unique weakest member of
  a nogood. With no defeat-class the engine has no content-keyed minimum, so a loser would be
  chosen on arrival order, which breaks order independence.
- **Defeat requires `:groundable`.** The sweep deletes a datum that is OUT and ungroundable,
  and keeps one that is OUT and groundable for revival
  ([the states a node can hold](#the-set-membership-states-a-node-can-hold)). Without
  `:groundable`, a defeated datum and a datum that lost its last derivation read alike, so
  the sweep either deletes what `clear-defeats!` would revive or keeps what nothing derives.

### Without defeat, `:groundable` equals `:in`

`relabel-region*` calls `region-fixpoint` twice over the same region and the same
justification edges. The `:in` call forces the `:defeated` set OUT, and the `:groundable`
call forces nothing OUT. `:blocked` enters both calls through `valid?`, so a block moves both
sets alike. When `:defeated` is empty, the two calls take equal arguments whenever their
boundary sets are equal. Both sets start empty and every mutation of the network relabels, so
the two sets stay equal. A network with no defeat therefore holds a second copy of `:in` and
runs `region-fixpoint` twice per relabel for it.

### The cycles a settle runs

The layers above have no cycle. The algorithm iterates in five places, each stated where
its mechanism is documented:

| cycle | what closes it | why it terminates |
|---|---|---|
| the exception loop | a blocked set moves belief, and belief moves what an exception query answers | a cycle through negation is refused at assert time; 16 passes bound it ([exceptions.md](exceptions.md#blocking-and-the-tms)) |
| the defeat rounds | a defeat moves a region, and a moved region can expose a nogood | a defeat only removes belief, so a round retires pairs and never forms one ([the resolution rounds](#the-resolution-rounds)) |
| a support cycle | `A` justified by `B` and `B` by `A` | `region-fixpoint` starts from nothing IN inside the region and only adds ([Locality](#2-locality)) |
| the class equation | a node's defeat-class reads its antecedents' classes | `region-classes` starts every member at `:default` and applies a monotone operator ([Strength propagates](#strength-propagates-from-the-antecedents)) |
| a `genl` or `genlCx` loop | an edge that would close a cycle in the closure | refused, or dropped and recorded when derived ([exceptions.md](exceptions.md#stratification)) |

### No switch removes a feature

Every feature above runs on every KB. Each optional feature sits behind an emptiness check
instead: a KB storing no `exceptWhen`, no merge, no clash declaration or no `except` pays a
set read for that feature per settle. The one belief policy on the KB handle is
`:constraints` (`checks/arbitrating?`), which decides whether a definitional clash against
defeasible content is refused at the entry point or arbitrated, and the reasoning image
stamps it because a store recovered under the other policy believes different content
([storage.md](storage.md#the-reasoning-image)).

## The runtime of a settle

Invariant 2 states that a relabel costs its region. A settle does more than relabel, and
each of its other steps is bounded by a different quantity: the standing contradiction
set, the rules a trigger reaches, a sweep budget, or the whole store. This section lists
the steps in the order `settle*` runs them, gives the quantity that bounds each one, and
names the gate that holds the bound. The last part lists the steps where the bound is not
the region.

### The runtime view

`n` is the store, `r` the relabelled region (`jtms/touched`), `k` the standing defeats and
dilemmas, `q` the rules the recheck queue holds, `B` the sweep budget
`tax/*exposure-instance-budget*` (8192).

```
write entry point (assert / retract)                          bound
 ├─ canonicalize · checks · index · record · JTMS node        O(1) per fact
 ├─ chain: join each rule keyed on the fact's predicate       O(rules on the predicate × join)
 └─ add-justification → relabel the affected region           O(edges in r)

settle*
 ├─ 1  clear-defeats! · clear-scoped-defeats!                 O(k) + a relabel of each loser's region
 ├─ 2  revival reconcile (only when step 1 lifted a defeat)   O(r)
 └─ passes, until nothing is queued, at most 16
     ├─ 3  constraint-nogoods                                 O(1) gate; else O(r), sweeps capped at B
     ├─ 4  resolve-contradictions: rounds until one defeats nothing
     │     ├─ negation-nogoods                                O(opposed bodies in r + recorded pairs)
     │     ├─ preserving-nogoods                              O(1) gate; else O(standing + r), asks O(r)
     │     ├─ decide-nogood                                   O(members) class reads per nogood
     │     └─ defeat → relabel                                O(edges in the loser's region)
     ├─ 5  drain-recheck!                                     O(q)
     ├─ 6  revived-seeds                                      O(r)
     ├─ 7  exception-blocked-set                              one level-6 query per trigger-reachable firing
     └─ 8  set-blocked · sweep · re-chain released firings    O(released firings);
                                                              a blanket re-join is O(fact extent) per rule

settle-finish
 ├─ restore-depths (only after a deferred batch)              O(V + E) of the taxonomy, once
 ├─ refresh-beliefs (only when belief moved)                  O(caches a supporter in r feeds)
 ├─ refresh-supersessions                                     O(r + classes moved), every settle
 └─ arity and unarbitrable reach · record-clashes!            capped at B instances per trigger

recover                                                       O(n): one settle, r = every sentex
```

Inside step 1 and every relabel, the three least fixpoints are `region-fixpoint` for `:in`,
`region-fixpoint` again for `:groundable`, and `region-classes` for the defeat-classes. Each
is a worklist over the region's edges, so each is O(edges in r)
([Locality](#2-locality) has the measurement).

A settle materializes the region `passes + 1` times, which `settle_region_cost_test` pins
as a count. On the dense network each read copies the touched bitmap into a set, so that
count is a multiplier on O(r), and on a `recover` it is a multiplier on O(n).

### The resolution rounds

Step 4 is `resolve-contradictions`, which runs rounds until one defeats nothing. Each round
reads three sources and keeps the nogoods whose members are still believed
(`live-vantages`):

- the definitional nogoods step 3 found for the pass. A defeat only removes belief, so a
  round can retire one of these and never forms one. From the second round on, each is
  re-asked at each vantage (`reads-clash?`) and keeps the vantages that still read it
  ([A defeat is scoped to its vantage](#a-defeat-is-scoped-to-its-vantage)).
- `negation-nogoods`, asked every round, since a defeat can change which other pairs are
  believed. It answers from its per-body memo, so a round that moved nothing re-derives
  nothing.
- `preserving-nogoods`, asked every round, since a defeat of a declaration or a relation
  edge withdraws the inherited claim resting on it, and the pair has to stop being a
  nogood in the next round rather than at the next settle.

Each nogood is weighed at each vantage in `live-vantages`. A round then applies one kind of
decision and re-enters:

1. the scoped defeats the vantage roster does not hold yet, alone
   ([A defeat is scoped to its vantage](#a-defeat-is-scoped-to-its-vantage));
2. else the global defeats of a handle the taxonomy derives an answer from
   (`tax/derives-from?`), which withdraw grounds
   ([A clash is reported, never stored](#a-clash-is-reported-never-stored)).
   `derives-from?` names more handles than withdraw grounds, and each extra one costs a
   round and changes no answer;
3. else the other global defeats.

The rounds terminate. A scoped round needs a defeat the roster does not hold, and the
roster is bounded by the handles; a global round defeats a believed member, and nothing in
the resolution revives one. The hard clashes and the dilemmas are collected at the round
that defeats nothing, so a clash that stands beside other rounds' work is counted once.
After the rounds, the pass finds the `except`s they flipped by reading the region or the
`except` root, whichever is smaller (`settle/resolution-watch`).

### What `settle-finish` reconciles

`settle-finish` runs once, after the last pass, in this order:

1. `restore-depths`, the depth repair a `with-deferred-settle` batch owes.
2. `refresh-beliefs` over the region, only when belief moved: a defeat, a revival, a scoped
   defeat, a pass that moved the blocked set, or a relabel before the settle
   (`belief-moved?`). Those are the only label flips a settle sees. The last is
   `preview`'s: `suspend-premise` and the rollback's `add-premise` flip labels with no
   defeat, block or write, so `preview` binds `settle/*relabelled-before?*`, and the
   settle also reconciles at its start, as after a revival, before the passes read the
   closures. A declaration that arrives or leaves reaches the caches
   through `special`'s integrate hook on the write path, so a settle that flipped no label
   leaves the caches consistent. `restore-depths` runs again after the reconcile, since
   the reconcile can open or close a cycle
   ([taxonomy.md](taxonomy.md#what-a-batch-does-to-the-depth-potential)).
3. `refresh-supersessions`, on every settle. A retraction can un-merge without moving a
   label, so `belief-moved?` does not cover it. Its cost is the region plus the stored
   sentexes naming a term of a class the equality partition moved
   ([equality.md](equality.md#what-a-merge-does)).
4. `refresh-beliefs` again whenever a supersession entry changed since the last settle,
   over the region plus those data (`special/take-supersession-moves!`). A merge
   supersedes a `genl` or `disjoint` declaration with no label moving, and step 2 read
   `in?` before step 3 recomputed supersession. The spellings an un-merge gave back go to `settle`'s re-seed
   ([the other half](#the-other-half-a-spelling-an-un-merge-gives-back)).
5. The reports, which read the caches steps 2–4 reconciled: the arbitration and
   partner cut notices, the arity reach, the unarbitrable reach, and
   `record-clashes!`. Each is off on a rebuild.
6. The window: the region, the supersession flips, and the scoped defeats' closure before
   and after the settle (`scoped-moves`), handed to `*touched-sink*`, `*touched-in-sink*`
   and the change feed. The sets are built only when a sink is bound or a listener is
   registered, and the feed is skipped on a rebuild, whose region is the whole KB.
7. `res/reconcile-withdrawn!`, the last read of the window before it is cleared
   ([the withdrawal cache](#the-withdrawal-cache)).
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
| `:chaining` — the generative join | **48–51%** | 0% | 4% |
| `:outside` — canonicalization, checks, index, minting | 42–44% | 6–11% | 10% |
| `:belief` — relabel and `add-justification` | 0.5% | **87% memory, 90% disk** | 4% |
| `:discovery` — the three nogood scans | ~1% | ~0% | **75%** |
| `:resolution` — decide and solve | 0.5% | ~0% | 5% |
| `:finish` + `:glue` | 6–8% | 3–4% | 2% |
| relabelled region, p50 | 2 | 104,157 | 52 |

A centre is charged its **self-time**, the interval while its span is on top of the stack,
so nested centres are not counted twice and the seven buckets sum to the run. `:belief`
holds the relabels `clear-defeats!` and `resolve-contradictions` drive, the revival
reconcile and `recovery/rebuild-tms`' replay; `:resolution` holds `decide-nogood` and the
edge solver, less the discovery and relabel they drive; `:finish` is `settle-finish`;
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
- **A contradiction-dense load spends its time discovering.** The load seeded 50 standing
  contradictions (`defeats=50`), and the median region rose from 2 to 52. Step 1 lifts
  every standing defeat at the top of every settle, so each of the 50 is re-discovered
  and re-decided on every later assert, at about 1 ms per settle on that run.

The exception loop is measured separately in
[exceptions.md](exceptions.md#the-fixpoint-question-measured): the blocked set moved in
**0** passes on every settle of the starter and stories load, and in at most **1** in every
`except_test` scenario. On `except_recheck_test`'s workload, where a
second rule makes the exception hold on every firing, step 7 costs **1.0** level-6
evaluation per assert and the whole settle **2.0**, flat from n=25 to n=200.
`except_recheck_test` pins the growth of that count, not its value.

### Where the scaling arguments hold

`lein perf` asserts each scaling claim as a growth ratio between two sizes, never as a
duration (`bench/vaelii/bench/perf.clj` states the method). Its checks sort into five
groups by the quantity the claim bounds a step by.

**Flat in the store.** The step costs its region, and the ratio bound is 2.0× across an
8× to 128× size step unless the row says otherwise. These checks hold invariant 2 end to end:

| step | `lein perf` check | sizes |
|---|---|---|
| a fact derived through a defeasible rule | `defeasible-load` | 250 → 2000 |
| a negative fact with no positive twin | `negation-load` | 250 → 2000 |
| a `genl` edge deep in a chain | `taxonomy-depth` | 250 → 2000 |
| defeat and revive one `genl` edge (steps 1, 4, `refresh-beliefs`) | `taxonomy-belief-flip` | 500 → 4000 |
| defeat and revive one `disjoint` declaration | `flat-cache-belief-flip` | 500 → 4000 |
| a region delivered to a feed listener | `feed-listener-scaling` | 250 → 2000 |
| the `exceptWhen` roster gate (step 7) | `exception-roster-gate` | 64 → 2048 |
| a `genl` edge against a negated exception it cannot reach | `genl-edge-negation-recheck` | 32 → 1024 |
| step 3 on a KB whose marks the fact does not reach | `unrelated-fact-under-marked-kb-fanout`, `constraint-exposure-shared-arg`, `constraint-genl-edge-gate` (2.5×) | 250 → 2000 |
| a `genlCx` edge widening a few readers | `genlcx-edge-reader-fan` (3.0×) | 8 → 512 |
| an un-merge of one class, beside standing merges it does not touch | `unmerge-over-standing-merges` (3.0×) | 32 → 1024 |
| a merging assert inside a deferred batch, per merge the batch already holds | `deferred-merge-batch` (3.0×) | 128 → 1024 |
| an assert beside believed `except`s it does not reach ([the withdrawal cache](#the-withdrawal-cache)) | `assert-over-standing-excepts` (3.0×) | 32 → 4096 |
| a scoped read | `visibility-reading` | 8 → 1024 |
| a clash vantage below a maximum that reads less of the grounds, in the contexts below that maximum | `per-reading-vantages` | 250 → 2000 |
| the join naming an `anti_transitive` chain's contexts, in the open chains beside it | `chain-join` | 250 → 2000 |

**Flat past the budget.** A budgeted sweep implicates every instance below a type or
inside an ancestor set, which is the extent rather than the region. The sweep stops at `B`
instances and files a notice naming its trigger, so the cost is flat once the extent is
larger than `B` and linear in the extent below it:
`constraint-exposure-context-edge`, `functional-in-arg-empty-determinant-sweep`,
`arity-reach-budget-cap` and `constraint-genl-mark-descent`, each 2.0× past the cap.

**Linear in the standing set.** Steps 1 and 4 re-decide every standing contradiction on
every settle. Belief is computed
from current state and never carried over, which is invariant 1, and the cost of that is an
O(k) term on every write. The checks bound the per-member cost, so a regression to a full
re-derivation of the set on every settle fails them:

| claim | `lein perf` check | growth | bound |
|---|---|---|---|
| standing definitional clashes, per assert | `clash-arbitration` | 32× | under 15× |
| standing `P`/`¬P` dilemmas, per assert | `negation-arbitration` | 8× | under 11× |
| standing inherited dilemmas, per assert | `inherited-clash-arbitration` | 32× | under 10× |
| standing scoped inherited defeats, per unrelated assert | `inherited-clash-arbitration-split` | 512× | under 90× |
| standing merges, per unrelated retract | `retract-merge-scaling` | 32× | under 18× |
| standing merges, per `except` of one merge asserted and retracted | `except-merge-scaling` | 128× | under 28× |
| standing clashes, per `genl` edge separating nothing | `taxonomy-edge-arbitration` | 100× | under 35× |
| standing dilemmas, per `genlCx` edge reaching nothing | `context-edge-arbitration` | 100× | under 32× |
| `contradictions`, which orders the standing set it returns | `standing-clash-reading` | 32× | under 175× |

**Linear in a structure the write walks.** The step walks something the fact names, and the
claim is that it walks it once:
`membership-under-depth` (32× the hierarchy, under 12×),
`disjoint-metatype-membership` (8× the metatype's members, under 12×),
`arity-reach-under-subtree` (32× the subtree, under 45×),
`arity-reach-batch-roots` (8× the deferred edges in one settle, under 25×) and
`refusal-grounds-reading` (4096× the derivations of one separation over three times the
ancestry, under 3×).

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

A settle hands no nogood to a solver: `decide-nogood` answers a defeat, a dilemma or a
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
  argument constraint, an arity, a malformed special predicate, an unstratified derived
  edge ([Definitional constraints on the derivation
  path](#definitional-constraints-on-the-derivation-path)).
- A mark whose conviction names no second sentex reports the stored facts it reaches and
  decides nothing: a late `arity`, `irreflexive` or `anti_symmetric` leaves them believed
  ([Which entry point the content came through](#which-entry-point-the-content-came-through)).
  A mark that revives is in the moved region and reports as an arriving one does. A
  convicted fact that revives under a standing mark is not reported, because the pass
  reads the marks' reach and not the region's plain facts.
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
  | a scoped defeat of an edge | the vantage and below | the firing again, at each reader that still reaches, with every witness search asked from that reader (`settle/lost-firing-seeds`, `chain/*witness-view*`) |
  | an `except` of an edge | the excepting context and below | the same, per reader |

  The argument-type entailment and the equality a descended `functional` or
  `anti_symmetric` mark derives name a `genl` route the same way (`checks/edge-support`),
  and the first two rows re-derive them too: a retraction draws each derivation the sweep
  deleted again after the teardown, and a network defeat draws each one the edge took OUT
  (`special/rederive-descended`, [argtypes.md](argtypes.md)).

  A scoped defeat and an `except` leave the edge IN in the network, so no relabel starts:
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
               (largerThan dog cat)  (transitiveInArg largerThan 1 genl)
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
  CxUniverse   (largerThan dog cat)  (transitiveInArg largerThan 1 genl)
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
  CxUniverse   (aRel high val)  (transitiveInArg aRel 1 genl)
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
  and the handle count do. And the scan runs on every settle pass while a scoped defeat or
  an `except` stands, one withdrawal per reader below it and one check per firing withdrawn
  there — linear in those firings (`lein perf`'s `lost-firing-scan`), and nothing when the
  KB holds neither. The covering test that decides which routes place a firing leaves a
  surplus of the same kind, a firing placed below another it is read beside, in a lattice
  that splits one route across sibling contexts
  ([defenses.md](defenses.md#routes-in-sibling-contexts-each-carry-a-firing) gives the
  shape and its count).

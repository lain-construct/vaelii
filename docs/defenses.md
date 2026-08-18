# Design defenses

- **Covers:** why a belief-and-contradiction decision is shaped the way it is, and why
  the alternative a reader would reach for is worse. The argument a how-to doc points at
  rather than restates.
- **Not here:** how any of it works — each entry names the subsystem doc that describes
  the mechanism, and assumes you have read it. The vocabulary → [glossary.md](glossary.md).
- **Assumes:** the mechanism you came for the rationale of. This doc argues about a
  design; it does not teach it.

A subsystem doc says **how** the engine works. A few of its decisions are non-obvious, or
have a tempting alternative that fails for a reason worth writing down once — and left in
the how-to doc that argument grows until the mechanism is hard to find under it, and the
same argument gets re-derived in three sections because it bears on all of them. So the
argument lives here, under a stable heading, and the how-to doc states the rule and links
to it. Where one argument bears on several places, those places link to **one** entry
rather than each carrying a copy.

Each entry names the doc it defends, and the sections below follow the grouping the
[doc map](README.md) uses.

## Belief and truth maintenance

Defends [nmtms.md](nmtms.md).

### Two strength classes, not three

There are exactly two assumption strengths, `:monotonic` and `:default`, and derivation
adds none. A third is tempting: something between them would let `penguin ⇒ ¬flies`
outrank the default `bird ⇒ flies` without the penguin fact having to be known-true.

Do not add it. That one problem is [`exceptWhen`](exceptions.md)'s, and it needs no rank:
a rule states its own exception and does not fire, so nothing has to out-rank anything. A
class between the two buys that single case and costs the total order **monotonic >
default** everywhere else — and the total order is what lets `decide-nogood` resolve a
clash by defeating the strictly-weaker member with no solver. An intermediate class turns
every unequal pair into a question of which of three ranks each side holds, for a case
already handled structurally.

### A bare re-assert never downgrades the class

A re-assert takes the stronger of the two classes (`strength/max`), never the weaker. The
mark is resolved from *content*, the way a re-asserted rule's slots are
([canonicalization.md](canonicalization.md)).

The alternative — last-writer-wins, the mark taking whatever the latest assertion carried
— reads a re-assert's silence as a claim. A re-assert carrying no `:strength` states
nothing about the class; the `:default` it falls back to is the door's fallback, not the
caller's claim. Treat that silence as a downgrade and arrival order decides belief: assert
`S` known-true, re-assert it bare, then assert the known-true `¬S`, and a last-writer-wins
mark leaves `S` **defeated**, while the same three sentences in the other order leave the
pair an irreducible clash. `strength/max` is commutative and idempotent, so every order
agrees and a third assertion changes nothing. Narrowing a class is deliberately not a
re-assert but `retract!` and re-assert — the retraction takes the mark with it, so nothing
is inherited across one.

### A firing is capped by its weakest ground

A justification confers `min(its own strength, the weakest of its antecedents' classes)`,
and the taxonomy edges a firing names — a `genl` edge a subsumed match climbed, a `genlCx`
edge the conclusion's context reads the rule or facts over — are grounds like the facts and
cap it the same way.

Without the cap, a bare rule over a merely-default premise would conclude `:monotonic`,
and a rule would **launder** a default into something a directly-asserted default cannot
contradict: a conclusion carrying more authority than any of its grounds. Read across a
merely-default context edge, known-true facts under a bare rule conclude `:default` for the
same reason — the sighting is as defeasible as the edge that carries it, and a conclusion
stronger than the wiring it was read over is the same laundering.

The **informant is excluded** from the cap, though a rule is one of its own justification's
antecedents. That membership is what makes retracting or defeating the rule withdraw
everything it licensed — a *validity* role, not a ground. A rule takes `:default` unless
its own assertion says otherwise, exactly as a fact does, so capping on it too would drop
every datum an ordinary rule licensed to `:default`. This is why a rule's own class
(`:strength`, what `defeat-class` answers for its handle) and its defeasibility (`:strength
:default` on a firing versus a bare rule, what its firings confer) are two slots: only the
second moves belief, and nothing in the engine defeats a rule, so the first takes part in
no contest.

### The subsumption path is the widest bottleneck, not the shortest route

A `genl` edge can itself be defeasible, so when a fact reaches a rule antecedent of a
different functor across the closure, the edges the match climbed become antecedents of
the firing and the cap above floors the conclusion at their weakest class. Which *route*
through the taxonomy the walk names therefore decides how strongly the conclusion holds,
and the obvious walk names the **shortest** one — the fewest supports the reachability can
be made to depend on.

Do not keep the shortest route here. Fewest supports is a reasonable thing to optimize and
it is not the same thing as strongest: on a hierarchy offering a one-hop `:default` edge
beside a two-hop all-`:monotonic` chain, the short route floors the conclusion at
`:default` while a `:monotonic` derivation of the identical conclusion exists and the
engine merely declined to find it. "Fewest edges" never asked how strongly each edge
holds, so the class a conclusion is reported at would be an accident of how many hops its
cheapest witness happened to take — arrival order wearing another hat, since the cheapest
witness is the one that happened to be asserted.

The walk takes the **widest bottleneck** instead: the route whose floor — the `min` defeat
class along it — is highest, tie-broken by depth then by the name order every closure read
uses, so the choice is a function of the hierarchy and never of a handle. It adds no third
class and invents no second lattice — a path's rank is the `min` over its edges' classes,
the same fold `strength` folds over a justification's antecedents, so the two compose
rather than competing. `kb/reach-strength` reads that floor off the same chosen path, so
the reported class and the witness that justifies it never disagree ([taxonomy.md](taxonomy.md),
*Strength of a subsumption path*).

Only the `genl` subsumption a firing rests on asks for the widest route, because only there
does a supporter's *class* change an answer the engine gives. The `genlCx` visibility a
placement is recorded over still takes the shortest path — most general supporter per edge
— because placement asks whether an edge is *seen*, not how strongly it holds; routing it
to the widest bottleneck would make where a firing is filed depend on a defeat class that
can move under it.

### The class fixpoint is a least fixpoint, not a single pass

`jtms/region-classes` solves the recursive class equation — a node's class depends on its
antecedents' — as a least fixpoint inside the region relabel, every in-region IN node
starting at `:default` and a semi-naive worklist iterating to stability.

A single pass would be wrong in a way that looks fine. Visited one way it reads a
not-yet-computed antecedent as bottom and under-rates the conclusion; visited the other it
reads a stale value and over-rates it — so the answer would depend on visit order, which is
arrival order wearing a different hat. The operator is monotone and the iteration starts at
bottom, so the least fixpoint is unique and therefore independent of the worklist's visit
order and of the order the knowledge arrived in. Uniqueness is also why locality costs no
order independence: a least fixpoint over the region with boundary labels fixed has the
same unique solution a global fixpoint would produce, so there is nothing for a visit order
to influence.

### Locality is a claim about every representation

The locality guarantee — no operation recomputes the whole graph — is a claim about every
representation of the network, and a perf table over the reference network tests only one.

The reference network's persistent maps are region-local by construction. The dense network
([density.md](density.md), Phase 3) holds belief in `RoaringBitmap`s, where any operation
that rebuilds a bitmap costs one pass over all of its 65,536-value containers — so it
satisfies locality up to 65,536 nodes, where there is exactly one container, and silently
violates it above. At the largest graph a reference-network table measures, nothing could
show it; it takes a rebuild over nine million premises. So whatever else a second
representation is proven to match, **cost shape is part of it** — an oracle test that
compares only answers passes a representation whose answers were never wrong and whose cost
grew with the KB.

### Two TMS implementations, not one

The network sits behind a `Tms` protocol with a `:reference` and a `:dense` implementation
rather than one adaptable structure, and two properties are why — both easy to assume and
both wrong.

A dense network cannot simply replace the reference. `RoaringBitmap` is mutable, and
`jtms_atomicity_test` pins that a mutation applies all-or-nothing; a mutable bitmap inside
a persistent value would break `swap!`'s retry and let a reader observe a half-applied
relabel. So the dense one serializes writers on a monitor and leaves readers unlocked — the
latitude the one-writer contract already grants ([storage.md](storage.md)) — while the
reference one gets its consistent snapshot from a single deref.

Order independence rests on the backward dependency and the forward propagation being the
**same** edge set. The class fixpoint re-examines a node when something it derives from
moves, reached through `:consequences`; if a justification id were ever rebound to a
different justification, a node's `:supports` would name a justification that now concludes
elsewhere, and its class would depend on a value the propagation can never carry to it — at
which point the answer depends on visit order, in either implementation. `p/next-id` is
monotonic, so the engine cannot construct that state.

### Tie-breaks and orderings key on content, not the handle

Every place the engine linearizes a set of beliefs — the tie-break in a dilemma, the stored
antecedent vector, a report's two sides, the list of reports, a list of justifications —
orders on **content**, never on the integer handle. This is one rule, and it is the subtle
half of order independence, so it has one home.

The handle is allocated in assertion order, so a lower handle marks a belief typed into the
KB earlier — "typed first" throughout this section means exactly that. Key any of those orderings on it and arrival
order is smuggled back in: the Nixon diamond elects the pacifist or the non-pacifist by who
was typed first; `(first (:sides c))` on a clash report means "which side was typed first"
on a report whose `:sentence` reads the same either way; `(first (contradictions kb))`
answers which pair was typed first on a call whose every other reading is
order-independent; a firing seeded by whichever antecedent triggered it would store `[h_b2
h_b1 rule]` one way round and `[h_b1 h_b2 rule]` the other. What a sentex *says* is the same
whenever it is asserted, so `solve/content-key`, `kb/antecedent-order` and
`kb/justification-content-key` sort by printed sentence, then context, then — only for a
pair a reader cannot otherwise tell apart — the handle. That last step does not undo the
rule: two beliefs with an identical content key *say the same thing*, so which one sorts
first is unobservable, and the handle separates only beliefs that are interchangeable —
never two that differ. Content decides between different beliefs; the handle only sequences
duplicates. The choice a dilemma's tie-break
makes stays arbitrary; arbitrary and stable is the contract, arbitrary and order-dependent
is the bug.

The informant enters a content key as its *sentence*, never as its handle: two
justifications for one conclusion usually differ in their rule before anything else, so a
handle there would decide the whole comparison on which rule was typed first. Ordering the
antecedent vector once, where it is built, is what makes `why`'s `:because`, `why-not`'s
`:missing` and `preview`'s `:antecedents` functions of the knowledge rather than of the
write.

### The touched window is a superset, not the flip set

`settle` publishes the region it moved so three readers — a consequence preview, a
consequence report, a change feed ([preview.md](preview.md), [feed.md](feed.md)) — get one
answer instead of each diffing the believed set at O(KB) per write. The window
deliberately means *what I published about this datum may be out of date*, which is a shade
larger than *whose belief flipped*.

That extra shade is load-bearing. A **redundant justification** — a second derivation of an
already-believed conclusion, conferring no stronger a class — is the write the JTMS declines
to relabel for, and that fast path is what collapses a recursive forward load from
O(derived²) to O(derived). Belief does not move, so no label does; but in a dilemma the
engine declines to decide, and the *reason* it hands back is the whole answer — so the
consequence's handle is noted as touched even on the fast path, O(1) at the write. Polling
every standing pair for its support count at report time would be O(standing) per settle
instead. Every consumer reads the window as a superset, so an extra handle costs a
re-derivation and never a wrong answer — which is exactly what lets a clash report be
carried forward for any pair the region did not move.

### The settle memoizes standing clashes

`settle` runs after every mutation, and both the negation nogoods and the definitional
clashes carry forward the answer for any pair whose members did not move. This is a memo on
the recomputation, not an optimization to taste.

One check per standing pair per settle is quadratic in the clashes a load creates: measured
at 36ms an assert against 8ms at 300 standing definitional clashes, and 56ms against 7.5ms
at 1600 standing dilemmas. The carry is sound because the memo compares as **values** every
input a check reads that is small enough to — the separations, the predicate properties,
the disjoint metatypes' membership — and weighs per pair the one input too big to compare,
the `genl` closure: a pair of unary memberships is decided by `disjoint?` of the two types
its sentexes name, so the memo stamps those two supertype closures, and an edge leaving both
standing is an edge the pair was not about. A `genlCx` edge retires the whole carry, since
which contexts can convict a pair is a question about the context relation rather than about
either half's reading of it.

The rule the whole scheme rests on: **a nogood whose detection reads a belief-following
cache its own member supports is not stable.** That is why `arity` is not a nogood though it
names a second believed sentex — `declared-arity` answers from a cache that follows belief,
so a nogood defeating the declaration would destroy its own premise — and reports instead.

### An un-merge re-seeds through a second channel

A datum displaced by an equality merge is OUT while its twin joins in its place, so a
partner arriving during the merge concludes at the twin's spelling. Stop believing the
equality and the twin is swept while the displaced spelling comes back — and the conclusion
has to be made again at the surviving spelling, or the KB believes both antecedents of a
forward rule and holds neither spelling of what they conclude. `settle` re-seeds the
recovered spellings and settles again.

Two other designs lose to that one on what they cost elsewhere. **Moving the reconcile into
the settle loop** keeps a single fixpoint, the better property in the abstract — but
`settle-finish` decides what the settle moved by diffing the supersession map it brackets,
so a reconcile running earlier would have to thread its own flips forward or a merge would
stop being reported as `:believed-removed` at all: a change to what every preview and feed
event says, to save a re-derivation. A **re-enter signal** from `settle-finish` is this same
second-settle loop with the bound further from what it bounds. What the shipped shape costs
is that a KB whose settle un-merges something settles twice; one that does not pays a deref
of an unbound var.

### There is no second axis

Defeat-class alone cannot separate "birds fly" from "penguins do not" — both are defaults,
and since strength propagates, the exception cannot buy rank from its rule either. The
tempting second axis is a **specificity heuristic**: score a type by the size of its
reflexive-transitive `genl` up-closure, a rule by the greatest such score among its
antecedent predicates, a datum by the greatest among its valid justifications, and on a tie
in class let the more specific member win.

Do not build it. `exceptWhen` makes the relation such a heuristic can only reconstruct
explicit: the exception is stated *on* the rule it excepts, so the general rule does not
fire and there is no tie to break. Deriving an ordering from the `genl` hierarchy is
inference *about* the knowledge rather than *from* it — it works when the exception happens
to be keyed on a narrower type and silently ties when it is not, so whether it applies
depends on how the ontology was written rather than on what it says. There is a single axis,
defeat-class, and a default/default clash it cannot separate is reported as a dilemma rather
than decided.

### The solver split is guarded in both directions

Only `:default` content is ever decided; `:monotonic` is the fixed background a solve
reasons *from*. That followed from `decide-nogood`, but nothing checked it, so `settle`
guards both ends: `check-solver-eligible` rejects a contested handle that is not `:default`
(read before any defeat lands, since `defeat-class` reports nil once a datum is OUT), and
`accepted-defeat` keeps only defeats the program actually offered.

The guards matter because `set-solver` takes any implementation, and an unclamped `:defeat`
would let a third-party solver withdraw known-true content the program never handed it. The
cost of a regression here is not a wrong answer; it is the engine quietly giving away
something it knows to be true. `asp_label_test` covers both directions.

## Namespaces and layering

Defends [namespaces.md](namespaces.md).

### The layering inversions live in wiring.clj, not at the call sites

The engine's requires run one way, from `kb` up through `checks`, `special`,
`integrate`, `chain` and `settle` to `vaelii.core`, and the compiler checks every edge.
Three calls break that order, and all three live in `impl/wiring.clj` instead of at the
call site that needs them.

None of the three is a misplaced function waiting to be moved somewhere that restores
the one-way order. `assert-sentence` is called back from `impl/nat.clj` and
`impl/skolem.clj` because storing is a whole assert — naming, the definitional checks,
the index, chaining, settle — so the write path itself runs chaining, and chaining mints
a constant by calling back into that same write path. The cycle is in the behaviour a
NAT or a skolem witness needs, not in how the code happens to be arranged, so no
rearrangement removes it. `solve-goal` is the prover registry that
`impl/resolution.clj` calls to discharge a deferred antecedent, and `unknown` runs that
same registry back over its own argument — negation-as-failure is mutually recursive
with the chainer that asked for it, not merely calling down into it. `import-dump` sits
`impl/io/import.clj` above `vaelii.core` because reading a dump is asserting: it
re-canonicalizes records, reindexes and recovers through the public write path.
`core/import!` is `export!`'s inverse, and a round trip whose two halves are not both
public is not a round trip, so the delegation has to point up to reach `vaelii.core`.

Gathering the three in one file beats leaving each as a `requiring-resolve` at its own
call site. Scattered, a `requiring-resolve` is invisible: nothing counts it, nothing
stops the next one, and the set of places the layering is broken can only be recovered
by grepping for it. Gathered, they are an inventory — three entries, each owing the
reason it cannot be an ordinary require — and `lein lint`'s E8 fails a literal
`requiring-resolve` anywhere else under `src/`, excepting the keyword-dispatch
registries it names. A cut with a real fix takes the fix; one that lands in the
inventory argues for itself in writing first.

## Storage and the single writer

Defends [storage.md](storage.md).

### Records and the index are separate stores

The record store and the index store sit behind separate protocols rather than
one, and the split follows directly from an asymmetry between what each holds. The
records are what has to survive: lose one and the knowledge behind it is gone, so
durability is the record store's problem. The index is a cache over the records —
every entry is recomputable from them, which is what lets `reindex` throw the whole
index away and rebuild it from scratch. Merging the two into one store would force
a single durability answer onto both, either persisting index structure that adds
nothing (since it is always rederivable) or leaving records exposed to whatever
cheaper guarantee suits the index. Keeping them separate lets each answer to what it
actually is: the record store to durability, the index store to representation.

### RAM records under a durable index is refused

Of the eight `:records` × `:index` pairings, RAM records under a durable index is
the one `open-kb` refuses. The index is derived from the records, so persisting it
over a record store that empties at JVM exit would leave index files on disk
describing records that no longer exist once the process ends. The next open of
that directory would find a populated-looking index and answer every query out of
stale index state rather than out of any record actually present, with no signal
that anything is wrong. Refusing the pairing outright is cheaper and safer than
trying to detect or repair that mismatch after the fact, so the axis combination is
rejected before a KB is ever built from it.

### Frames are positional, not tagged

A frame holds its record's fields positionally rather than as a self-describing
map, because nippy's default encoding writes the record's type tag and every field
name into every frame it serializes. Measured, that per-frame tagging costs 56% of
the store's size — over half of every durable byte written is field names and type
tags repeated once per record rather than payload. A positional frame carries only
the values, in a fixed field order the decoder already knows from the frame's
shape, so the redundant tag and name bytes are never written at all.

### The index WAL logs the operation, not the value

The index's write-ahead log records the write operation itself — `[:add-to-set k
m]`, `[:increment k]`, and so on — rather than the value the key holds after the
write. Logging the resulting value instead would mean re-serializing the whole set
on every add: the i-th add to a set of size i would write a value of size i, so N
adds to one key would cost O(N²) total WAL bytes rather than O(N). A few roots take
this hit hardest — `[:functor-root p]` and the common contexts — since they are
exactly the keys a bulk load adds to thousands of times each. Logging the operation
keeps every write O(1) in the size of what changed, independent of how large the
set it is changing has already grown.

### Torn tail recovery reads lengths, not frames

Finding where a log's readable tail ends is answered by reading each frame's
length and skipping ahead, never by decoding the frame's payload. The question
being answered is only how long the log is, not what it contains. Answering it by
thawing every frame ties the length-finding walk to the frame decoder's own ability
to read that data — and that coupling is exactly what makes a record class rename
dangerous: thawing every frame to find the tail would read the decoder's failure on
old data as a torn or unreadable log, and delete the store it could not decode
rather than the store it could not read. Reading only lengths keeps the walk
independent of the frame decoder, so a decoder that cannot read old data has no
power to make the recovery path erase it.

### The columnar and dense backends use unsynchronized fields

The `:columnar` and `:dense` index backends hold their mutable state in
`^:unsynchronized-mutable` fields rather than behind a lock or an atom, unlike the
rest of the engine's single-writer contract. Making them synchronized would buy a
consistent view for an incidental reader thread — one who reads the index
concurrently with the writer, such as a browser thread beside a REPL's KB — but the
engine's own single writer never needs that guarantee, since it is always the
thread doing the writing. The walk reads these fields at every frontier node, which
is the index's hottest loop, so paying for a volatile read or a lock acquisition
there would tax every lookup to protect a case that does not occur under the
contract the engine actually requires. The cost is pushed onto whoever keeps an
incidental reader off the writer's thread or behind a synchronizer of their own,
rather than paid by the writer on every read the walk makes.

The **dense truth-maintenance network** (`:tms :dense`) makes the opposite call, and
the difference is that it is the *default* — an opt-in index backend can push the
synchronization cost onto whoever selected it, but a default cannot ask that of every
KB, so it must honour the incidental-reader guarantee itself. It does, through a
`StampedLock`: point reads run optimistically and validate, so the steady-state read
stays lock-free like the index walk, while a reader that races a relabel is validated
into a consistent retry rather than left to tear. Measured, that costs the hot `in?`
about 3 ns — and the dense probe is still an order of magnitude faster than the
reference network's hash-set lookup it replaced as default (density.md), so unlike the
index there is no hot-loop tax to weigh against the guarantee. Iterating reads take a
shared stamp outright; they already allocate O(nodes), so the acquisition is lost in
the walk.

### The belief certificate records a clean bill, not the labels

A full `recover` settles two things a cold open would otherwise redo: the JTMS labels, and
that no definitional constraint stands in clash. The tempting way to buy back the second on
the next open is to store the first — snapshot the JTMS labels and map them back the way the
index image does its trie, so the open skips the whole rebuild.

Do not store the labels. A label is a fixpoint over the justification graph, and a stored
image of it is a value the open did not derive: to use it the open would have to reconcile
it against whatever the records now say, and a label that disagrees with a re-read record is
a belief nobody computed — [order independence](nmtms.md) spent for a warm start, and on top
of the reason the JTMS cannot be a write-ahead log in the first place
([why the index persists and these two do not](storage.md#why-the-index-persists-and-these-two-do-not)).
What a cold open can safely carry across is not the answer but the *permission to skip
re-deriving part of it*. So the certificate records only that a clean close found no standing
clash, plus the record store's slot fingerprint; belief is still rederived from the records
on every open, and the certificate only lets the closing settle skip the constraint-clash
scan whose result a clean close already proved. Any fingerprint mismatch discards it, so the
worst a wrong certificate can do is make an open redo the scan it always did — never believe
something no derivation produced.

## Indexing and retrieval

Defends [indexing.md](indexing.md).

### Handles get a key separate from tokens

The trie is ragged: arity varies and one sentex's path can be a proper prefix of
another's, so a node is leaf and interior at the same time. If a handle shared the
child-set token with the trie's other tokens, it would be indistinguishable from an
ordinary token — a handle is an integer, and so is a stored numeric argument like
`1970` — so `lookup [bornIn Tom]` over a stored `(bornIn Tom 1970)` would return
`1970` as a phantom handle, and `get-sentex 1970` names a real, unrelated sentex.
Neither rejecting a non-leaf terminus nor discriminating by type fixes this: the node
genuinely is a leaf, and a handle and a token are both integers with no marker to
tell them apart at read time. The fix is structural rather than a check: handles
live under their own key, `[:trie :handles prefix]`, and tokens under
`[:trie :children prefix]`, so `lookup` reading only the leaf key at its terminus
never returns a token as a handle, and `p/children` reading only the child set is
correct at such a node with no phantom branch reaching `plan/prefix-estimate`'s
fan-out.

### Child count is its own read

`p/count-children` answers a node's width off a cardinality directly — the set's
own count in the KV family, an edge-array span or a map's size in the columnar trie
— rather than by materializing the child set and counting it. The query planner's
cost model asks this once per literal per plan, so the cost of answering it is paid
on every plan the engine builds. Building the children to answer it would make
planning one fixed conjunction scale with the size of the KB rather than staying
flat: measured, over a 32x larger corpus, building the children to answer this reads
32x the facts and costs 25x the planning time, on a conjunction that never changed.
`lein perf`'s `plan-scaling` check holds the cost flat instead, which is what a
direct cardinality read buys.

### Rule defeasibility is not indexed

Nothing indexes `:defeasible`, and nothing should. Defaults fire from the same
agenda as strict rules — found by predicate like any other candidate, and fired at
the strength their own record reports — so nothing ever needs to enumerate the
defeasible ones as a group. An index that could enumerate them is an index that has
to be kept in step with a field the record already carries: every assert or retract
touching `:defeasible` would have to maintain a second copy of a fact the sentex
record already answers, for a query nothing in the engine actually asks.

### The exception index stays coarse

The exception re-check index answers "which rules might need re-checking", at two
coarse granularities, deliberately. The trigger is coarse: a fact on a predicate
arriving or leaving re-checks the rules whose exception mentions it, and any `genl`
/ `genlCx` edge change re-checks every exception-bearing rule wholesale, rather than
tracking which cached closure a particular exception query actually touched. Edge
changes are rare and exception-bearing rules are few, so the coarse trigger is
cheaper than the fine-grained alternative — and it cannot be subtly wrong the way a
closure-tracking scheme could, since it re-checks everything an edge change could
possibly affect rather than trusting a derived subset. The unit indexed is coarse
too: the rule, never the individual firing. A rule handle is already an antecedent
of every justification it licenses, so each conclusion it produced is reachable
through the consequence links that exist anyway. Indexing individual derivations
would buy nothing beyond what those links already answer, and it would grow the
store with entries for the exceptions that do not apply — against a rule index
whose scale is tens of entries, never millions.

### A variable functor rule is refused, not silently accepted

Where a variable functor sits decides whether the rule can be run, so the door splits
on it. In an **antecedent** — `(?p ?x ?y)` as a trigger — it names no predicate, and the
rule index is keyed by predicate (canonicalization numbers the functor to `?var0` like any
other variable), so no arriving fact can ever spell the key. Such a rule is **refused** at
`assert` with `:not-indexable`. Accepting it would leave it silently inert: reported as
asserted, never reachable by an antecedent lookup, so it would fire only when a concrete
antecedent beside it arrives — joining over whatever happened to be stored at that instant,
two arrival orders giving two answers. Refusing it surfaces the mistake where it is made.

In the **consequent** — `(implies (holds ?p ?x ?y) (?p ?x ?y))` — it is **allowed**. Range
restriction guarantees the functor is bound by an antecedent, so the rule fires forward with
the predicate ground, through its concrete antecedent's own index entry; and its consequent
is filed under one catch-all bucket (`protocols/var-consequent-key`) that
`resolution/concluding-rule-handles` unions into every backward answer, since a rule
concluding `(?p …)` could conclude any predicate once `?p` binds. So the half the engine can
key is kept and the half it cannot is refused, rather than refusing both. The workaround for
the refused half is the instantiated rule, one per predicate, or a generator that stamps
them with the functor ground.

An **inert** rule (`set/inertRule`) is exempt from the antecedent refusal — it runs in
neither engine, so it promises nothing the index must answer for — and, concluding nothing,
its own variable consequent stays on the dead `?var0` key rather than the live catch-all,
so it never surfaces as a phantom concluder for every goal.


## Taxonomy and disjointness

Defends [taxonomy.md](taxonomy.md).

### An inert rule records transitivity, not a forward rule

A KB that computes transitivity in code rather than from a rule is a KB whose most
important rule is written nowhere. Asserting the transitivity rule bare would not be
documentation: it would be a forward rule materializing what the closure already
answers, one derived sentex per pair the closure already covers (see
[taxonomy.md](taxonomy.md) for the closure). The inert rule (`set/inertRule`) is the
spelling that writes the rule down without running it, so the claim is on the record
and no second engine computes it beside the closure.

### Recording a disjoint clique beats asserting it

`(disjointMetatype Metatype)` records that a metatype's members are pairwise disjoint
rather than asserting the pairs as `(disjoint …)` sentexes (see
[taxonomy.md](taxonomy.md)).

Asserting the clique instead would mean n(n-1)/2 stored premises for n members, and
premises rather than justifications is a teardown no retraction can reach. Recording
makes teardown exact: dropping the metatype releases every pair at once, and dropping
one `(M T)` releases exactly that member's pairs while the remaining members stay
separated.

### The answer is not found by testing every type

A goal with an open argument — `(disjoint a ?t)` — asks which types are separated
from `a`, not whether one candidate is. Testing every type in the KB would answer it,
but the cost is then a function of the vocabulary rather than of the goal: on an
imported ontology the vocabulary is six figures ([kbs.md](kbs.md)) where a term's own
declarations are three or four. The answer is read off `a`'s own declarations instead,
sized by what `a` actually declares rather than by everything the KB knows (see
[taxonomy.md](taxonomy.md) for `tax/separating-partners`).

## Inference and chaining

Defends [inference.md](inference.md).

### There is no separate defaults phase

Defaults look like they need their own rounds: derive the strict consequences, then
the defeasible ones, then re-run the strict chainer over what that produced. A phase
built that way cannot use the agenda, because the datums it must revisit are the ones
already believed — it degenerates into re-solving *every* default rule as a full
unindexed join over all facts, per round. A single defeasible rule then makes every
assert a full KB scan, and loading N facts costs O(N²).

Do not add the phase. One agenda is semantically neutral against two phases, and the
reason is narrow enough to state exactly: a default conclusion is placed
unconditionally, and whether it survives is decided later by `settle` from
recomputed belief. Phase ordering therefore cannot affect *what* is derived, only how
expensively it is found — either scheme computes the least fixpoint of the same
monotone immediate-consequence operator. The one thing separate phases are reaching
for is that a strict consequence of a default conclusion still gets derived, and a
unified agenda gets that for free: the default conclusion lands on the agenda and
triggers strict rules like any other new datum.

### Why a sort and not a search

Costing a plan by searching over candidate whole orders — summing intermediate rows
per candidate order, minimized over subsets, using `est-matches` as the per-literal
cost — is refuted, and measurably: on randomized joins such a search ran a mean 2.31×
the best permutation's actual rows, against cheapest-first's 1.19×, losing 3 trials of
9 and winning none.

The reason is not that a search is the wrong shape but that it minimizes a sum of
incomparable quantities: `est-matches` is an upper bound for some literals and an
average for others, so summing across literals adds numbers that answer different
questions. `est-rows` fixes that by giving every literal an expected value that
composes across a join, and once the numbers compose the ordering does not need a
search at all — the transposition law (descending `s/(n-1)`) sorts blocks in
O(k log k), no search.

### The loop guard's scope is the subtree, not the frame

A frame is not a path. `prove-from` expands a goal by pushing a single stack frame
that holds both the rule's antecedents and the conjuncts still queued behind the
goal, and those queued conjuncts are **siblings** of the expansion, not descendants
of it. Growing the guard to cover the whole frame would charge a later conjunct for a
goal key an earlier one claimed, and a conjunctive query would answer less than its
own conjuncts do: `[(anc Tom ?y) (anc Tom ?z)]` would come back empty where
`(anc Tom ?y)` alone answers twice, `provable?` would say false, and `prove-within`
would report `:status :complete` on a wrong answer.

This is also why the planner cannot be allowed to change an answer. Reordering
conjuncts moves which one claims a key first, so a guard scoped to the frame would
make `plan/*enabled*` semantic rather than a cost decision, and adding facts could
make a query stop answering. Scoping the guard to the subtree instead keeps it a
statement about descent — a claim about a path, not about a frame — so the order
conjuncts are tried in is free to change without changing what the query proves.

### The leaf must never itself backchain

`prove-from` and the node engine both take a `:leaf-solver` — how a literal the
search will not rewrite gets answered — and the division between rewriting and the
leaf is load-bearing: a leaf that itself backchained would run the engine's rewriting
*plus* a nested search per binding under it, compounding the two costs instead of
paying one.

Measured on a converging DAG (every node with two parents), against `ask`'s
6.7 / 3.9 / 4.0 ms:

| leaf solver | time |
|---|---|
| stored facts (`matches-visible`) | 6.5 / 4.5 / 5.4 ms — level with `ask` |
| the registry, which expands no rule | 5.2 / 6.4 / 9.6 ms — level with `ask` |
| a leaf that backchains too | 150 / 411 / 700 ms — 24-73x worse |

Both shipped leaf solvers — the stored facts and the registry — expand no rule, which
is what keeps either one level with `ask`. A leaf that searches is the one leaf shape
the design excludes.

## Exceptions

Defends [exceptions.md](exceptions.md).

### The exception belongs on the rule it excepts

A defeasible generality and its exception can be written as two unrelated rules
concluding opposite literals:

```clojure
(set/defaultRule (implies (bird ?x) (flies ?x)))
(set/defaultRule (implies (penguin ?x) (not (flies ?x))))
```

Nothing connects them. Both conclusions are derived, and the connection has to be
*rediscovered* syntactically at settle time by matching `S` against `(not S)` — which
puts every hard question in the rediscovery rather than in the knowledge: which
contexts make the pair a real clash, what breaks a tie between two defaults, and how
to recover an ordering the ontology already implies without reading it back off the
genl hierarchy ([why no such ordering is derived](defenses.md#there-is-no-second-axis)).

The deeper cost is that no argument survives. `why (flies Opus)` and
`why (not (flies Opus))` are two disjoint trees, and nothing records which won or
why — so an application cannot argue for or against a proposition, which is the whole
point of keeping justifications.

The exception belongs on the rule it excepts instead, naming the rule directly rather
than leaving the connection to be rediscovered:

```clojure
(exceptWhen (flightlessBird ?b)
  (set/defaultRule (implies (bird ?b) (hasAbility ?b flying))))
```

### The exception is not materialized per instance

An exception naming a rule could instead be materialized per instance: for each
ground binding under which it would hold, store the ground exception as an unbelieved
node and list its handle in the justification's `out` set. That implementation is
wrong twice over.

It would store the negative space. `(exceptWhen (flightlessBird ?b) ...)` over ten
thousand birds would materialize a probe for every bird that *is not* flightless,
which is nearly all of them — the store would grow with the exceptions that do not
apply, rather than with the exceptions that hold.

An arbitrary query has no handle to materialize either. `out` is a set of handles and
can only say "these specific propositions are not believed"; an exception answered
through transitivity or arithmetic has no single node whose OUT-ness stands for it.
The `out` slot is the wrong shape for this, independently of the materialization cost
above.

So a rule's exception is stored once, as a meta-sentex naming the rule, and
re-evaluated per firing rather than expanded into ground instances.

### A cycle through negation is rejected, not resolved

A rule set in which one rule's exception depends on what another rule concludes, and
that second rule's exception depends back on the first, is a cycle through negation —
the kind of program that admits zero or several stable models. Which model a reader
gets would depend on arrival order: settle the first rule before the second and one
model results, settle the other way and a different one might. That breaks the
order-independence invariant [nmtms.md](nmtms.md) holds non-negotiable — the same
knowledge asserted in any order must yield the same beliefs.

So a rule set with a cycle through negation is rejected at assert time, as a
well-formedness check over the rule dependency graph, rather than evaluated under
some fixed pick of stable model. Refusing the assert is what keeps every stored rule
set stratified, which is what lets the exception evaluator stay within one settle
pass instead of hosting its own model-selection machinery.


## Anytime inference

Defends [anytime.md](anytime.md).

### Qualitative cost tiers over time estimates

`ask-within`'s `:max-cost` ceiling is a qualitative tier (`:lookup` < `:compute` <
`:search`), not a per-prover time estimate. Wall-clock is a real measurement; a
per-prover millisecond estimate is not — no implementation has a way to compute one, so
it would be a constant standing in for a number nobody measured, and a real budget
cannot be gated against a number nobody measured. The qualitative tier asks a question
every prover can honestly answer instead: is the result looked up, computed, or searched
for? Admission stays coarse for the same reason there is no finer gate: reading a
prover's `est-bindings` against the remaining budget would gate on the same kind of
unmeasured estimate.

The `:search` tier stays in the taxonomy even though the shipped registry occupies none
of it. The tier is a claim about what a prover **may** cost, not a census of the ones
that ship — an application prover added through `add-prover` can claim it. Rule
expansion, `ask`'s own recursive case, is priced separately by `:max-depth`, because it
is a bound on depth rather than a claim about cost.

### Refusing an unrecognized cost ceiling

`ask-within` refuses a `:max-cost` value outside `:lookup`/`:compute`/`:search` (`:type
:unknown-option`) rather than reading it as no ceiling. A caller writing `:cheap` for
`:lookup` is asking to exclude the expensive tier, so running every tier anyway is the
one reading of that typo that is certainly wrong. Treating the bad value as unbounded
would also hide the mistake: a ceiling that admits everything returns exactly the
answers a correct one would, only slower, having done the work the bound existed to
avoid. Refusing the value surfaces the typo instead of silently discarding the budget's
intent.


## Qualitative constraint networks

Defends [qcn.md](qcn.md).

### Path consistency computes the greatest fixpoint, not the least

A fixpoint of the tightening operator is a network `X` with `tighten(X) = X`, and
tightening is monotone over a finite lattice, so more than one exists — a smallest and a
largest, each reachable only by iterating from its own end. Path consistency iterates
from the top, the network as given, and only ever removes; that lands it on the greatest
fixpoint, the one that says nothing is ruled out beyond what the constraints rule out.

The least fixpoint of the same operator is a genuine fixpoint and a useless one: every
constraint set to `#{}`. Intersecting the empty set with anything stays empty, so it is
perfectly stable, and it claims that no two regions can stand in any relation at all —
every KB's theory is contradictory, always. Nothing in the tightening equations rejects
that fixpoint; only starting from the top does.

The dual case sits a couple of namespaces away in this codebase, and the contrast is
exact. `jtms/region-classes` solves the defeat-class equation by starting every in-region
node at `:default` and iterating upward to stability — a least fixpoint, for the mirrored
reason: starting *that* computation from the top would let a node claim a strength
nothing conferred, the same way starting path consistency from the bottom would let the
network deny a relation nothing refuted. A least fixpoint means nothing is in unless
something put it in; a greatest fixpoint means nothing is out unless something took it
out. Reachability and derivation want the first kind; possibility and consistency want
the second — and path consistency is answering a possibility question, so it has to
start at the top.

Both ends are unique, which is what makes both order-independent regardless of which one
a given computation needs; uniqueness is available at either end, but only at an end, so
picking the wrong one does not fail loudly — it silently computes a different,
well-defined, wrong answer.

### An impossible network is reported off the pass, not thrown as a wff check

`wff` throws, and which fact it would throw on is whichever arrived last — the clash a
qualitative calculus finds is a property of a *set* of facts, not of any one of them, so
blaming a single member makes the stored KB's error depend on the order the facts were
asserted in. Throwing would also cost a fixpoint per assert, run whether or not anybody
asked for it, and the provers are opt-in, so a KB that never registered one would be held
to a calculus it never asked for. Recording the inconsistency where the pass already
proved it, in the violations ledger, costs nothing beyond a pass the KB already ran and
holds the property every other check in the engine holds: the answer does not depend on
the order the facts arrived in.

### A variable context goal fans over readers rather than reading one unioned network

A goal whose context is a variable means "in some context", the same reading every other
prover gives it, and the tempting implementation is to read every context's facts into a
single network and ask that. It is unsound: `(ntpp A B)` asserted in one context and
`(ntpp B D)` asserted in an incomparable one compose for nobody, since no context
inherits both, yet a single wildcard network holds them together and reports `A ⊏ D` — a
relation no reader of the KB actually sees. The prover instead fans over the readers (the
fact-holding contexts closed under where they meet) and unions their answers, so every
binding it yields is entailed for a reader that genuinely exists.

Reading only where facts are stated, rather than wherever is convenient, is a soundness
rule rather than a cost decision, and the two read the same on a KB that never retracts
anything — which is what makes the difference easy to miss. A join that read facts from
wherever was cheapest would wait for some unrelated fact to be asserted into the meeting
context — any fact, entailing nothing about the pair in question — and would then survive
that unrelated fact's retraction, because by then the firing has a justification of its
own that no longer depends on anything about the meeting. Reloading the identical content
from nothing would then not reproduce the KB, which breaks order independence
([nmtms.md](nmtms.md)): the belief a KB ends up holding would depend on which unrelated fact
happened to pass through the meeting context first, not on what was asserted.


## Operations and the daemon

Defends [operations.md](operations.md).

### A read that crosses the wire is realized inside the write monitor

Projecting a query's answer for the wire, or walking a KB's records for an export, is
what realizes what would otherwise be a lazy result. Doing that after releasing the
daemon's write lock is the tempting shortcut, since the lock is nominally for writes and
a query stores nothing — but a lazily realized result reads the KB at whatever moment it
is finally walked, not at the moment the op was dispatched. Run outside the lock, a
`:query` could straddle a concurrent `:assert` and report a KB that never existed at any
single instant: part of the answer reflecting the state before the write, part reflecting
the state after. An export has the same exposure for the same reason — it fetches record
by record rather than atomically, so a dump taken while something is asserting into the
KB is a dump of no single state, just a different KB shape than any that was ever
believed.

So both run *inside* the write monitor the daemon serializes every op through, trading a
query's chance to overlap a write for the guarantee that whatever it returns is a
snapshot of one real moment.

### Unknown subscription and bad cursor refuse rather than answer an empty feed

`:unknown-subscription` and `:bad-cursor` could each be answered with `{:events []}`
instead of a refusal — a dropped, timed-out, or foreign token, and a cursor that is
malformed or already ahead of what the subscription has delivered, all look like "nothing
new happened yet" from the wire. That is the tempting shortcut, and it is wrong for
exactly the reason a refusal exists at all: a feed that has stopped and answers
`{:events []}` is a feed its reader believes is still running, and a reader that believes
a dead subscription is live never resubscribes, never notices it has stopped receiving
events, and silently falls behind forever. Refusing by name — with a `:type` the client
can act on, by dropping the subscription or re-subscribing with a fresh cursor — costs
nothing an empty answer would have saved and tells the caller the one thing an empty
answer cannot: that there is nothing to wait for.

### The default collector is chosen against this engine's measured footprint

No collector flag is set for either the daemon or the container image, and that omission
is measured rather than skipped. `lein perf`, two alternating passes at a fixed 6 GiB
heap, 2026-08-06, put the JDK default at 40.7-41.2 s and 1493-1510 MB peak resident
against generational ZGC's 55.5-55.9 s and 6224-6258 MB — 36% slower while holding 4.2x
the resident set, and ZGC alone tripped the `:negation-arbitration` growth bound on both
passes.

A concurrent collector earns its throughput cost on a live set of tens of gigabytes,
where pause time dominates and a bigger resident set is the price willingly paid for it.
This engine's peak measured heap is 1.5 GB, nowhere near that regime, so the trade a
concurrent collector offers is not one this workload benefits from — it pays the
resident-set cost with nothing to buy back in return. The JDK default collector is not a
placeholder waiting for someone to pick a better one; it is the measured right answer for
this footprint, and picking ZGC is left to `lein with-profile +zgc`, for a JVM that runs a
different workload with a reason to want it.

## The web browser

Defends [web.md](web.md).

### Loopback only for the browser plus nREPL pairing

`lein browser` pairs two things that are each a considered risk alone and a remote shell
together: the browser's write route, unauthenticated, and an nREPL, arbitrary code
execution by design. Either one on a shared interface is a risk that stays local to what
it grants; combined, a request that reaches the browser can drive the REPL, and a REPL
is a way past every check the browser's own write routes enforce. So the pairing is not
configurable — the profile pins nREPL to `127.0.0.1` rather than trusting Leiningen's
own default, and the browser binds loopback with no flag to widen it. Exposing the
browser to another interface stays `--listen` on `-main`, which starts no REPL at all,
so the one config that is reachable off-machine never carries the arbitrary-code-execution
half of the pair.

### The term graph renders live, not behind a reveal button

A term page's concept graph draws itself on every render — server-drawn, no click, no
route, no state recording whether it is shown — rather than sitting behind a reveal
button a reader clicks to see it. A reveal button looks like the safer default: nothing
is spent until a reader asks. It is not, because it buys a saved read from the readers
who never click it and charges a whole extra round trip to the readers who do — the read
it defers is one the page already paid for in its own index groups and closures, so
deferring it saves nothing there and only adds a request most readers would end up
making anyway. A route to reveal it would also mean a `show=0` parameter, a
collapsed-versus-expanded fragment, and a second entry point rendering the same picture
with different chrome — three things to keep in sync for a feature that is otherwise one
function called from one place.

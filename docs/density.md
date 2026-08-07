# Density — the dense backends

- **Covers:** the dense int-postings, columnar trie, and packed-root backends that replace
  the default map-based index structures, and what each is measured to cost or save.
- **Not here:** the index's logical key layout these backends implement →
  [indexing.md](indexing.md); how `open-kb` selects a record/index backend pairing →
  [storage.md](storage.md).
- **Assumes:** sentex, handle, index, canonical form → [glossary.md](glossary.md).

`vaelii.impl.dense-kv`, `vaelii.impl.columnar`, `vaelii.impl.dense-roots`,
`vaelii.impl.tokens`, `vaelii.impl.dense-jtms`, and the record-side work in
`vaelii.impl.disk.*`.

These exist because of a gap between the engine's *seams* and its data structures at
corpus scale. The seams carry a large KB — the `AtomicSentex`/`RuleSentex` split, symbol interning,
an index derived from the records and rebuildable by `reindex` — while the default
structures are persistent Clojure collections holding boxed values, which measure
~1,973 B/fact of index (591.9 MB over 300k real facts, measured below). Each backend
here is a dense replacement for one of them.
**Every one is off by default**, selected per KB, and each is gated by a differential
oracle proving it answers the protocol identically to the structure it replaces.

Nothing here changes what the engine computes. If a dense backend ever returns a
different answer, that is a bug in the backend, not a feature of it — which is why the
oracles compare *sets*, not summaries.

## Selecting one

The records and the index are chosen on **separate axes** — `open-kb`'s `:records`
(`:memory` / `:disk`) and `:index` (`:memory` / `:dense` / `:columnar` / `:disk`), with
`:backend` as sugar naming a pair (see [storage.md](storage.md)). That split is what
lets the density work run durably: a dense index is *derived* state, so pairing one with
durable records costs only a rebuild on open.

| `:backend` | records | index | what it is for |
|---|---|---|---|
| `:memory` | RAM | `KvIndexStore` over a map | the default; no external dependency |
| `:memory-dense` | RAM | int-postings values | Phase 1 — the 31% of the index that is posting *values* |
| `:memory-columnar` | RAM | native int-token trie + int-keyed roots | Phase 2 — the 69% that is *keys and nodes* |
| `:disk-memory` | paged from disk | `KvIndexStore` over a map, rebuilt on open | durable records, nothing written for the index |
| `:disk-dense` | paged from disk | int-postings values, rebuilt on open | Phase 1's index, measured at durable scale |
| `:disk-columnar` | paged from disk | native int-token trie, rebuilt on open | Phase 2's index, measured at durable scale |
| `:disk` | paged from disk | `KvIndexStore` over a WAL-backed map | durability; the record side of the density work |
| `:overlay` | a decorator | a decorator | a fork over a frozen base — [overlay.md](overlay.md) |

The whole test suite runs on any of them: `VAELII_TEST_BACKEND=memory-columnar lein
test`. `backend_parity_test` runs a scripted KB session across all eight configurations
— the seven legal record×index pairs plus the overlay decorator — in an ordinary `lein
test`, so a divergence fails without anyone remembering to.

`:backend` names the *storage*. The third resident structure, the truth-maintenance
network, is orthogonal to it and is selected separately by `:tms` — `:reference`
(default) or `:dense` (Phase 3 below), either of which works with any backend.
`VAELII_TEST_TMS=dense lein test` runs the suite through the dense one.

## The measurement that shaped it

The index's cost is **keys, everywhere** — not the handle sets everyone assumes. On
300k real facts (`lein bench-densetrie`):

```
── index decomposition ──            MB    keys    values
  trie-counters                     137.6  137.6     0.0    ← pure key overhead
  trie-childsets                    202.2  105.2    97.0
  trie-leaves                       131.7   90.1    41.6
  root-arg                           98.7   52.6    46.1
  term-index                        196.8  101.3    95.5
  root-context / root-functor        31.7    0.6    31.1
  TOTAL                             591.9   (the whole index map, deduped)
```

The rows sum higher than the TOTAL, and that is not an error: a row is measured on its
own entries, so an object two subsystems share is counted twice across the rows and once
in the total. Read the rows against each other and the TOTAL as the retained size. About
487 MB of it is boxed structured-vector **keys**.

A trie node is three map entries (`[:trie :count prefix]`, `[:trie :children prefix]`,
`[:trie :handles prefix]`), and a path's every prefix is a separate vector object.

**The finding that had to drive the build: the win is the *layout*, not the interning.**
Interning tokens while keeping an object-per-node map (a fastutil
`Int2ObjectOpenHashMap` per node) recovers **1.28×** — per-node map overhead swamps it.
A columnar layout — parallel `int` arrays, zero per-node objects — gets **15–20×**. A
plausible design and a good one differ by an order of magnitude here, which is why the
bake-off ran before the build.

## Phase 1 — tiered int postings (`:memory-dense`)

`vaelii.impl.dense-kv` replaces each `PersistentHashSet` of boxed `Long` handles with
`IntPostings`: a sorted `int[]`, promoted to a `RoaringBitmap` past 128 members.

The tiering is measured, not assumed. Sorted `int[]` beats the boxed baseline
**5.6–6.3×**; **RoaringBitmap only 1.07–1.45×**, because the index's mass is in a very
large number of *tiny* postings where a bitmap's per-container overhead dominates. So
the answer was a size-tiered hybrid, not blanket Roaring — the opposite of the obvious
choice. Oracle: `dense_kv_oracle_test`. Measured 591.9 → 464.5 MB (**1.27×**).

**The tiering pays a second time on reads.** `kv-intersect` — what `sentexes-with-args`
and `sentexes-with-terms` bottom out in — narrows in the representation the postings are
already in rather than in the sets they would make: `RoaringBitmap/and` where both sides
are hot, a sorted two-pointer merge where both are cold and comparable, a probe of the cold
side's entries into the bitmap where the tiers differ, and — where neither side is a bitmap
and one is 32× the other — a binary search of the short run into the long one, which is
what a **mapped** root run needs, having no hot tier to probe at all (`dense-roots` reads a
snapshot's postings as plain sorted runs). Smallest posting first, so the accumulator
starts as narrow as any column can make it and only shrinks, and the one Clojure set is
built at the end at the size of the *answer*. Measured against folding
`clojure.set/intersection` over materialized postings, on one hot root and one rare
argument root:

```
  rare(4) ∩ hot(1000)      0.120 ms → 0.0015     80×
  rare(4) ∩ hot(32000)     4.734 ms → 0.0015   3234×    ← flat where it was linear
  hot(1000) ∩ hot(1000)    0.628 ms → 0.0149     42×
  hot(32000) ∩ hot(32000)  29.24 ms → 0.563      52×
```

Read down the column and the four rows say one thing: **the cost tracks the answer, not the
columns it came from.** The rare rows hold their answer at 4 handles while the hot side
grows 32× and the cost does not move; the hot ∩ hot rows grow their answer 143 → 4,572 and
the cost grows with it. That is the boundary contract showing through — the narrowing is
native, and what is left is `|answer|` handles boxed into `Long`s for a caller who was
promised a Clojure set. `lein perf --only intersect-selectivity` gates the first half of
it.

Every arm allocates its result, so a read can never shrink a posting it narrowed against.
The mutating `RoaringBitmap.and` instance method would, and would stay invisible until some
later query came back short — which is why `dense_kv_oracle_test` snapshots every posting
across a run of intersections and compares.

**Which families get packed is a decision, and it is checked.** A handle family is one
whose value is a set of handles: the trie leaves `[:trie :handles …]`, the three roots
`[:context-root …]` `[:functor-root …]` `[:argument-root pred pos …]`, the term index
`[:term-index …]`, both halves of the rule index `[:rule-index :antecedent|:consequent
…]`, and both halves of the exception index `[:exception-index <pred>|:rules]`. The rest
must *not* be packed: `[:trie :count …]` is an integer, `[:trie :children …]` holds path
tokens (numbers among them), and `[:term-roster]` and `[:argument-slot …]` hold term and
predicate *names*. One handle family packs on one backend only: the argument roots'
four-part key does not fit `dense-roots`' packed long (family | pos | term-id is already
full), so the columnar roots route the family to their boxed fallback —
`dense_routing_test` records that exception — while the tiered map backend, whose keys
stay boxed vectors and whose *values* are the packed postings, tiers it like any other
handle family.

Both dense backends keep a fallback for keys they don't route, which makes a routing
mistake behaviourally invisible — a misrouted family is stored as an ordinary boxed set,
answers every read identically, and passes both oracles and the `index-entries`
projection while buying nothing. So routing has its own test that reads the stored
*representation* rather than the answers, over keys taken from a real load rather than
spelled by hand: `dense_routing_test`. It also fails on a family nobody has classified,
so adding an index family forces a routing decision instead of silently taking the
fallback.

## Phase 2 — the columnar trie (`:memory-columnar`)

`vaelii.impl.columnar` is a native trie rather than a map of path keys: `int` node ids,
grow-on-demand parallel arrays (`counts` `int[]`, per-node child edges — sorted `int[]`
tokens and targets while narrow, one `Int2IntOpenHashMap` once wide — and `IntPostings`
leaves, so Phase 1 and Phase 2 are the same structure), and edges labelled with interned
`int` tokens from `vaelii.impl.tokens`.

It is **mutable, not a static CSR**, because the index mutates: a per-node child
structure plus a free list supports incremental add and remove, which a CSR cannot do
live. The
CSR is available as a *read optimization* instead — `columnar/compact!` freezes the node
graph into flat parallel `int` arrays (DFS-preorder renumber, which also reclaims the id
holes a churny load leaves), the read primitives dispatch on a `frozen?` flag, and a
write thaws back to mutable. That is the bulk-load-then-query move, and the record
store's own mutable-head/compacted-tail pattern.

**A node's child structure is tiered on its width**, for the reason that recurs across
these backends: a representation chosen for how it *holds* data has to be re-checked
against how the code *writes* it. Minting an edge in the sorted pair splices both arrays,
so it costs O(children already there) — and nothing bounds a node's width. The level-2 node
holds one child per distinct first argument of a predicate, so an array-only node
structure loads one broad relation — `(isa X T)`, `(genl S T)`, any hot relation in a
real ontology — in time quadratic in *that relation's own extent*. The cost tracks the
node, not the corpus. Holding 200k facts fixed and varying only the widest node's
fan-out:

```
  widest node   2,000 children    4,188 ms
  widest node  20,000 children    9,045 ms
  widest node 200,000 children   18,193 ms
```

So past `columnar/promote-at` (64) children a node's edges become one primitive
`Int2IntOpenHashMap` — O(1) insert, no splice — and drop back to the array pair below
half of it, the hysteresis keeping a node on the boundary from rebuilding on every
add/remove pair. Blanket maps are the wrong answer in the other direction: the bake-off
above put a fastutil map per node at 1.28× against the columnar layout's ~15–20×. The
tier takes both, because nearly every node is narrow and never leaves the dense pair.
Child order is not part of `p/children`'s contract — the flat-map index answers it out of
an unordered set — so a wide node's edges come off the map as they lie, and only
`compact!` pays to sort them, which the frozen CSR's binary search needs.

`lein perf --only columnar-fanout` is the gate: n sentexes on one predicate with n
distinct first arguments, so the only thing that grows between 4,000 and 64,000 is the
fan-out of the single node every insert passes through. The tiered node reads **1.07×**
growth against a bound of 2.00×; the array-only node reads 3.14×, and costs 4.3× as much
per insert at the larger size.

`vaelii.impl.dense-roots` is a key-interning `KvBackend`: the secondary roots, the rule
and exception indexes, and the inverted term index route into one
`Long2ObjectOpenHashMap` keyed by a packed `family | pos | term-id`, with the term
interned through the *same* dictionary the trie uses. Unrecognized keys fall back to a
plain backend, so it stays a full `KvBackend` and the composition above it is unchanged —
which here is three families: `[:term-roster]` and `[:argument-slot pos term]`, whose
members are term and predicate names rather than handles, and `[:argument-root pred pos
term]`, whose fourth key part the packed long has no room for (family | pos | term-id is
already full) and which `route` therefore sends to the fallback by name. The columnar
trie is native, so no `[:trie …]` key reaches this backend at all.

`vaelii.impl.tokens` is the `path-token ↔ int` dictionary. It interns a path level
**as-is** — a symbol, a number, `:false`/`:rule`, `nil`, a `[::subterm k]` arity marker,
or a whole literal list — because re-canonicalizing would turn a marker vector into a
list and break `sentex/subterm-mark?`. Content-keyed and first-writer-wins, so ids are
stable; the id *value* depends on encounter order, which nothing above it reads, so a
rebuild that interns in a different order yields an equal index.

It keys tokens by **Clojure** equality, and that is load-bearing rather than tidy. The flat
map it replaces keys its trie on a `PersistentHashMap`, where `(= 2 (int 2))` is true and a
path carrying an `Integer` reaches a node stored under a `Long`; a `java.util.HashMap` keyed
on the token says false, and the node is simply not found — one fewer answer, no error. The
two boxings meet in ordinary use, since `agg/count` concludes with an `Integer` and the same
sentence asked as a question carries a `Long`, and a whole literal list is a token too, so
the disagreement nests. A `Key` wrapper defers to `hasheq`/`equiv`, the same two the flat map
uses.

Oracles: `columnar_index_oracle_test` (including a compaction arm that freezes, re-checks
every read against the never-compacted reference, churns, re-freezes, and inserts after
freezing, and a width arm that drives one node across `promote-at` in both directions
with the threshold turned down — asserting the *representation* as well as the answers,
since no comparison of reads can tell a promotion that happened from one that did not),
`dense_roots_oracle_test`, `tokens_test`.

```
  whole index, 300k real facts   591.9 MB → 223.0 MB   2.65×   resident
                                          → 185.9 MB   3.18×   after compact!
  ├─ native trie                  52.4 → 15.4 MB (3.4× compacted)
  ├─ int-keyed roots + term index 69.1 MB  (was ~208 boxed)
  └─ shared token dictionary     101.4 MB
```

The dictionary is the largest part above, and every term-index key interns through it — so
what the term index keys on is what the dictionary is bounded by. A sentence's own body is a
subterm of itself, so keying each literal for *itself* mints one token per record, holding
exactly one handle: at that setting 4,754 records over 511 distinct terms produce 5,336
tokens, 4,750 of them whole lists. A dictionary of facts, over a vocabulary of hundreds.

**`sentex/*min-indexed-depth*` is the floor that refuses them**, and the bound is the
vocabulary. It drops a content literal's key for itself and keeps every compound nested inside
one, so nothing a probe is actually *for* loses its key (`(sentexHandle H)`, the sentence
inside an `(ist Ctx S)`), and a compound with no key is still found — from the atoms it
contains, verified against the record ([indexing.md](indexing.md), "Which compounds are
keys"). Measured on the same corpus at the same two sizes, 17,267 → 51,071 records over a
fixed 511 names:

```
                            keys for itself      the default
  mapped index, resident      13.0 MB              1.8 MB
  ├─ dictionary                9.8 MB (75%)        0.1 MB (6%)
  ├─ trie                      1.6 MB              1.6 MB
  └─ roots + term index        1.6 MB              0.1 MB

  growth over 2.96× the records
    dictionary                 2.94×               1.00×
    roots + term index         3.59×               1.00×
    whole mapped index         2.99×               2.35×
```

The dictionary and the roots are flat in the corpus and bound by the vocabulary. What
grows is the CSR skeleton, which is path-scaled and deliberately resident.

## Phase 4 — the record side (`:disk`)

Records already leave the heap on `:disk`; what was unmeasured was what reaching them
costs, and what a frame spends its bytes on. Both answers were surprising, and both are
in [storage.md](storage.md#the-on-disk-backend-disk):

- **A warm fetch was 52% slot read.** Not seek distance — *syscall count*: an unbuffered
  `RandomAccessFile` charged six syscalls to move 24 bytes. One positional
  `FileChannel` read each for the slot and the payload took a fetch 7.12 → 3.08 µs. The
  batched `get-many` the plan called for measured **0.91–0.95× — slower** — and was not
  built, because sorting a batch by offset removes no syscall.
- **56% of a frame was scaffolding.** nippy writes the record's type tag and every field
  name into every frame. A **positional** frame is 1.72× smaller and needs no dictionary;
  the `int[]` int-id body the plan called for measured **0.89× — worse than symbols** —
  because four bytes per token only beats nippy's symbol encoding where names are long.
- A bounded **hot-record LRU** serves 64–81% of a skewed stream (5.6× on a zipfian
  stream), and **tokenized bodies** (opt-in) take the log 92.3 → 45.8 B/record.

## Phase 3 — the dense truth-maintenance network (`{:tms :dense}`)

The index and the records are only two of the three resident structures. The **JTMS is
always in RAM in every backend**, and `lein bench-jtms` measures it at ~467 B/node —
~43 GB at 100M, on par with the whole record store. `vaelii.impl.dense-jtms` is the dense
representation, selected by `open-kb`'s `:tms` rather than `:backend` (it is orthogonal
to storage — any backend may use either network):

```
  109,055 nodes, a fact corpus         total    graph    justs
  :reference (atom + persistent map)    26.8     24.1      2.7
  :dense (bitmaps + primitive maps)      4.9      3.8      1.1   5.52×  (258 → 47 B/node)

  16,889 nodes, 60,486 justifications — a rules-heavy corpus (3.6 per node)
  :reference                            22.3     11.3     11.0
  :dense                                 6.8      2.0      4.9   3.26×
```

The decomposition (`lein bench-jtms`) refuted the plan the same way the index's did.
**The per-node scalars are already free** — stripping `:depth`, `:premise?` or `:datum`
releases *nothing*, because they are shared cached objects (small `Long`s, keywords,
booleans). 310 of the 467 B/node is the per-node **map object and its HAMT slot**, so
the lever is not "shrink the fields" but "stop having a map per node".

**Belief sets are the opposite regime from the index's postings.** `bench-postings` found
RoaringBitmap a *loss* (1.07–1.45×) on millions of tiny postings; `:in` holds nearly every
node and compresses **384×**. Both measurements are right — density is the variable, and
a single blanket answer would have been wrong in one direction or the other. Two more
consequences fall out of the same reading: with exactly two defeat-classes and only the
non-bottom stored, **the class map is one bitmap**; and adjacency reuses Phase 1's
`IntPostings` rather than a bare `int[]`, because a much-used premise's consequences grow
without bound and an array-copy insert would make loading such a rule quadratic.

**The compression that makes the belief sets cheap to hold made them expensive to
write, and the locality invariant is what noticed.** A `RoaringBitmap` is a sorted list
of 65,536-value containers, so any operation that rebuilds the whole bitmap costs one
pass over every container — invisible below 65,536 nodes, where there is exactly one.
`relabel-region!` did six such passes per call: it built each fixpoint's boundary with
the *static* `RoaringBitmap/andNot` (which copies every container), cloned that again
inside the fixpoint, and installed the answer with `.clear` + `.or`. So a **singleton
region cost O(believed)** — the opposite of what [nmtms.md](nmtms.md)'s locality
invariant claims, and undetectable in the table there, whose largest graph is 16,000
nodes.

It shows up when a rebuild adds a premise per stored premise. Adding premises in
batches of 250,000, and measuring the copying implementation against the in-place one:

```
  copying     15.6 µs/premise rising to 232.1   ×14.9 across 3M — quadratic
  in place     2.4 µs/premise steady at   2.5   ×1.04 across 3M — flat
  reference   11.6 µs/premise steady at  14.3  (persistent maps never have the problem)
```

What holds the invariant is not copying: `relabel-region!` clears the region out of each
live bitmap **in place** — the mutating `andNot` is a merge over the container lists and
touches only the region's own — and each fixpoint accumulates straight back into it.
That is worth ~56× over 3M premises (~388s against ~6.9s) and 6.5× even in the first
batch, because a clone is never cheap; it is also what puts the dense network 5× ahead
of the reference rather than behind it. **Do not reintroduce a whole-bitmap rebuild in
that path**, however local the code looks. The general lesson is the one this whole
document keeps finding: a
representation chosen for how it *holds* data has to be re-checked against how the code
*writes* it, and the two answers need not agree.

This one is a **parallel implementation** rather than a swap, and the reason is
atomicity, not caution: `RoaringBitmap` is mutable while the reference is an atom over a
persistent map whose all-or-nothing mutation `jtms_atomicity_test` pins. So both sit
behind a `vaelii.impl.jtms/Tms` protocol, and the dense one serializes writers on a
monitor while leaving readers unlocked — the same latitude the mutable index backends
take under the one-writer contract. `VAELII_TEST_TMS=dense lein test` runs the whole
suite through it; `jtms_dense_oracle_test` compares the two networks in full after every
step of randomized operation streams.

**A justification is not an object either.** A fact corpus derives about a tenth of a
justification per node and cannot say what one costs, so the decomposition was taken on a
rules-heavy corpus — a dense relation with a join rule over it, where every 2-path is a
separate witness:

```
  structure     118 B  43%   the record object + its map slot
  bindings       80 B  29%   the firing's variable map — belief never reads it
  antecedents    73 B  26%   a vector of boxed handles
  consequence     6 B   2%
  id / informant / strength / out    0 B   already shared objects
```

Two answers fall out. The belief-relevant fields become **columns keyed by justification
id** — an int column for the consequence, one `int[]` per antecedent list, a bitmap for
the strength (two classes again) — and a record is rebuilt only when a caller asks for
one, which no relabel does. And the **bindings leave the network entirely**: they are read
only to re-evaluate an `exceptWhen` query or a NAF antecedent per firing, both readers
hold the KB, and the record store has the record durably. `jtms/graph-just` is the
projection, applied by both representations, so neither keeps a second copy of a
justification and the two still store equal values. **277 → 85 B each**, and the dense
network's advantage on a rules-heavy corpus goes 1.61× → 3.26×.

## Reading these numbers honestly

Two caveats the measurements carry, both easy to drop and both load-bearing:

- **A uniform sample of a corpus breaks locality.** Sampling 202k records out of 11.3M
  sees each term about once, so a dictionary measured against it is corpus-sized while
  the store is sample-sized. That is why tokenized bodies read 2.02× on the log but only
  1.13× all-in: the dictionary row does not carry over, the log row does.
- **Retained heap (jol) is structural, so it is trusted under contention; wall-clock is
  not.** Every RAM figure here is jol; every timing was taken on an otherwise-quiet box
  and is indicative.

## Traps in measuring and writing one

Four that cost real time here, and that a fifth dense representation would meet again:

- **A fact corpus cannot size a rule structure.** At 0.12 justifications per node the
  justification columns are invisible; the rules-heavy corpus — a dense binary relation
  plus a join rule, so every 2-path is a witness — puts it at 3.6 per node and the
  numbers change shape. Size a structure against the corpus that exercises *it*.
- **Strip-and-remeasure needs a rebuilt baseline.** Stripping a field rebuilds the map,
  and an `into`-grown `PersistentHashMap` differs from an `assoc`-grown one by a few
  bytes per entry. That constant lands on every row and reads as *negative* cost for the
  shared-object fields until the baseline is itself a rebuild.
- **Columns are set, never merged.** A map entry is replaced wholesale, so every one of
  the parallel columns standing in for it has to be told; a column left alone on a re-add
  still answers for whatever held that id before.
- **A dense read must be total where the map it replaces was.** `handle-of` returns nil
  for an unstored sentence and `core/defeat-class` is called with it, so a bitmap read
  has to guard for a non-handle rather than `(int nil)` — a persistent map is total for
  free and a primitive column is not.

One language trap worth naming: `doto` clears its target *before* the argument
expression is evaluated, so `(doto mono (.clear) (.or (region-classes …)))` wipes the
boundary classes `region-classes` is about to read.

Harnesses: `lein bench-postings` (the Phase 1 bake-off), `bench-densetrie` (the index
decomposition and the trie bake-off), `bench-records` (the record side), `bench-jtms`
(the truth-maintenance decomposition and the two representations), `bench-scale` (the
Phase 0 per-component sizing).

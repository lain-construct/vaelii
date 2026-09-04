# What the process holds beside the stores

- **Covers:** the cache register (`vaelii.impl.caches`) — how a derived, droppable
  structure declares itself, what a descriptor says (`:scope` `:unit` `:limit`
  `:counters` `:note`), the one bound policy (wholesale clear, never eviction), the two
  reads `caches` / `clear-caches`, and a snapshot roster of every registered cache with
  its bound.
- **Not here:** what the *stores* cost — the JVM heap figure and a loaded KB's estimated
  footprint → [catalog.md](catalog.md); what the index *is* → [indexing.md](indexing.md),
  [density.md](density.md); readings about the *traffic* rather than the held answers →
  [profile.md](profile.md); readings about the *knowledge* → [quality.md](quality.md);
  the two numbers in the relation-algebra mask layer that bound a **build** rather than a
  cache — the algebra width, and the dense-table threshold → [qcn.md](qcn.md).
- **Assumes:** sentex, handle, generation, the `genlCx` closure, the change clock →
  [glossary.md](glossary.md), [taxonomy.md](taxonomy.md).

A cache is a map of answers the engine would otherwise recompute — atoms and plain
maps, none of them a store, all of them droppable without moving a belief. They do
not show up in a heap figure as anything but bytes, and "the second query was fast" is a
demo until a hit rate says *why*. This is the register that names them and the read that
counts them.

## The register

`vaelii.impl.caches` **requires nothing**. Every namespace that holds a cache requires
*it* and calls `register-cache` once at load, so there is no list here for a new cache to
be added to twice and no require edge from the reader down to the caches. The register is
open: a cache in a namespace this process never loaded — a qualitative calculus nobody
touched — is simply absent from the read, which is the honest answer rather than a row of
zeroes.

Each descriptor carries what a reader needs to compare rows that count different things:

- **`:scope`** — `:kb` for a cache hanging off one KB record, `:process` for a static one
  every KB in the JVM shares. It says what `:entries` counts.
- **`:unit`** — what one entry *is*: a literal, a network, a symbol, a mask. A column of
  bare integers compares none of them, so the unit rides every row.
- **`:limit`** — entries held before the cache is cleared, or nil for one bounded by
  something other than a count (a generation, the store lifecycle), named in `:note`.
- **`:counters`** — `:kb`, `:process`, or nil: what a row's `:hits` / `:misses` count,
  which is not always what its `:entries` count. The literal cache is the awkward case —
  per-KB entries, process-wide `AtomicLong` counters — and conflating them would bill one
  KB for another's hits. The closure neighbours are awkward the other way: the counters
  are readable at any time and the entries only from inside the search step that holds
  them, so that row reports a rate against a blank count.
- **`:note`** — one line: what it holds and what retires an entry.

A row whose `:entries` is nil cannot be counted from outside — it is scope-bound, alive
for the length of one chaining run or one search step and garbage when it returns. It is
registered all the same, so the list is complete rather than merely finite.

## The bound: cleared wholesale, not evicted

A counted cache past its bound is dropped **whole** (`assoc-bounded`), not trimmed to the
one entry that would make room. Evicting exactly the right entry costs more bookkeeping
than the entry saves, and a cache that has outgrown its bound is one whose questions have
moved on. A nil bound is not unbounded neglect: those caches are retired by a **generation
bump** (a taxonomy edge or context change retires every closure read at once), by the
**change clock** (a per-placement stamp, so a chaining run meets its own reads cold), or
they are structural (the symbol pool, the compiled algebras) where dropping entries costs
the sharing they exist for.

Clearing wholesale is cheap and it is fragile in one direction, so **a scan does not get
to fill one**. A read that asks thousands of literals *once* — a transitive closure walk
visits each node once and asks that node's neighbour literal once — pushes the literal
cache past its bound and clears it part-way through, discarding the entries a rule-heavy
query really does re-ask for a pass that had no repeat of its own to serve. A 5 000-node
walk crosses the 4 096 bound before it ends, having asked for a repeat on almost none of
those nodes. So the walk's neighbour probes read with `res/matches-visible`'s `cached?`
false, and the walk keeps its repetition
where the repetition is — the whole closure in `:closure-answers`, the neighbour sets a
join re-walks in the search step's memo. A cache earns its eviction where the questions
repeat; a scan is the read where they do not.

It is the *probe* that opts out, not the walk: the seed read a `(P ?x ?x)` condensation
takes is one extent literal, asked through the ordinary cached entry point, because one literal
asked once is not a scan.

## Reading them

- `(caches kb)` — one row per registered cache: `:entries :limit :unit :hits :misses
  :hit-rate`, plus `:scope` / `:counters` / `:note`, and `:error` where a row's own read
  threw (one broken descriptor costs its row, not the answer). Each row is a count off a
  map the engine already holds, **O(1)**, so the page that shows it can poll.
- `(clear-caches kb)` — drop every cache that offers a clear and say what went. Bare, not
  `!`: every entry is derived and no belief moves, which makes a clear a *measuring
  instrument* — clear, ask the same question again, watch the miss the second ask no
  longer skips. Scoped to `kb`; `{:counters? true}` also zeroes the process-wide rates, in
  a call that says out loud it reaches past its argument.

Both are on the remote surface (`vaelii.impl.serve`) and drive the browser's caches page.

## The roster (a snapshot — `caches` is the truth)

This list drifts; the register does not. Treat the table as orientation and
`(caches kb)` as authority. Presence depends on what is loaded: the qualitative caches
need the QCN/temporal reasoners, `hot-records` needs a disk-backed store.

**KB-scoped** — one set per KB:

| Cache | Unit | Bound | Retired by |
|---|---|---|---|
| Literal matches `:literal-matches` | literals | 4096 | wholesale clear; each entry clock-stamped, so any state change drops it |
| Taxonomy closures `:taxonomy-closures` | reach sets | — | taxonomy generation bump |
| Taxonomy closures, scoped `:taxonomy-scoped-closures` | visibility sets | 128 / relation | flush past budget, or generation bump |
| Taxonomy visibility sets `:taxonomy-visibility` | relation/context pairs | — | generation bump |
| Closure answers `:closure-answers` | closures | 100 000 members | wholesale drop; a single reach past the bound is never stored |
| Resident derived values `:resident` | networks & passes | 256 | wholesale clear |
| Hot records `:hot-records` | records | 65 536 / kind | per-kind LRU (`vaelii.disk.cache`, 0 disables); disk stores only |

**Process-scoped** — shared by every KB in the JVM:

| Cache | Unit | Bound | Retired by |
|---|---|---|---|
| Symbol pool `:symbol-pool` | symbols | 1 000 000 | wholesale clear |
| Relation decode tables `:relation-decode` | masks | 8192 | wholesale clear |
| Compiled algebras `:compiled-algebras` | algebras | 64 | wholesale clear |
| Path-consistency passes `:path-consistency` | networks | 256 | wholesale clear |
| Network support passes `:network-support` | networks | 256 | wholesale clear |
| Metric closures `:metric-closures` | networks | 256 | wholesale clear |
| Metric path reconstructions `:metric-reconstructions` | networks | 256 | wholesale clear |
| Stored handles `:stored-handles` | sentences | — | structural |
| Closure neighbours `:closure-neighbours` | neighbour sets | — | structural |
| Pinned values `:pinned-values` | resident values | — | structural |
| Justification dedup `:justification-dedup` | conclusions | — | structural |

The units do not sum: eighteen rows counting eighteen different things. A total across
them is a number of nothing.

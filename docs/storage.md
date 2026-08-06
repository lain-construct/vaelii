# Storage

`vaelii.impl.protocols`, `vaelii.impl.kv`, `vaelii.impl.memory`,
`vaelii.impl.disk.*`.

## Protocols

Two protocols keep the reasoning code independent of any backend:

- `RecordStore` — canonical sentexes and justifications, keyed by integer handle:
  `put-sentex`, `get-sentex`, `delete-sentex!`, `put-justification`, `get-justification`,
  `delete-justification!`, `next-id`, the provenance triple, premise tracking, and
  `clear-records!` (the whole-db wipe). Both puts honour an `:id` on the record they are
  given — that is how an import lands records at the handles a dump gave them — and
  `next-id` is required to stay above every handle the store holds however it arrived.
  A handle is an identity, so no store may issue one twice. Both backends allocate from
  a counter of their own rather than from a field of the record map, and both lift it
  clear of an explicit `:id` as the record lands: one handle is minted per stored sentex
  and per justification, and forward chaining takes one per firing
  ([inference.md](inference.md)), so the allocation is a compare-and-set on a `Long`
  and not on the store.
- `IndexStore` — the trie, the secondary roots, the rule index, the exception index,
  and the term index (see [indexing.md](indexing.md)), plus `clear-index!` (the
  whole-db wipe `reindex` rebuilds from) and `index-entries` / `index-load`, the
  `[structured-key value]` projection all four index backends share — what a dump
  writes, and why an index written by one loads into another.

A `KB` record bundles the two stores with the twenty-odd other slots the engine hangs off
one value — the prover registry, the solver, the contradiction and violation bookkeeping,
the settle and chain statistics, the resident qualitative networks, the match and naming
caches, the feed. **The engine programs against these protocols and never against a
concrete backend**, so a KB built on any store runs the whole engine unchanged. Records
are in-memory (default) or on-disk; the index has four representations, and the pairings
are below.

## Two stores

| Store | Holds | Standing |
|-------|-------|----------|
| record store | sentexes + justifications (values); a per-handle provenance map | the ground truth |
| index store  | trie, rule index, term index (keys → sets/counts) | derived from the records |

**The asymmetry is the design.** The records are what has to survive: lose one and the
knowledge is gone. The index is a cache over them — every entry is recomputable, so
`reindex` throws the whole thing away and rebuilds it from the records. Durability is
therefore the record store's problem alone, which is why the two are separate stores
behind separate protocols rather than one.

That also sets what each backend owes. A record backend must persist; an index backend
need not. The index is resident in RAM: the on-disk one logs its mutations for a fast
restart but still holds the whole map in memory. The one exception is the
`:disk-columnar` image ("The image", below), which is off by default and `mmap`s the
leaf handles and root postings rather than reading them onto the heap.

Two space numbers (`:record-space` / `:index-space`, default 0/1) namespace the pair so
several KBs coexist in one process; each backend uses them as it sees fit — the memory
backend keys its registry by number, the disk backend derives a directory from them.
Naming one in-RAM number without the other is refused: the unnamed half would sit in
the default space, and two KBs meaning to be disjoint would share it.

**An option `open-kb` does not read is refused, not ignored** (`:type
:unknown-option`), and the space numbers are why. Every other opt fails loudly when it
is wrong — an unknown `:backend` throws, an impossible axis pair throws — but a
*misspelt* one is a key nothing looks at, so the KB opens on the default space and reads
and writes there in silence. Two KBs a caller built to keep apart then share one store:
each one's flush empties the other, and the second reads out of records the first
cleared. Downstream, a KB that took the default is indistinguishable from one that asked
for it, so the mistake is only legible in the opts map itself. `kb/opt-keys` is the set,
and a fork's `:base` and `:overlay` maps are held to it too.

## Backend selection: two independent axes

The asymmetry above is a **selection** axis, not only a design note. The records answer
to durability and the index to representation, so `open-kb` chooses them separately —
`:records` (`:memory` / `:disk`) and `:index` (`:memory` / `:dense` / `:columnar` /
`:disk`) — and `:backend` is sugar naming a pair, spelled **`<records>-<index>`**.
`vaelii.impl.kb` is the only place a concrete store is named (`record-store-for` /
`index-store-for`); everything above reads the protocols.

| `:backend` | records | index | |
|---|---|---|---|
| `:memory` (default) | RAM | RAM map | one store on both axes |
| `:memory-dense` | RAM | int postings | [density.md](density.md) Phase 1 |
| `:memory-columnar` | RAM | native int-token trie | [density.md](density.md) Phase 2 |
| `:disk-memory` | durable | RAM map | rebuilt on open |
| `:disk-dense` | durable | int postings | rebuilt on open |
| `:disk-columnar` | durable | native trie | rebuilt on open |
| `:disk` | durable | durable | one store on both axes |
| `:overlay` | a decorator | a decorator | a fork over a frozen base — [overlay.md](overlay.md) |

`:memory` and `:disk` are the two pairs that are the same store on both axes, named for
the store rather than doubled into `:memory-memory` / `:disk-disk`.

- **Memory records** (`vaelii.impl.memory`) — plain Clojure maps in atoms, **no
  serialization** (records held directly, structured key vectors used as map keys). They
  have **space-number sharing**: a process-global registry keyed by `:record-space`
  means two KBs constructed over the same number share one store, so a restarted KB
  (`recover`) sees the records the first wrote — the persistence tests' contract.
  Durable within a JVM, not across a process restart.
- **Disk records** (`vaelii.impl.disk.record-store`) — an on-disk log-structured store in a directory
  (`:dir`, or derived from the space numbers). Durable across a process restart and
  crash-safe, with no server. Selected for the whole suite with
  `VAELII_TEST_BACKEND=disk lein test` (durability parity gate: identical results).
  Detailed below.
- **A derived index** — the RAM map, the dense postings, the columnar trie — holds
  nothing that is not recomputable, so it is never written. Over durable records that
  costs one `reindex` per open (below); in exchange, every density experiment can be run
  against a durable KB instead of only in RAM.

The axes admit eight pairings and **seven are legal**, each with a name: RAM records
under the durable index is refused, since the index is derived from the records and
persisting it over a store that empties at JVM exit leaves index files describing records
that are gone — the next open would answer every query out of them. So `:records` /
`:index` are for overriding *half* of a name, not for reaching a pair the table left out,
and `VAELII_TEST_BACKEND` takes a name. `./scripts/test-backends.sh` (`lein
test-backends`) runs the whole suite on all seven, one log and one ✔/✘ per run, plus an
eighth over the `overlay` decorator. `backend_parity_test` also runs one scripted KB
session across every pair in an ordinary `lein test`, so a divergence fails without
anyone remembering to.

`:overlay` is the one selection that is not a store: it is a **decorator** over whatever
each axis resolved to, naming its frozen base with `:base` and its own writable half with
`:overlay` — the fork of [overlay.md](overlay.md), of which `core/fork` is the ergonomic
spelling.

### A derived index over durable records (`:disk-memory`, `:disk-dense`, `:disk-columnar`)

The records open populated and the index opens empty, so such a KB needs its index
rebuilt before it can answer anything. `recover` alone is **not** that: it rebuilds the
TMS and taxonomy *by reading the index* (`special/rebuild-taxonomy` reads the functor
root), so over an empty one it would recover an empty KB and report nothing wrong. The
repair is `reindex` — rebuild the index from the records, *then* recover — and
`{:recover? :auto}`, the default, runs it and logs how long it took.

That log line is the point of interest: the rebuild is O(records) on **every** open, so
whether it is worth buying back — by persisting a snapshot of the derived index, which
is what `:disk-columnar`'s image below does — is decided by that number at the corpus
size in question. `lein bench-reindex [facts] [rules] [index]` produces it. Measured on a generated corpus of **105,392 records**, single-threaded:

| index | reindex | records/s | recover | open | extrapolated to 100M |
|---|---|---|---|---|---|
| `:memory` | 2.7 s | 39k | 2.6 s | 5.3 s | ~84 min |
| `:columnar` | 1.7 s | 61k | 2.6 s | 4.3 s | ~68 min |

Only the first column is the price of a derived index: the `recover` half is the TMS and
taxonomy rebuild every durable KB already pays, and it dominates at this scale. So the
open cost of *not* persisting the index is roughly 2× a durable-index open.

#### The image (`vaelii.index.snapshot`, off by default)

`:disk-columnar` can write that rebuilt index to disk and **map it back** instead of
recomputing it — `vaelii.impl.disk.index-snapshot`. The compacted trie's CSR arrays and
the roots' packed postings are already flat `int` runs, so the image is a write rather
than a serialization; the skeleton and the token dictionary are read into heap on open and
the leaf handles and root postings are `mmap`ed, which is the whole residency claim.

It is a **cache of derived state**, and everything else follows from that. The image is
stamped with the record store's slot fingerprint and checked on every open — never behind
a flag — and any doubt at all (format, `kv/index-layout-version`, byte order, records that
moved, a short section, a missing commit marker) discards it and runs the same `reindex`
above. A write thaws whatever it lands on, mapped or frozen alike. The image is written
when the directory closes, so it never outlives what it describes by more than a crash,
and a crash leaves no image at all.

The swap is an atomic rename of the new file over the live one, which Windows will not
do while the target is mapped — so the image is **macOS and Linux only, and the engine
refuses it elsewhere**: `vaelii.index.snapshot` on an unsupported platform throws
`:unsupported-platform` naming the property, the OS and the reason, and an image already
in the directory is discarded as one more `decision` mismatch class. Only the publish is
implicated: the `:disk` backend's logs, slots and lock run on every platform, and with
the property unset a `:disk-columnar` KB opens there and rebuilds its index from the
records.

One part of it does not work: the token dictionary is **not** vocabulary-scaled, so it
is read into heap whole and its cost grows with the number of distinct terms rather
than with residency.

A derived index is shared for the life of the JVM under the identity of the records it
belongs to — the space number for RAM records, the **canonical directory** for durable
ones. Keying a disk-backed KB's RAM index by `:index-space` instead would hand two KBs
over different directories one shared index whenever they took the default numbers. If
the records are emptied out from under it, the leftover index is dropped on the next
open rather than left describing records that no longer exist.

### The index is written once — `KvBackend`

`KvIndexStore` (`vaelii.impl.kv`) is the **generic** `IndexStore`: the whole trie /
roots / rule / exception / term-index logic lives there, in terms of a small `KvBackend`
protocol — scalars, counters, sets, an N-key `kv-intersect`, a `kv-member?` probe, and a
`kv-batch` that lands one sentex's entire path (levels, term index, roots) as one unit. A
backend supplies only that adapter:

- `MemoryKvBackend` (`vaelii.impl.memory`) — one map keyed by the logical vectors;
  `kv-intersect` is `clojure.set/intersection`, `kv-members` returns the stored set by
  reference.
- `DiskKvBackend` (`vaelii.impl.disk.kv`) — the same in-RAM map, durable behind a
  write-ahead log (below).

`kv-member?` is there for a *cost* rather than an answer. `exception-rule?` — the gate
the firing path takes once per candidate rule per new datum — asks whether one handle is
in the roster, and a backend that packs a posting (`vaelii.impl.dense-kv`,
`vaelii.impl.dense-roots`) has to answer by probing it, not by materializing the roster
and testing the result. On the two backends above the two roads read identically, which
is exactly why nothing behavioural catches the difference: `lein perf --only
exception-roster-gate` is what defends it, and `kv_membership_test` is what says every
adapter's probe agrees with its own `kv-members`.

So a new backend (SQL, overlay) is a new `KvBackend` rather than a second index,
contract-tested by `kv_backend_test` (every adapter satisfies one spec). The one
`IndexStore` that is *not* a `KvBackend` is `ColumnarIndexStore`
(`vaelii.impl.columnar`), which implements the trie natively over CSR arrays and
delegates the flat families — roots, term index — to an embedded `KvIndexStore` on the
same keys, so the two answer alike. The **record store** stays per-backend
(`MemoryRecordStore` / `DiskRecordStore`) — a handle→blob map is simple enough that
sharing it buys nothing.

## The on-disk backend (`:disk`)

`vaelii.impl.disk.*` — a self-contained, durable, crash-safe store in a directory, no
server.  Its substrate (`files`) is append-only `.log` files of length-prefixed nippy
frames plus fixed-width 24-byte `.idx` slots keyed by integer id.

- **`DiskRecordStore`** (`disk.record-store`) — the `RecordStore` protocol over three
  per-kind log/idx pairs (sentexes, justifications, provenance).  A record is **paged**
  from disk on `get`: one positional read of the 24-byte slot, one of the payload it
  points at, then the thaw.  Both are `FileChannel` reads that name their offset, so
  neither uses nor moves the RAF's shared file pointer, and neither pays the seek and
  four primitive reads an unbuffered `RandomAccessFile` would charge for the same bytes
  (measured: that was 52% of a warm fetch).  Only the small set of live handles per kind
  sits in RAM (for O(1) enumeration), plus a **bounded LRU of hot records**
  (`vaelii.disk.cache`, `:cache-capacity`, 0 disables) — sound because a record is an
  immutable value and the three paths that change what lives at an id all maintain it
  (`store!` replaces, `kill!` evicts, `clear-records!` empties; compaction preserves
  content and so needs nothing).  `next-id` recovers as `max(a counters blob, 1 + the
  highest slot id)` — the highest slot survives deletes and compaction — so a handle is
  never reused.  A premise is a sentex with non-nil `:strength`, so the premise set is
  derived from the durable records, not stored — and derived without *reading* them:
  every write puts the answer in two bits of its slot's reserved `flags` word (bit 0 =
  the slot speaks, bit 1 = premise), so an open reads the set off the idx walk it
  already makes for the live handles.  A slot that does not speak — one written before
  the bits existed — sends that one handle to its record, and the record wins wherever
  both do, which is what keeps the bits a cache rather than a second truth.  Two bits
  and not one for the same reason: a legacy slot reads as 0, and 0 has to mean *unknown*
  rather than *not a premise*, so no store needs rewriting and no version needs bumping.
- **The frame codec** (`disk.codec`) — a frame holds its record's fields
  **positionally**, because nippy otherwise writes the record's type tag and every field
  name into every frame, which measured 56% of the store.  A sentex frame is
  `[tag sentence context id truth strength …]`, a justification frame a bare vector (one
  shape needs no tag), and provenance — an open application map — passes through as it
  comes.  Each decoder dispatches on the thawed frame's shape, so **frames written before
  the codec still read** and no store needs rewriting.  Decoding interns the symbols it
  rebuilds, so a paged record shares one vocabulary object per name with the in-memory
  store instead of minting a private copy per fetch.
- **Tokenized bodies** (`disk.tokens`, opt-in via `vaelii.disk.tokens` / `:tokenize?`) —
  the positional frame still spells its sentence out, so the vocabulary is written into
  every frame.  A tokenized frame replaces the s-expression fields with one varint byte
  string of ids from a **durable** `tokens.log` (id = append order, content-keyed,
  first-writer-wins, never reused).  A frame citing an id the dictionary lacks is
  unreadable data, so the ordering is what makes it safe: a token is written **before**
  the frame citing it, and `fsync` fsyncs the dictionary **first, holding the sentexes
  kind lock**, so nothing is appended between the two fsyncs and every record durable
  after a tick has durable tokens.  (fsyncing per *new* token would give the ordering
  too, and it is the wrong trade: a cold load is then fsync-bound, measured ~217
  records/s.)  Between ticks the two logs can still skew on a machine crash, the
  same cross-file skew a log and its idx have; `open-record-store` repairs it as
  `validate-idx-tail!` does, by tombstoning a record whose ids the dictionary lacks.
  Only symbols and
  keywords are interned — numbers and strings ride beside the id stream as literals, so
  a KB of measurements cannot mint an entry per value.  It is two more frame *tags*, not
  a format change: a store reads plain, tokenized and pre-codec frames side by side, so
  turning it on costs no rewrite and turning it off orphans nothing.
- **`DiskKvBackend`** (`disk.kv`, behind `KvIndexStore`) — the index is derived and
  small (and `reindex` rebuilds it from the records), so the whole key→value map lives in RAM,
  exactly as `MemoryKvBackend` holds it, with every mutation appended to a `kv.log`
  write-ahead log that replays on open.  Durability without changing the index logic.
  The WAL is **logical**: a frame is the write op itself (`[:add-to-set k m]`, `[:remove-from-set k m]`,
  `[:put k v]`, `[:delete k]`, `[:increment k]`, `[:decrement k]`), so a set-add logs the one added
  member — O(1) — and a bulk load of N members into one root writes O(N) WAL bytes.
  (Logging the resulting *value* would re-serialize the size-i set on the i-th add and
  cost O(N²), with a few hot roots — `[:functor-root p]`, the common contexts — dominating.)
  Replay folds each frame through the same `apply-op` that applies a live op; `compact!`
  rewrites the log as one `[:put k v]` op per live key, so every frame is a uniform op
  and the reader needs no snapshot-vs-delta discrimination.  Compaction is this store's
  snapshot cadence — it bounds replay length and reclaims the delta frames, triggered
  off a delta-accumulation ratio (`dead-ratio` = frames beyond one-per-live-key).

**Durability + crash-safety.**  A daemon (`disk.durability`) fsyncs every store on a
tick and a JVM shutdown hook closes them.  Logs are recovered on open: finish an
interrupted compaction, truncate a torn tail, tombstone any slot now past EOF.

Finding that torn tail reads the frame **lengths** and decodes nothing
(`files/log-tail-offset`): a prefix, a skip, repeat, through a positional read window,
since a `RandomAccessFile` is unbuffered and a `seek` per frame is syscall-bound.  Not
decoding is the point rather than a side-effect — the question is *how long is the log*,
and answering it by thawing every frame made a record class rename delete the store it
could not read.  The length chain suffices because a frame is appended **before** the
slot that points at it, so a torn tail frame is one nothing references, and
`validate-idx-tail!` is what reconciles a slot against a log that lost its end.  A
**non-positive** length ends the walk: no frame payload is empty, so a zero is space
never written, and a filesystem that zero-fills past a tear would otherwise be walked to
EOF four bytes at a time and pronounced intact.

A clean `close!` records each log's length in `clean.nippy` and the next open skips the
walk while the length still agrees; the marker is *consumed* on open, so it only ever
describes a store nobody holds, and any disagreement — stale, absent, unreadable, past
EOF — falls back to the walk.

The walk finds a frame boundary; it cannot say whether what remains is *everything*,
and a short index opens populated-looking and answers short forever — re-asserting a
fact it cannot find mints a second handle for a sentence already stored.  Two
instruments close that, each for the loss that defeats the other, and `open-kb`'s
coverage gate reads both.  The **batch-seal counter** (`kv/sealed-prefix`) is
incremented as the *last* op of every `index-sentex` batch and decremented as the
last op of an unindex's cleanup, so it equals the indexed-sentex count exactly when
every batch landed whole: a torn append-mode tail keeps a batch's prefix — the root
count included, which is why the root count alone is the wrong instrument — and loses
the seal first.  The **length check** compares the file against the clean marker
before the marker is consumed: a compacted log is one flat `[:put]` per key in hash
order, so a tail lost at rest — a short restore, a partial copy — is arbitrary keys,
the seal possibly among the survivors, and only the length says the file is not the
one that was closed.  Either sign, and the gate rebuilds the index from the records.
A store whose seal reads zero — one written before the counter, or an index installed
whole by `import-dump`'s replay — is checked by the root count alone, as before.

The index WAL additionally **compacts on a clean close**
when its dead ratio has earned it (the same switch and threshold the background tick
uses), because opening it is a replay and so costs the frame count rather than the
live-key count.  Measured at 300k facts, that compaction is worth 4.5× on reopen (36.2s
uncompacted against 8.0s), and the index's own share of the open is where nearly all of
it sits (32.9s against 6.5s).

Compaction never edits in place — it rewrites to a temp, fsyncs, drops a commit
marker, then replaces the original, so a crash mid-compaction recovers to the last
durable state.  The record store's compaction is **copy-on-write**: the O(live) record
rewrite (read + thaw + re-freeze + write every live frame) runs *without* the kind
lock, reading the log's immutable region through a private read handle, so reads and
writes of that kind do not stall for it.  Only two brief lock holds bracket it — a
snapshot of the live slots up front, and a delta reconcile + swap at the end that folds
in whatever was stored/killed during the rewrite (a concurrent `clear-records!` sets an
abort flag and the reconcile discards its temps).  `reindex` rebuilds the index from the records on
disk unchanged.

**The switches are checked.**  Every `vaelii.*` property the backend reads — the tick
(`vaelii.disk.sync-ms`), `vaelii.disk.fsync`, `vaelii.disk.auto-compact`,
`vaelii.disk.compact-dead-ratio`, `vaelii.disk.compact-min-interval-ms`,
`vaelii.disk.compress`, `vaelii.disk.cache`, `vaelii.disk.tokens`, `vaelii.disk.lock`,
`vaelii.index.snapshot` — has a domain in `vaelii.impl.config`, and a value outside it is
refused with `:unknown-option` naming the property, the value and the legal spellings.
`open-kb` reads the lot before it opens anything (`config/check!`), which is the earliest
door: two of them are read per fsync tick, where a throw is a log line nobody can
attribute.  The boolean switches share one vocabulary — `true` / `1` / `on` / `yes` and
`false` / `0` / `off` / `no`, case-insensitively, a blank value being unset — so a
spelling that works for one works for all of them, and `=disabled` is an error rather
than the opposite setting.  `vaelii.disk.fsync` takes `dsync` or nothing, and
`vaelii.disk.compress` `zstd`, `lz4` or `none`.

**Single-writer.**  `disk.lock` takes an exclusive OS `FileLock` on `.vaelii.lock`
when a directory opens and fails fast if another JVM holds it — enforcing the
single-writer contract.  `-Dvaelii.disk.lock=false` (or `0` / `off` / `no`) turns the
lock off, for a filesystem whose `FileLock` is unreliable (some network mounts).  It
removes the *enforcement* and not the contract:
a second writer under it corrupts exactly as the contract says one does, with nothing
left to fail fast.
`vaelii.core/close!` releases it without the JVM exiting —
flush and close each component, deregister from the durability daemon, drop the lock —
so a long-running process can hand the directory to another process.  An unclean close
still releases: every component gets its close attempt, the lock release and the
registry removal run even when one throws, and the first component failure is rethrown
*after* that cleanup — so a throw from `close!` means the directory is handed back but
the close was not clean.  Within one process, stores are shared per canonical
directory (`disk.backend`, a registry mirroring the memory backend's db registry), so
two KBs over one directory share the durable store — the restart contract the recovery
tests rely on — and the lock, file handles, and durability registration are taken once;
closing either KB closes both.

## The sentex records — `AtomicSentex` and `RuleSentex`

A sentex is stored as one of **two records**, split so an atomic sentex does not carry
the seven rule-only slots — there are 100M+ facts, and each dropped reference field is
~4 bytes across all of them (measured: the record shell falls from ~80 to ~48
bytes/instance, ~3.2 GB at 100M). Both share a scalar **core**; `RuleSentex` adds the rule
decomposition. The `sentex/sentex` constructor canonicalizes the structural connectives
and `set/*` wrappers into these fields rather than leaving them as sentence data, and
emits the right record.

The **core** (`AtomicSentex` and `RuleSentex` alike):

- `:sentence` — the readable, normalized form (`(not (flies Tweety))`,
  `(implies (and A B) C)`), kept for display and matching.
- `:context` — the context symbol it holds in.
- `:id` — the integer handle, `nil` until the record store assigns one.
- `:truth` — `:true` / `:false`. A `(not S)` becomes `S` at `:false`, and **double
  negation is eliminated** (`(not (not S))` ⇒ `:true` over `S`, via `peel-not`).
- `:strength` — the assumption strength (`:monotonic` / `:default`) when the sentex is
  asserted as a premise; `nil` for a purely-derived sentex. The record store writes it
  on `mark-premise` and reads it back with `premise-strength`, so premise strength
  lives **on the record**.

**`AtomicSentex`** is an atomic sentence — a fact, a metadata declaration, or a query
pattern: one signed predicate application, ground or holding variables. It adds nothing
to the core. Reading any rule-only key off an `AtomicSentex` returns `nil`, so
`(some? (:antecedent sx))` is the atomic-vs-rule discriminant everywhere — no consumer
needs to know which record it holds.

**`RuleSentex`** is an implication, and adds the decomposition:

- `:antecedent` — the antecedent patterns as a vector (a leading `and` unwrapped).
- `:consequent` — the consequent pattern.
- `:varmap` — `{?var0 ?x, …}` mapping each **canonical variable** back to the name the
  author wrote, so `sentex/originalize` can restore the original form for display.
- `:direction` — the inference direction, set by the rule's `set/*Rule` wrapper:
  `:forward` / `:backward` / `:inert`, or `:both` for a bare `implies`. The wrapper
  canonicalizes into the record exactly like the connectives do, so a rule carries its
  own direction rather than it living in a side index.
- `:defeasible` — `true` for a `set/defaultRule` rule (its conclusions fire at
  `:default` strength and can be defeated); `nil` otherwise. Wrappers may nest, so a
  defeasible forward rule sets both fields.
- `:assumption` — `true` for a `set/assumptionRule` whose head is a *choice* for a
  solve rather than a derived truth; `nil` otherwise. Part of the rule's **identity**
  (it is a constant slot in the trie key), so a choice rule and its bare twin are
  distinct sentexes — see [solving.md](solving.md).
- `:constraint` — `:hard` for a `set/hardConstraint` rule and `:soft` for a
  `set/softConstraint` one, `nil` otherwise: the head is a contradiction the solver must
  avoid rather than a truth to derive. In the trie key on the same footing as
  `:assumption` — see [solving.md](solving.md).

An `exceptWhen` exception is **not** among these. It is a separate meta-sentex naming the
rule's handle, so it is not in the trie key and a rule and its excepted twin are the same
sentex — asserting the exception amends the rule in place. See
[exceptions.md](exceptions.md).

The constructor also puts the sentence into a **canonical form** — canonical
variables, canonical antecedent order, sorted symmetric arguments, and folded /
collapsed comparisons — so logically identical knowledge dedups to one handle. Sorting
symmetric arguments needs the taxonomy, so callers that store or look up a sentex go
through `res/kb-sentex`, which supplies `:symmetric?`. See
[indexing.md](indexing.md) for how this reaches the key.

Both indexes are built from this decomposition: the **term index** is fully
connective-free (heads stripped even nested in a rule), and the **trie key** drops
the `implies` / `and` rule frame — a negative literal keeps its `not` there as its
polarity (see [indexing.md](indexing.md)). `AtomicSentex` and `RuleSentex` are records (not bare
maps) so each round-trips through nippy (the on-disk backend) with its type intact.

## Provenance — a side map, not record fields

Bookkeeping about *who* asserted a sentex and *when* lives in a **per-handle
provenance entry** keyed by the record handle, deliberately **beside** the record
rather than as fields on an `AtomicSentex` / `RuleSentex` / `Justification`. Two reasons the shape
is a side map:

- The record shapes stay fixed. Adding `:who` / `:when` / `:confidence` / `:source`
  slots to every sentex would bloat the hot on-disk value and the trie-adjacent
  canonical form for metadata belief never reads. The map is open — an application
  puts whatever it wants there — without the record schema ever growing.
- It is **not belief**. Belief is a pure function of the justification graph
  (docs/nmtms.md); provenance is annotation *about* an assertion event. A wall-clock
  `:created` therefore cannot affect order independence — nothing in `relabel` /
  `settle` reads it.

`assert` stamps `{:creator :created}` on the sentex it creates — `:creator` from
`opts :creator` or the dynamic `*creator*`, `:created` from the dynamic `*clock*`
(epoch millis by default; both bindable, which is how tests pin them). Creation is
**first-writer-wins**: re-asserting an existing sentex keeps its original stamp,
while any `opts :provenance` map is merged in. `add-provenance` layers application
fields on later; `provenance` reads the map. It is torn down with the record — a
`retract!` (via `delete-sentex!` / `delete-justification!`) deletes the provenance entry
alongside the record, so it never leaks past the thing it annotates. The store methods
are keyed by any handle, so the seam admits justification-level provenance (derivation
who/when); only asserted sentexes are stamped.

## Serialization

The engine stores Clojure data — records, symbols, keywords, numbers — and every
backend must preserve it type-faithfully (a keyword read back as a keyword, `1970` as
a number, an `AtomicSentex`/`RuleSentex` back as itself), or `lookup`'s wildcard descent silently
matches nothing (`kv_backend_test` and `index_edge_test` guard exactly this).

- **In memory** there is nothing to serialize: records sit in the map directly and
  the structured key vectors are the map keys (equal vectors are equal keys).
- **On disk** values are **nippy**-frozen into the log frames and thawed on read, so
  an `AtomicSentex` round-trips as an `AtomicSentex` and a `RuleSentex` as a `RuleSentex`; the in-RAM index map
  is rebuilt from the WAL frames the same way. nippy freeze is a pure function of its
  value, so equal values freeze to equal bytes.

## The canon gotcha

`LazySeq`, `PersistentList`, and vector can be `=` yet freeze to **different**
nippy bytes — and even two `=` `PersistentList`s (a reader literal vs one built
by `apply list`) differ. More basically, an in-memory map keys on `=`/`hash`, and a
`LazySeq` and a `PersistentList` that are `=` still must key identically. So every
sentence is canonicalized to a single `PersistentList` shape by `sentex/canon` (in
the `sentex` constructor), and `kv/term-key` canonicalizes lookup terms too (via
`sx/canon`). Anything that builds a sentence or a term for a key must go through
`canon` / `sentex/sentex`.

## Symbol interning

`canon` also **interns** every symbol it canonicalizes, through a process-wide pool
(`sentex/symbol-pool`, a `ConcurrentHashMap`), so a predicate, type, individual,
context, or variable name is a **single shared object** across every sentex that
mentions it, so the sharing it buys dwarfs its own footprint: a `parentOf` or `dog` in
millions of facts is one symbol, not one per fact. The trie key gets the sharing for
free, since `alpha-rename` passes constant symbols through unchanged, and the context is
interned by the constructor. Interning changes object identity, never equality, so a
pooled `?var0` still matches a fresh one as a binding key.

What bounds the pool is **not** the vocabulary. A KB that only names things holds one
entry per distinct name, but three writers mint a fresh symbol per *fact* — NAT
reification (`nat/fresh-constant`), head-existential skolemization
(`skolem/skolemize-conclusion`) and abduction's scratch contexts — and the pool is
static, process-wide and shared by every KB, so nothing hands an entry back. So it is
capped at `sentex/*symbol-pool-limit*` (1M, several times any real vocabulary: the
shipped ontology plus the whole of OpenCyc is ~188k constants) and cleared **wholesale**
when full, the shape the other bounded caches take. A clear costs the sharing for the
names minted before it and can change no answer, since identity was never what anything
read.

## Persistence & recovery

The record store, trie, term index, and rule index all persist — durably across a
restart on the `:disk` backend, and within the JVM on `:memory` (the space-number
registry). The **taxonomy** and **JTMS graph** are in-memory, so a KB constructed
against an existing store has to rebuild them. `open-kb`'s `:recover? :auto` default
does it at construction (`true` is an alias for it); `:warn` leaves them empty and says
so, `false` leaves them empty in silence, and both leave the repair to a `core/recover`
call of the caller's own. Nothing else is a setting — a value `recover-modes` does not
name is refused (`:unknown-option`) rather than read as the warn branch, since a KB that
silently took `:warn` answers `[]` to everything and reads like an empty store. Either
way recovery is these two steps:

- **taxonomy** — re-integrate the special-predicate sentexes (`rebuild-taxonomy`
  queries `genl`/`genlContext`/`disjoint`/`disjointMetatype`/predicate-props/`inverse`).
- **JTMS** — the record store tracks live sentex ids, justification ids, and premise
  ids; each premise's assumption strength rides on its own sentex record (the
  `:strength` field, no side hash). `rebuild-tms` recreates a node per sentex, marks
  premises at their stored strength, adds every justification as
  a justification, and `relabel` recomputes belief. `recover` rebuilds the JTMS
  *before* the taxonomy (`rebuild-taxonomy` reads **stored**, not believed,
  sentexes, so `:support` / `:cache-support` record every asserting sentex —
  belief-filtering the replay would drop a disbelieved supporter, and clearing
  its defeat could never revive the entry) and then settles, whose
  `refresh-beliefs` applies belief afterward, so strengths, defeats, and reported
  conflicts are re-derived on restart and match either side of a restart.

Derivation depths reset to 0 on recovery (they only bound future chaining).

### Why the index persists and these two do not

All three are derived from the records, so "it can be rebuilt" does not separate them.
What separates them is **how** each is derived, and it decides the storage form each can
take.

An index entry is a **pure local function of one record**: `sentex/path`, `kv/root-keys`
and `kv/sentex-terms` read that record and nothing else. So a write touches ~6.2 entries
and no others, a log of write ops replays to exactly the map that produced it, and the
cost of persisting is proportional to the change. That is what makes `disk.kv`'s logical
op-logging work at all, and it is why the index is the half that persists.

A JTMS label is **not local** — it is a fixpoint over the justification graph, and one
assert can flip an unbounded region of it. Logging label changes would mean logging the
whole cascade per assert, which is precisely the cost `add-just*`'s
redundant-justification fast path exists to avoid. So the JTMS cannot be a write-ahead
log for the same reason the index can: the shape of its derivation is different.

That argues against *logging* it, not against *snapshotting* it — a snapshot is O(nodes),
written once and read once, and it is what the mapped index image already does for the
index. The taxonomy sits at the other end again: its adjacency is O(V+E) and each edge
insert is local and O(1), so it is a set-and-counter structure that `KvBackend` could hold
with no new ideas — the reason it is not held there is that nobody has needed it to be,
not that it resists it.

Two numbers to keep apart before acting on this. The Phase 0 "taxonomy ≈ 0" figure is
**residency** — 0.0 MB, 0 bytes/fact — and says nothing about rebuild *time*:
`rebuild-taxonomy` does a `sentexes-with-functor` per declaring functor plus a record
fetch per hit, and on a corpus where `genl` is a top predicate that is a great many
fetches. And `recover`'s 7,792 ms at 313k records is not decomposed, so how it splits
between the two is unmeasured.

**Atomicity.** All validation (naming, wff, arg/disjoint/functional/negation
checks) runs *before* any write, so a rejected assert leaves no trace (tested).
Cross-store atomicity is bounded by the two-store design: each side commits as a
single unit, and `reindex` rebuilds the index from the records to repair a torn
write.

## The single-writer contract

**One process, one writer.** The engine pairs a durable store with in-memory state
(the TMS, the taxonomy closures), and only the writing process's memory tracks its
writes:

- *Two threads, one process:* every TMS mutation applies atomically
  (`jtms/swap-with-result!` for the result-returning ops, `swap!` for the rest),
  so concurrent operations **compose** — none is silently lost. That is a
  liveness floor, not a semantics: interleaved `assert`/`retract!` sequences are
  not serializable (find-or-create and the settle pipeline are check-then-act), so
  concurrent *writing* still needs a single writer. A reader thread beside a writer
  thread (the web browser over a REPL's KB) is the supported shape.

  **Two selectable index backends are narrower than that**, and it is the one place the
  floor does not reach. `:columnar` (`vaelii.impl.columnar`, and the `vaelii.impl.dense-roots`
  it builds on) and `:dense` (`vaelii.impl.dense-kv`, whose `IntPostings` is mutated in
  place) hold `^:unsynchronized-mutable` fields, so a write
  publishes through no barrier: a second thread may read an array reference, a
  capacity, the CSR-mode flag or a half-installed mapped section from before a growth,
  a compaction or a snapshot install, with no happens-before edge to stop it. The atom-
  and lock-based backends give the incidental reader a consistent view; these two do
  not, and keeping such a read on the writer's thread or behind a synchronizer is the
  caller's. The fields are unsynchronized because the walk reads them at every frontier
  node — the index's hottest loop — where a volatile read buys a guarantee the engine's
  own single writer never needs.
- *Two processes, one store:* not supported, and worse than stale — process B's
  belief filter hides A's facts, and B's retraction sweeps **delete records A
  still believes**. The `:disk` backend enforces this with an exclusive file lock
  that fails a second opener fast (`:type :disk-locked`), and there is no read-only
  open: `lock/acquire!` takes the whole file exclusively or throws, so the second
  process never reaches the records at all.

The contract is a property of the engine rather than of any backend: a shared record
store is not a shared KB, because belief lives in the writing process's RAM. So it holds
whatever the store underneath is, and no choice of backend relaxes it.

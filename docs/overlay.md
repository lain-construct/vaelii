# Forks: an overlay over a frozen base

`vaelii.impl.overlay.kv`, `vaelii.impl.overlay.store`,
`vaelii.impl.overlay.frozen`, `vaelii.impl.overlay.mount`; `core/fork`.

A **fork** is a private, writable KB layered over a shared, read-only **base**. Reads
resolve fork-first and fall through to the base; writes land only in the fork; **the base
is never mutated**. So N forks can hang off one base and each keep its own divergent
copy, and the sharing costs nothing — no copy, no protocol between them, no coordinator.

The sharing is **within one process**. A `:disk` base is opened through the ordinary
durable store registry, which takes the directory's exclusive single-writer lock
(storage.md, "The single-writer contract"), so a second JVM mounting the same base
directory is refused with `:type :disk-locked` — base immutability is a property of the
decorator, not a licence to open the bytes twice.

```clojure
(def base (v/open-kb {:backend :disk :dir "/kb/frozen" :recover? :auto}))
(def f    (v/fork base))                             ; ephemeral: an in-RAM overlay
(def g    (v/fork base {:backend :disk :dir "/kb/g"})) ; durable: remountable later

(v/assert f '(penguin Pingu) 'BirdContext)   ; f believes it; base and g do not
```

`opts` names the fork's *own* storage, as an ordinary opts map — so the two variants are
spelled with the backends that already exist rather than with names of their own: an
in-RAM overlay is the ephemeral hypothesis, a disk one is durable and remountable.

A fork assembled from opts alone spells it out instead — which is how a durable fork is
remounted, in a later process, over the base it was taken against:

```clojure
(v/open-kb {:backend :overlay
            :base    {:backend :disk :dir "/kb/frozen"}
            :overlay {:backend :disk :dir "/kb/g"}
            :recover? :auto})
```

A base opened this way is held to the index key-layout sentinel `open-kb` holds its own
half to ([indexing.md](indexing.md), §7) — and refused (`:type :stale-index-layout`)
rather than rebuilt, since rebuilding is a write and a base is mounted read-only. Open
that directory as a KB once, which clears and rebuilds it, then mount the fork over it.

## Why one decorator forks the whole index

`KvIndexStore` (`vaelii.impl.kv`) implements every index family over one substrate — the
count-aware trie, the context / functor / argument roots, the rule index, the exception
re-check index, the inverted term index and the term roster — and it holds no state of
its own: every read bottoms out in `kv-members`, `kv-count`, `kv-intersect` or
`kv-get`, and every write in `kv-batch`. So a single `KvBackend` decorator merges the
entire index, and the trie walker, the matcher, the planner, the TMS and the query layers
need no part in it. That is what the `KvBackend` seam buys.

Two things follow, and they bound the feature.

**The columnar index is not forkable this way.** `vaelii.impl.columnar` is a *native*
`IndexStore`: its trie is int-id nodes in parallel arrays, with no keys and no backend
underneath, and only its roots / term / rule / exception families delegate to an embedded
backend. A KV decorator over it would fork those and silently leave the trie behind, so
`fork` refuses it by name. The forkable index axes are `:memory`, `:dense` and `:disk`.

**The TMS is not storage.** Belief lives behind its own protocol (`vaelii.impl.jtms`,
with `dense-jtms` as a second implementation) over state derived from the records. A fork
therefore gets its *own* network, and the engine already has the operation that computes one
from records: `recover`. So `fork` recovers over the merged view rather than layering one
truth-maintenance graph over another. One pass over the merged records, which is what
`recover` costs anywhere.

## The merge model — index half

`OverlayKv` is a composite `KvBackend` `{overlay base}`, per key:

| shape | rule |
|-------|------|
| set | `members(K) = (base(K) ∪ overlay(K)) − removed(K)`; `base(K)` is empty if `K` is tombstoned |
| scalar | the overlay's value shadows the base's |
| counter | **copy-on-write** — the first `kv-increment`/`kv-decrement` seeds the overlay from the base value, so afterwards it holds base+net |
| whole-key delete | a **sticky** tombstone shadows the base for that key; a later `kv-add-to-set` repopulates it from the overlay *only* — "deleted, then re-added fresh" |
| whole-store clear | one `::cleared` flag, after which every base key reads absent |

A base set cannot be edited, so removing an inherited member is *recorded* rather than
applied: `[::removed K]` holds the base members this fork took out of `K`. All the
bookkeeping — `::cleared`, `::deleted-keys`, `[::removed K]` — lives in the overlay under
reserved namespaced keys that no index key can collide with, which means it is exactly as
durable as the fork is and a remount needs no separate recovery step.

**`kv-count` answers the merged cardinality**, never the overlay's. The count-aware trie
is a selectivity structure — `plan/order` costs every conjunct off `count-at` and
`provers/est-bindings` off the functor root — so a base-blind count would not be a wrong
answer, it would be a silently wrong *plan* for every query touching inherited content.
`kv-intersect` merges for the same reason: `sentexes-with-args` intersects the
predicate-scoped argument roots, and it has to see the base's postings.

**Merging is not the same as building the merged set**, and on a fork the difference is
what every query plan costs. Read the rule backwards: `(base ∪ overlay) − removed`
collapses to `base` exactly when the base is visible and the overlay holds neither members
of its own at that key nor a record of a removal there — which is the shape of nearly
every key a fork reads, since the whole point is that N processes share one base and each
writes a little. `kv-count` and `kv-members` recognize that case and hand the base's own
answer straight back, and `kv-intersect` recognizes it across *all* of its keys at once —
when every one is inherited the whole narrowing goes to the base, which then does it in
whatever representation it holds rather than in sets the merge would have flattened it
into first ([density.md](density.md)). Over a flat-map base the two roads read the same, because its
`kv-members` is a reference return; over a `:dense` base, where the posting has to be
materialized into a Clojure set first, counting through the merge cost 12.6 ms per call on
a 100,000-handle root — a selectivity read, per conjunct, on a key the fork had never
written to. `lein perf --only overlay-selectivity` is the gate. `kv-member?` is the same
observation at member granularity: it probes both sides rather than merging them, which is
what keeps the `exception-rule?` gate O(1) across the seam.

`kv-get` is the scalar/counter read and does **not** merge set values. No key in the index
is read both ways (the trie's counters go through `kv-get`, its handle sets through
`kv-members`), and a backend is free to hold a posting privately — `vaelii.impl.dense-kv`
hands back an `IntPostings` here — so merging at that op would mean type-testing another
backend's internals. `kv-entries`, whose contract *is* Clojure sets, merges properly, and
it is what an export of a fork writes.

**`kv-clear!` is O(1), and it is what makes `reindex` work on a fork:** the flag hides the
base wholesale, so clearing the merged index and rebuilding it from the merged records
means what it says. The rebuilt index is then wholly the fork's — the sharing is spent,
deliberately, because that is what the caller asked for.

## The merge model — record half

`OverlayRecordStore` is a composite `RecordStore` `{overlay base}`.

- **The id seam.** The fork's handle counter is seeded above every handle the base holds,
  so a minted handle can never collide with a base one. A record written at a handle the
  base *already* uses is therefore an **override** — same handle, different record — and
  the overlay's copy wins every read. That is how a base record is edited without editing
  the base: `mark-premise` materializes an override before it writes, since the assumption
  strength lives on the record.
- **Tombstones.** Deleting an inherited record cannot touch the base, so it is recorded
  and the read path filters it. They are sticky: an inherited record cannot come back
  through fall-through, only by being written into the overlay again (a revival, at the
  same handle).
- **Handle sets.** `sentex-ids` / `justification-ids` / `premise-ids` are
  `base ∪ overlay − tombstoned`, with released premise marks subtracted from the last.
- **Durable bookkeeping.** The tombstone sets, the released marks and the cleared flag
  live in a small `KvBackend` beside the overlay, mirrored in atoms for the read path.
  Every mutation writes through and a mount rebuilds the atoms from it, so remounting a
  durable fork over the same base serves the merged view it was left in. An in-RAM fork
  gets an in-RAM one and pays nothing for the machinery.

**Counts need no delta bookkeeping.** A `RecordStore` exposes handle *sets*, not
counts, and everything counted — `sentex-count`, `context-size`, `count-with-functor` —
is read off the *index*, where the merge is the trie's copy-on-write counters and the
merged root sets. So a fork's counts are exact by construction rather than by a second,
parallel accounting that could drift from the records.

## The frozen mount

A base is any `RecordStore` + `KvBackend` wrapped by `vaelii.impl.overlay.frozen`, which
answers every read and **throws on every write**. Base immutability is thus structural: a
write path that forgot to divert fails loudly at the seam instead of silently mutating
what every other fork is reading. It is a decorator, not a file mode, so it says nothing
about how the underlying store was opened — which is what makes the composition safe
whatever the base is.

One call is deliberately not a refusal: `next-id` on the frozen record store. It hands out
a handle nobody holds and touches no stored record, and it is what the fork's id watermark
is seeded from; the alternative is a `max` over the base's whole live-id set at every
mount.

**It is the one thing a mount changes about the base**, and over a durable base the change
outlives the process. `next-id` advances the base store's monotonic counter, and the disk
record store persists that counter to `counters.nippy` on its next flush — so mounting a
fork over a `:disk` base bumps the base's stored sequence by one, permanently. The bump
allocates: it can only skip a handle, never reuse one, and recovery takes
`max(the counters blob, 1 + the highest slot id)`, so a skipped number costs nothing and
loses nothing. There is no read-only way to seed a watermark, and no arrangement under
which the counter both seeds a fork and stays where it was.

## Invariants

1. **Base immutability.** No overlay operation writes the base. `overlay_test` compares
   the base's records, premise marks and whole index before and after a fork asserts,
   derives, retracts and clears — byte-identical, including handles. The **id counter**
   is outside that comparison and is the one exception, above: mounting advances it by
   one, and on a durable base that lands in `counters.nippy`. No record, key, mark or
   handle assignment moves.
2. **A fork of nothing is the thing it forked.** The overlay `KvBackend` passes
   `kv_backend_test`'s adapter contract over an empty base, and
   `VAELII_TEST_BACKEND=overlay` runs the *whole suite* that way
   (`scripts/test-backends.sh`).
3. **Tombstones are sticky and durable.** A deleted inherited record or key stays deleted
   across a remount, rebuilt from the bookkeeping.
4. **Counts stay exact** under the frozen-base + copy-on-write-counter scheme, after adds,
   deletes and overrides alike.
5. **`reindex` and belief are unchanged** — the overlay is transparent to the index, TMS
   and query layers. That is the point.

## What this is not

This is the *storage substrate* for hypothetical reasoning, not the belief logic: an ATMS
tracks several environments inside one network, and nothing here does. It is also not a
distributed system, and not a way around the single writer: a durable base is locked by
the process that mounts it, and the forks that share it are the ones in that process's
heap. There is no coherence protocol either — a base that changes under a mounted fork is
outside the contract. Multi-level stacks (base → fork → fork) are refused rather than
half-supported, on both roads in: an `:overlay` half declared `:overlay` is an error
naming itself, and `core/fork`'s own `:base-stores` — which names no backend to catch —
is asked directly (`mount/forked?`), so `(fork (fork base))` throws `:stacked-fork`.

See also [storage.md](storage.md), [indexing.md](indexing.md),
[density.md](density.md).

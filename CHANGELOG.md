# Changelog

## 0.3.0 — 2026-08-04

Correctness fixes across the durable index, the snapshot, the JTMS, the export
dump and the bounded prover, a sweep that gives every refusal a `:type`, the one
wire contract 0.2.0's own sweep left qualified, and the serialization both
servers' storage layer already assumed. Then a run of **inference and belief**
work: two orders that reached two answers (a firing refused before it could
become a justification, and a definitional clash whose halves sat either side of
a `genlContext` edge), the two doors that disagreed about an inherited claim, and
two enumerations that grew with the vocabulary rather than with their own answer.
Eight entries are marked **Breaking** — they refuse input 0.2.0 accepted or
change an observable contract, which is why this is 0.3.0 and not 0.2.1; the rest
are compatible.

- **Breaking: the daemon's refusal `:type` keywords are plain** — `:not-edn`,
  `:cross-origin`, `:bad-host`, `:body-too-large`, where the namespace serving
  them qualified each one. This finishes tree-wide what 0.2.0's own breaking
  entry claimed, so a client discriminating on a `:type` matches on what went
  wrong rather than on where the code lives.
- **Breaking: both servers hold one request-body ceiling.** The cap and its
  `VAELII_MAX_BODY_BYTES` override (16 MiB by default) live in
  `vaelii.impl.guard`, which the daemon and the browser both read, so the
  browser answers **413** for an oversized form body where only the daemon did —
  a body 0.2.0's browser accepted, which is why this is breaking on the same
  grounds 0.2.0 marked the daemon's own cap so. A daemon read is also fully
  realized **inside** the write monitor — `wire-safe`'s walk is what realizes a
  lazy answer, so running it after the monitor released let a `:query` straddle a
  concurrent `:assert`.
- **Breaking: the browser serializes its writes.** Jetty serves the write routes
  on a thread pool, so two POSTs were two writers — where the storage layer is
  written on the promise that they are not: `disk/kv`'s `apply-ops!` folds
  against a map read outside its lock and publishes outside it too. Interleave
  two and the WAL holds both frames while the RAM map holds one, so the running
  index and the one replayed on the next open disagree. The browser now takes one
  process-wide monitor around every content write, as the daemon always did. A
  concurrent write waits rather than racing, which is observable as ordering.
- **Every `ex-info` the engine throws carries a `:type`.** Twenty refusals threw
  an untyped map, so a caller had to guess from which keys were present —
  `lookup`, `import!`, the catalog loader, the deferred join, the solver bridges,
  the disk codec and the token dictionary among them. Two forms that threw a raw
  Java exception now answer instead: `(genl ?x ?x)` / `(disjoint ?x ?x)` answer
  the question one variable in both positions asks — which members the relation
  holds of themselves — rather than raising `Duplicate key`.
- **Breaking: an `ist` form must have exactly three elements.** `(ist Ctx S)` is
  the form; 0.2.0 read `assert` and `check` positionally, so `(ist Ctx S junk)`
  asserted with the extra silently ignored and `(ist Ctx)` raised a raw
  `IndexOutOfBoundsException`. Both now refuse with `:type :shape`, the same
  problem `check` already reported.
- **The durable index is gated on its key layout at open.** `layout.edn` sits
  beside `format.edn` under `<dir>/index`, and a log whose stamp does not match
  `kv/index-layout-version` is cleared, rebuilt from the records and restamped,
  `:recover?` notwithstanding — an absent stamp over a populated log counts as
  stale, since that is what an index written before the sentinel looks like. The
  stamp lands only *after* the rebuild, and the directory is marked mid-rebuild
  *before* the clear, so a crash anywhere between the two reads as still-stale
  rather than as a fresh directory needing no work. The gate reads the index
  **kind**, so it fires on a durable index and never on a fork, whose inherited
  half is held to the sentinel by the `:base` refusal below.
  **A 0.2.0 durable store carries no stamp, so
  its first open under 0.3.0 pays one automatic reindex**: O(records), logged at
  `:warn` with the record count and the time it took, and paid once. Without the
  gate such a log replays cleanly and then misses every read whose key shape
  moved — populated-looking counts over queries that answer nothing.
- **Breaking: `open-kb` refuses a `:base` whose durable index is at an older key
  layout** (`:type :stale-index-layout`). A fork's base is held to the same
  sentinel as the fork's own half and gets the other answer: the repair is a
  write, and a base is mounted read-only, so the refusal names the one place the
  rebuild can happen — open that directory as a KB, then mount the fork over it.
- **Breaking: `(fork (fork base))` is refused** (`:type :stacked-fork`), which is
  what `docs/overlay.md` has always stated. `core/fork` passes `:base-stores`,
  which names no backend for the opts check to catch, so the stores are asked
  directly (`mount/forked?`).
- **Breaking: `open-kb` refuses a `:recover?` setting it does not name.** `:auto`
  is the default, `true` is accepted as an alias for it, and `:warn` and `false`
  are the rest of the roster; any other value read as the warn branch and handed
  back an empty TMS over a store that is not empty, which answers `[]` to
  everything. A **stale derived index** — one describing records that are gone —
  is dropped on open whatever `:recover?` says: `false` asks for silence about an
  unrecovered store, not for an index answering out of records nobody holds.
- **Breaking: `close!` releases a durable fork's own directory.** A fork's
  writable half takes the same exclusive lock and holds the same file handles as
  any durable KB, so without its own `:dir` it could never be handed to another
  process short of exiting the JVM. 0.2.0's docstring promised the opposite in as
  many words — `close!` on a fork was a no-op that kept its lock — so code that
  closed a fork in a `finally` and kept reading it worked and now does not. The
  base's directory stays unnamed here: it is mounted read-only and shared by
  every fork over it.
- **A failed compaction takes its temporary files with it.** A rewrite that threw
  — a full disk, a damaged frame — closed its handles and left `<log>.compact`
  behind, and `f/open-log` seeks to the end while `f/open-idx` does not truncate,
  so the *next* compaction in the same session opened that temp and appended to
  it. Its replay then put back records deleted in between. The cleanup is scoped
  to the pre-commit phase: past the marker the temps are the only complete copy,
  and the next open finishes the replay off the marker, which is what it is for.
  The record store and the KV index both take the three-handle open under a guard
  too, so a throw from the second or third no longer leaks the ones before it.
- **A failed open gives back the directory lock with no handles still on it.**
  `open-kv-backend` and `open-token-log` replayed their logs outside any guard, so
  an unrecognized op frame or a torn dictionary entry propagated to a caller that
  answers a failed open by releasing the lock — leaving it released while this JVM
  still held an open handle, the one state `close-dir!` exists to prevent.
- **A fork's merged `kv-entries` is realized under its monitor.** Both halves were
  lazy, so the seq handed back from inside the lock realized outside it, and every
  element it then produced called the merged-view reads the monitor exists to
  serialize. An export of a fork taken while anything wrote it projected two
  states at once. Same class as the daemon's `wire-safe` fix above.
- **The rete alpha registry is synchronized.** It is JVM-lifetime shared state
  reached from the store observer hooks, which fire on whichever thread is
  writing, and a `HashMap` racing its own rehash can leave a reader spinning on a
  probe loop that never terminates. Its check-then-put is one step now too, so two
  callers cannot each build an alpha and leave the loser's permanently unmaintained.
- **`load-source` claims the catalog under one monitor.** The busy test, the
  already-loaded test and the registration were three separate reads of the
  catalog state, so two requests arriving together each passed all three and
  spawned a loader — two background loaders writing the same stores, which is the
  case the guard exists to refuse.
- **The browser reads untrusted EDN under `Throwable`, as the daemon does.** A
  deeply nested form overflows the reader's stack with a `StackOverflowError`,
  which an `Exception` catch lets escape — a 500 where an unreadable term, line or
  textarea is the ordinary answer these three sites exist to give.
- **The index snapshot's roots-fallback blob is validated like the sections
  beside it.** `roots-fallback.nippy` carries the argument-root postings, which
  are primary index truth, and a missing or torn blob loaded as `[]` behind a
  warning while every argument-root read answered `#{}` out of a snapshot that
  opened clean. The meta records the blob's entry count and byte length, the
  decision checks the length exactly, and the load thaws strictly — a torn blob
  or a count mismatch throws into the rebuild path. The reloaded token dictionary
  is checked against the log by count, since the two sides key on different
  equality, and a mismatch rebuilds from the records rather than citing the wrong
  entry for every mapped edge.
- **The mapped index snapshot survives a JVM shutdown, and a failed save leaves
  the previous image intact.** The stamp is taken against the records before a
  byte moves, durability registrants close in phases, and every section lands in
  a `.tmp` until the swap — so a shutdown cannot close the records under `save!`
  and leave it having deleted the commit mark of the image it was writing. A
  failed *open* likewise gives back the handles it took: `open-kind`,
  `open-record-store`, the token log and the durability registration each undo
  their own opens, so a throw cannot outlive the directory lock that made the
  handles safe to hold.
- **An export dump carries every provenance stamp, and `export → import →
  export` is byte-stable.** The provenance walk covers justification handles as
  well as sentex ones, so a stamp `add-provenance` put on a justification is no
  longer dropped, and import remaps a justification's own handle to replay it.
  Import also stores a justification's antecedents as a **vector**, the shape the
  engine's own write path stores, so a round-tripped dump is byte-for-byte the
  dump it came from.
- **The JTMS dedup index carries the identity of the TMS it mirrors.** A nested
  chain over a second KB — legal from an `:on-progress` callback, and with
  overlapping handle spaces — could answer one KB's dedup question out of the
  other's supports. Every reader and both wholesale clears hand the map out only
  to that TMS, and anything else falls back to the reference scan. Keys coerce
  fixnum boxing to `Long` at the boundary, since the map compares with Java
  `equals` where the scan compares with `=`, and an `Integer`-boxed handle would
  silently split a key.
- **`prove-within` prepares its goal**, through the same `prepare-goal-for-read`
  every other read path takes, so a reifiable NAT or a merge-retired spelling is
  the same question under the bounded prover that it is under `ask`.
- **The rete forward matcher fans over predicate-`genl` sub-predicates at every
  arity**, as the reference `res/match-pattern` does. Fanning only for a
  two-element sentence gave the opt-in matcher a different belief set from the
  default engine's on any rule whose antecedent had another arity.
- **A firing refused at derive time comes back when its exception releases.**
  `place-conseq` does not place a firing whose `exceptWhen` exception or
  `(unknown S)` antecedent already holds, and such a firing left no
  justification, no node, and nothing in `jtms/blocked` — so a settle pass, which
  reads a release off the justifications that left the blocked set, could not see
  it, and the conclusion stayed suppressed after the block lifted. The same
  knowledge in the other order concluded it. The refusal is now recorded as
  `[rule handle, bindings]` in a per-KB record; a queued rule's entries are
  re-evaluated under the narrowing the placed firings already take, and a
  released one is re-derived from its own bindings rather than by re-joining the
  rule over the fact extent. The record is capped at 4096 entries per rule, past
  which the rule falls back to that re-join; `recover` rebuilds it by re-firing,
  and the two edge triggers that narrowed on a rule's *placed* firings ask their
  question of its refusals too. See `docs/exceptions.md`, "A refused firing is
  remembered as bindings".
- **Five order-independence repairs.** `contradictions` names the same side of a
  clash whatever order the two arrived in — `handle-naming`'s exact-match arm was
  a bare `ffirst` over matches that fan across the whole `genlContext` cone, and
  `asymmetry-problem`'s tie-break stopped at the context name; both order on
  content. The two settle sweeps that share one exposure-instance budget walk
  their moved region in content order, so which nogoods are minted past the
  budget does not depend on arrival order either. `query` with `{:proof? true
  :portfolio? true}` returns each answer once: `portfolio-solutions` dedups on
  the bindings rather than on the whole result map, so a solution two racers
  proved differently is one answer, as `core/query`'s contract says.
  `negation-nogoods` writes with a compare-and-set, so a `note-opposed!` landing
  between the read and the write is carried rather than dropped. And the node
  engine's inline join plans with the `:est-override` belonging to its registry
  leaf, the pair `prove-seq` is handed.
- **A forward rule fires on a claim argument-position preservation licenses**, so
  `sentexes-matching` and `ask` stop disagreeing about the same knowledge.
  `(argPreserving largerThan 1 genl)` beside `(largerThan dog cat)` licenses
  `(largerThan chihuahua maine_coon)`, which `ask` reached through
  `ArgPreservingProver` while the fixpoint fired only on the claims that were
  written — so the same rule over the same KB answered differently depending on
  which door the reader came in, and the conclusion it never drew had no `why`,
  no retraction path and no way to be an antecedent. The join now contributes
  the handles the inherited claim was **read from** — the claim that was stated,
  the declaration licensing the move, the reach edges, and `(transitive R)` for
  a fact-relation — so retracting any of them withdraws the conclusion and
  placement descends to the microtheory that can see them all. A more specific
  contrary claim withdraws a firing with nothing retracted, blocked and revived
  by the machinery `exceptWhen` already uses. Union, never replacement: a stored
  claim matches exactly as it did, and a KB declaring no preservation pays two
  set-cardinality reads per datum. One asymmetry is left and is narrower than
  the one this closes: the declaration is an antecedent of the firing, which is
  what makes retracting it withdraw the conclusion, and a justification confers
  the weakest class it rests on — so a `:monotonic` claim declared preserved by
  a `:default` declaration draws a `:default` conclusion, where `ask` answers
  without weighing either. Assert the declaration `:monotonic` if the derived
  conclusion should carry the claim's own strength. `docs/inherit.md`.
- **A head-existential rule carrying an aggregate mints a ground witness.**
  `skolem/frontier-vars` subtracts a post-join literal's output, so the Skolem
  NAT no longer takes a variable into its argument list. In the same pass,
  `matches-visible`'s cache key omits no retrieval-strategy var, so a
  differential oracle cannot compare a result against itself.
- **An open `disjoint` goal is enumerated from the declarations rather than from
  the vocabulary.** A separation convicts two subtrees, so the answers are the
  subtypes of what a *visible* declaration names
  (`taxonomy/separating-partners`, `taxonomy/separating-pairs`) and the cost is
  the answer's own size; 0.2.0 asked `taxonomy/disjoint?` once per type in the
  KB, and once per **pair** of types with both arguments open. On a KB of 4,000
  types carrying one separation that is 15.4 ms to 0.13 ms with an argument
  bound — flat in the type count where it grew linearly — and at 1,000 types the
  two-variable goal goes from 2.5 s to 4 ms. `lein perf`'s
  `disjoint-enumeration` check is the claim. Two answers arrive with it: the
  open goal binds a disjoint metatype's members even where they carry no `genl`
  edge, which is what the ground goal has always said of them, and the candidate
  set (the taxonomy's nodes plus the declared pairs) did not hold. The
  prover's `est-bindings` is sized off the declarations too, so a `disjoint`
  conjunct in a registry-planned join is costed at what it will yield.
- **A definitional clash is arbitrated from a context that can see both halves.**
  The checks are scoped to the context they are asked in, and `settle` asked each
  candidate's question from that sentex's own — so a pair whose halves sit either
  side of a `genlContext` edge was answerable from exactly one of the two, and
  only when that half was the one the settle moved. Known-true content in a
  general microtheory sat beside a default that denies it, in one arrival order
  and not the other. `settle/clash-askers` runs the check from the candidate's own
  context and from the maximal common descendant of it and each context holding a
  sentex the candidate could pair with; nothing is widened, since a vantage
  already sees both halves. Runs under the KB's `:arbitrate` policy, like the
  retroactive sweeps — under `:refuse` a pair neither writer could see stays the
  exposure pass's report.
- **A pair per opposing sentex, not per opposing type.** One sentence stated in a
  general microtheory and again in one that sees it is two sentexes, of possibly
  different strength, and a claim that denies it denies both.
  `checks/disjoint-problems` and the asymmetric arm named one handle each, so the
  content-first of the two was weighed and the other left believed beside content
  that contradicts it; `functional-problems` counted its clashes per sentex all
  along. The asymmetric arm reads the stored converses beside `inherit/surviving`,
  which answers one claim per tuple by design. `clash_oracle_test` covers the
  cross-context pair rather than excluding it, and is what found both.

## 0.2.0 — 2026-08-03

**Not a drop-in upgrade from 0.1.0.** Several of the changes below refuse input
0.1.0 accepted or change an observable contract — each such entry is marked
**Breaking** — which is why this is 0.2.0 and not 0.1.1. Entries between here and
the 0.1.0 header are in it, newest first.

- **The argument roots are scoped by predicate** (`[:argument-root pred pos
  term]`), so a materialising join reads one literal's postings rather than
  wading through every functor's at a shared slot. An `[:argument-slot pos
  term]` roster, reference-counted off those postings, keeps the
  predicate-agnostic reads answerable as a union over the predicates present.
  The packed long has no room for a fourth key part, so the dense roots route
  the family to their boxed fallback. `index-layout-version` is **2**: an index
  written by 0.1.0 reads as `:layout-changed` and is rebuilt on first open —
  no action needed, but a large durable store pays a reindex for it.
- **Breaking: every handle-taking fn refuses a non-handle** (`:bad-handle`) —
  the vector `assert` returns for a conjunctive rule included, which 0.1.0's
  `retract!` silently answered with `{:removed-sentexes 0}`. `nil` stays a
  question with an answer (`in?` false, `why` `{:stored? false}`,
  `add-provenance` a no-op), and `check-edit` reports what `edit` throws. `why`
  also takes `{:max-depth n}` (default 256), marks a capped branch
  `{:truncated? true}` instead of overflowing, and refuses bad opts
  (`:unknown-option`).
- **`close!` releases a durable KB's directory** without waiting for JVM exit,
  and `import!` is `export!`'s inverse. An unclean close still releases the
  lock and registry; the first component failure is rethrown after.
- **An `argIsa` / `interArgIsa` / `argGenl` refusal names its convicting
  declaration in content order**, not in whichever order retrieval enumerated.
- **The five sweeps run in CI** — dense TMS, incremental matcher, node query
  engine, its tacticians, reference retrieval — each failing-set-identical
  with the default it replaces. Nothing ran them before.
- **Breaking: `assert` refuses a non-map `opts`** (`:unknown-option`) —
  `(assert kb s ctx :monotonic)` stored a defeasible sentence in 0.1.0.
  `check` already reported the same request; the two agree now.
- **Breaking: `open-kb` recovers by default** (`:recover? :auto`). The old
  `:warn` default handed back a KB that answered wrongly from a reopened
  store. The cost moves to construction — O(records) on a populated store —
  and `{:recover? false}` defers it. `:warn` and `false` remain.
- **The public surface is six namespaces**, where it was one: `vaelii.core`
  plus thin shims `vaelii.client`, `vaelii.starter`, `vaelii.web`,
  `vaelii.serve` and `vaelii.cli` over the `impl` namespaces they front. The
  boundary is now what the docs said it was.
- **Breaking: `vaelii.client`'s `assert` and `assert-rule` are spelled bare**,
  without the `!` 0.1.0 gave them. A `!` marks a fn that destroys stored
  knowledge and neither does — both are additive, and `retract!` is what takes
  one back — so the client now spells them exactly as `vaelii.core` does. A call
  site writing `c/assert!` or `c/assert-rule!` no longer resolves.
- **A clash names the sentex that states the membership**, not one that merely
  entails it, under either retrieval strategy.
- **An auto-compaction queued for a closed store is dropped**, so the next
  open no longer replays it as a crash-interrupted compaction.
- **Breaking: error `:type` keywords are plain across the tree**
  (`:unknown-source`, not `:vaelii.impl.catalog/unknown-source`), and
  `open-kb`'s backend refusals carry one. Swept in the same pass: the settle
  re-check queue no longer drops entries queued by a concurrent thread, and
  `foreign/register` refuses with `ex-info` rather than an elidable `{:pre}`.
- **Leiningen 2.10 is the minimum**: `:preserve-eval-meta` needs it, and 2.9
  ignores the key silently.
- **Breaking: `POST /op` requires `Content-Type: application/edn`.** The type
  is not CORS-simple, so a browser must preflight and the daemon answers no
  CORS headers — which closes cross-site request forgery against a loopback
  daemon. A client that sent no content-type is refused; add the header.
- **Breaking: a request body over 16 MiB is refused** (413) before it reaches
  the heap; `VAELII_MAX_BODY_BYTES` adjusts the cap.
- **Breaking: DNS rebinding is closed on both servers.** Every route requires
  a `Host` naming the interface the server was started on. A request with no
  `Host` still passes (a non-browser client carries no ambient browser
  context); a reverse proxy or local alias sets `VAELII_ALLOWED_HOSTS`.
- **`+with-foreign` names a coordinate that exists**
  (`com.vaelii/vaelii-foreign`); the bare id it carried resolved nothing.

## 0.1.0 — 2026-07-31

The first release. What follows is the development log that produced it, newest
first; every entry below is in 0.1.0.

## 2026-07-30

- A declaration re-checks the exceptions it moves: `(symmetric P)`,
  `(transitive P)`, `(inverse P Q)` and the `argPreserving` forms change what
  may be concluded with no fact arriving; `(functional P)` sweeps the extent
  when it lands.
- An equality restates a fact for each reader rather than once for the KB, and
  is itself a re-check trigger for `exceptWhen`, `unknown` and census reads.
- A change feed: the region a settle already computes is handed to a listener
  instead of discarded.
- English in — a sentence read into candidates a person still has to accept.
- A qualitative relation two microtheories entail together fires a forward
  rule; a believed negative reaches the wiring a positive does; "some context"
  means the union of what the readers answer.
- Three readers of one question agree over a cyclic hierarchy, and settle
  repairs the context ranking after reconciling belief as well as before it.

## 2026-07-29

- One front door for backward chaining: the four paths measured, then
  consolidated to two chainers behind one entry point with one dial. A proof
  of an ephemeral answer reads the way `why` does.
- The goal frontier's order is a policy measured on time-to-first-answer,
  `:ground-first` by default; the goal-stack chainer drives one solution at a
  time and level 7 streams its search.
- Foreign formats arrive as a classpath plugin, so a reader ships and retires
  without touching the engine.
- A constraint declaration may name a second sentex it must not weigh, and a
  depth bound has no default because there is no defensible one.

## 2026-07-28

- `lein gate`: lint, the suite, and the scaling claims, measured and failed on
  rather than asserted; five checks added for costs that grow with what they
  must not.
- The columnar index is written once and mapped back; backend names read
  `<records>-<index>`, all seven.
- A literal's matches are remembered and retired on a clock; converging
  branches share one rule expansion; a third backward chainer whose state is
  a frontier.
- The naming invariants belong to the knowledge base, and the bulk door counts
  what it skips.

## 2026-07-27

- Aggregation: a count is a query operator, and a firing that rests on one is
  maintained like any other — gated by a permutation test. A census counts
  distinctness through the representative the asking context elects.
- `argIsa` entails as well as constrains, behind a toggle, retroactively too.
- A definitional clash names a second sentex, making it a nogood, and the
  arbitrating sweep asks the taxonomy rather than a fixed functor set.
- The qualitative network lives on the knowledge base and warm-starts off its
  own previous answer; a violation ledger is a claim about one KB.
- The browser draws term shapes, composes English at three densities, and
  gained `lein browser`; OpenCyc loading went from 378s to 277s.

## 2026-07-26

- Contexts got a vantage: every taxonomy supporter records the context it
  asserts from, so disjointness, matching fan-out and settle all read only
  what the asking context can see.
- A firing names the `genl` edges it subsumed through — belief and strength
  run through them like any antecedent, checked against all 24 orderings.
- Records and index became two independent choices, plus an overlay backend:
  a private writable fork over a shared read-only base.
- A knowledge base is readable before it finishes loading, and the suite runs
  on every backend from one script.

## 2026-07-25

- OpenCyc, read and re-expressed: every constant given back its role, 1.1M
  sentexes in the engine's own format, on the machine that reads it. Nothing
  of Cycorp's is redistributed.
- An export format no rename can break, with `xz`, an importer, and an oracle
  comparing two knowledge bases; a dump lands every record at its handle.
- Qualitative spatial and temporal reasoning: RCC-8 and three more spatial
  algebras, Allen intervals, durations and instants, behind one glue.
- One gap written in two units is one constraint: both spellings snap to the
  tolerance grid, and a unit given two conversion factors is its own base.
- A knowledge-base catalog with a browser that switches between KBs;
  `inherit` declared rather than assumed; definitional checks reach every
  term; `argGenl` constrains one level up.

## 2026-07-24

- The scale program opened with measurement first: the truth-maintenance
  wall, a posting-encoding bake-off on a real corpus, and a rule audit.
- Three dense representations, each measured: `:memory-dense` integer
  postings, the `:memory-columnar` int-token trie with CSR compaction (3.18x
  whole-index), and a bitmapped TMS behind a protocol.
- The disk side got dense too: positional record reads with a hot-record LRU,
  a positional frame codec, tokenized bodies over a durable dictionary — all
  behind a backend parity gate.
- Recursive forward chaining went O(n³) → O(n log n); a term roster
  enumerates vocabulary in O(terms).
- The web browser was hardened — escape by default, guard the parse, bind
  loopback, refuse cross-origin writes — and a pluggable LLM proposes edits
  and never applies them.

## 2026-07-23

- A performance review, its findings fixed: the disk log records operations
  rather than grown values (killing an O(N²) write amplification), settle
  keeps a coincidence set, re-checks narrow to the moved cone, region
  fixpoints became semi-naive worklists, compaction is copy-on-write.
- Symbolic equational reasoning: pure oriented rewriting with full
  Knuth-Bendix orientation, order-independent normalization, and
  non-confluence surfaced; `rewriteOf` extended over predicates and types.
- An operational surface: an EDN-over-HTTP daemon, a command-line driver, a
  thin client, and a browser that attaches to a daemon — with the public API
  closing every hole the browser tracked.
- Existential rule heads with deterministic skolemization; an occurs check;
  closures answered on demand; the record split into atomic and rule shapes
  with interned symbols; a bulk-load fast path.

## 2026-07-22

- Negation as failure, at top level and in antecedents, with block, sweep and
  revive, and stratification to keep it sound.
- Resource-bounded anytime inference with qualitative cost tiers and a
  cost-ordered forward-chain join; `ask-within` normalizes its goal.
- Reification of non-atomic terms; structural subterm indexing,
  oracle-proven, then on by default.
- The storage seam: index logic onto one key-value protocol, an in-memory
  backend, then the on-disk substrate — files, lock, durability, record
  store, index store.
- The index benchmark harness, and a per-handle provenance side map.

## 2026-07-21

- `exceptWhen` canonicalized into the record, blocking excepted conclusions
  with only reachable firings re-checked; its query reified the way a fact
  is.
- Equality landed: the closure, the `different` prover, a specification
  suite, and wiring into assert; stratification is checked on edge change.
- The engine split out of one namespace into five, and the knowledge base
  restructured into a layered tree loaded on start.
- `assumptionRules` with persistent solve and labeling contexts, proven on a
  sudoku.
- Retrieval got sharper: argument roots, multi-column narrowing, predicate
  subsumption, set-algebra retrieval, an opt-in incremental matcher.
- Truth-maintenance mutations are atomic; lint arrived.

## 2026-07-20

- Canonical rule form — canonical variables with a varmap, literal order,
  comparison direction — so rules alike up to renaming share one handle.
- The eight-level lookup-to-query stack, lazy throughout, with a browser page
  showing which level answered.
- Order independence and locality pinned as invariants: region-local
  relabelling, belief-following closures, content-keyed tie-breaks.
- The answer-set layer wired to the edge-solver seam, with a labeling
  materialized as a context; the defeasible layer made sound, six bugs
  pinned as failing tests first; `exceptWhen` began as a failing suite.
- Everything but `core` moved under `vaelii.impl.*`; `!` reserved for
  irreversible operations; tests became net-neutral, and a second concurrent
  run fails fast rather than corrupting the first.

## 2026-07-19

The first day: a contextualized common-sense knowledge base with a trie
index, inference and truth maintenance.

- Sentexes — a sentence plus the context it holds in — stored as records
  behind protocols with nippy serialization; rules are sentexes too, with
  built-in transitivity for types and contexts.
- Forward chaining with dependency-directed retraction, and a backward
  chainer; a non-monotonic TMS with strengths, soft prioritized
  contradictions, and a solver seam.
- An inverted term index, directed rules, disjointness, well-formedness
  checks, and a pluggable prover query engine; structural connectives
  canonicalize into the record; evaluable arithmetic.
- A web browser over the whole thing, over a starter ontology with every
  term documented.

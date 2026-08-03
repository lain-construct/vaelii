# The KB catalog

`vaelii.impl.catalog`. Everything else in this repo assumes it is holding *the* KB. The
catalog is what makes that a choice: it lists the knowledge bases this process could
load, loads one in the background while the pages keep answering, and says which of the
loaded ones every other page is about.

Three parts, in the order a KB moves through them:

    a source          a KB you could load, as data      catalog/sources
      │  load-source  on its own thread, cancellable
      ▼
    an entry          a KB you have loaded              catalog/entries
      │  activate
      ▼
    the active KB     what every page reads             catalog/holder

## Sources

A source is a description, not a KB. Six kinds:

| kind | content | loader |
|------|---------|--------|
| `:core` | the CoreContext vocabulary head alone | `vaelii.impl.core-context` |
| `:starter` | the shipped schema-only ontology | `vaelii.impl.starter` |
| `:generated` | synthesized from numbers — see [generating one](#generating-a-kb) | `vaelii.impl.io.generate` |
| `:corpus` | a translated sentence corpus (OpenCyc) | a plugin's reader — [foreign.md](foreign.md) |
| `:dump` | a vaelii export dump, with or without its index | `vaelii.impl.io.import` |
| `:store` | an on-disk KB already in vaelii's own format | opened in place |

The first three ship here and are always offered. The last three are **found**, never
hardcoded: every directory on the search path is probed, and the marker its writer left
decides what it is — a corpus `meta.edn` carries the context order it was written in, a
dump's carries a `:format-version`, a vaelii `:disk` store is a `records/` + `index/`
pair. Anything else is not a KB and is passed over, including a directory whose
`meta.edn` does not read as EDN.

What it takes to *have* each of these — which ship here, which needs a plugin, which you
supply, and what each costs to get to a first load — is [kbs.md](kbs.md).

```
VAELII_KB_PATH=/kbs:/data/corpora    # colon-separated; each entry is a KB directory or
                                      # a directory of them, probed one level down
```

With no `VAELII_KB_PATH`, the `vaelii.kb.path` system property is consulted (the same
shape, and what a test sets — a JVM cannot change its own environment), and failing that
`./kbs` and `~/.vaelii/kbs`.

A KB **outside** the search path is named in a catalog file — `VAELII_KB_CATALOG`, the
`vaelii.kb.catalog` property, or `~/.vaelii/catalog.edn` — a vector of maps, each with a
`:path` and whatever it wants to override about what is found there:

```clojure
[{:id "alpha" :name "Vaelii alpha (full)"  :path "/kbs/alpha-export"}
 {:id "cyc"   :name "OpenCyc 4.0"          :path "/kbs/opencyc-4.0"}]
```

That file is the **only** place a machine's own paths live. Nothing about them is in the
repo, and `sources` is recomputed per call — dropping a corpus into a search-path
directory makes it appear on the next page load, with no restart.

Every source carries its own `:options`: the form controls it accepts, as data. The
generator's sliders are `vaelii.impl.io.generate/knobs` rendered directly, so the page
and the generator cannot disagree about a parameter's range or its default.

One of those options is worth naming here because its cost is easy to under-read. A dump's
`:belief?` (and a store's `:recover?`) governs **two** derived structures, not one: the
JTMS *and* the cached `genl` / `genlContext` closures. Left off, the KB is findable by
term and countable but has no type hierarchy at all — `types` and `contexts` come back
empty and the ontology page has nothing to draw. On a 1.2M-sentex OpenCyc dump that is
the difference between 0 and 125,385 types. (Exact counts move with the import profile
and the plugin version — [kbs.md](kbs.md) reports 132,391 types for the `:ontology`
profile it measures. The figure to read here is 0 versus six figures.) Off is still the right default for a corpus
past what `recover` can do in reasonable time, which is why it is a switch rather than a
decision the catalog makes.

## Loading

`load-source` registers the entry, starts a thread, and returns immediately. **One load
runs at a time** — they are minutes long and memory-hungry, and two at once would make
each other's timings meaningless and each other's memory unpredictable.

Progress comes back through the loaders' own `:on-progress` seam, which each of the three
long loaders takes:

| loader | phases | total |
|--------|--------|-------|
| `io.generate/load-into` | vocabulary → contexts → types → individuals → rules → facts → chaining | exact, except chaining |
| a corpus reader's `load-dir!` | topology → hierarchy → schema → memberships → facts | from the corpus's `report.edn` |
| `io.import/import-dump` | sentexes → justifications → index-entries *or* reindex | from the dump's `meta.edn` |

A load with a total gets a real percentage; one without gets a count and an indeterminate
bar, which is the honest rendering of not knowing how far there is to go. **Chaining is a
phase of the second kind even in a load whose assert phases are counted exactly**: a
fixpoint's agenda grows as it derives, so there is no total to count towards, and what it
reports instead is what it has concluded and how much agenda is left.

**Cancelling is that same callback throwing.** A loader is a tight assert loop with no
other point at which stopping is safe, so `cancel!` sets a flag the next progress report
reads and throws on. What had already landed stays landed — none of the loaders is a
transaction — and the entry keeps its KB so `unload!` can still release it.

That also means a phase reporting **no** progress cannot be cancelled while it runs, and
one still does: opening a large on-disk store, whose record log is scanned before anything
is said. Nothing is released while a loader is still running — `unload!` says the entry is
*still stopping* rather than clearing stores out from under a live writer.

**Forward chaining reports through the same seam** (`chain`'s own `:on-progress`), which
took a second reporting point to be worth anything: the agenda loop sees a run only
*between* datums, and the rule datum that joins over a whole corpus is one datum that can
hold the loop for a minute. So a firing reports too, and the
interval is wall-clock — about four reports a second — rather than a datum count, since
datum cost spans microseconds to minutes. A single *unproductive* join is the stretch that
still says nothing, bounded by the extent it scans. An aborted fixpoint leaves the
conclusions it had already placed, like every other cancelled phase.

Bounds are still what keep a chained load finite rather than merely interruptible: the
generator bounds cascade depth at its own layer count and passes the engine's
`:max-derivations` backstop, which the UI exposes as the derivation cap (a run overshoots
it by the last datum's fan-out, since the bound is checked between datums). A corpus has
no layer count to bound a cascade by, so there the cap is the *whole* bound — which is
why the corpus card carries one of its own.

**A chained load chains once, at the end.** Every loader asserts with `:chain? false` and
the pass runs after it, which is what the option says and the only shape that pays: firing
rules against a KB whose rules are half loaded costs more and reaches the same fixpoint.
It is also the only arrangement that can be *reported*, since a pass has a phase and a
per-assertion cascade has nowhere to say anything. Chaining is off by default, and the
cards that offer it are the two shipped ontologies, the generator and a corpus — a dump
and a store rebuild belief instead (`:belief?` / `:recover?`), which is a different
question from deriving what the rules conclude.

The KB an entry loads into is in memory by default, over a space pair the catalog claims
(from 100 up, clear of the block the test suite owns). Name a `:dir` and it is a durable
`:disk` KB there instead — which is what a corpus far past what RAM holds wants.

## Unloading never deletes an on-disk KB

This is the property to keep:

* a **memory-backed** entry has its stores cleared. They are keyed by space number and
  would otherwise hold the corpus for the life of the JVM.
* a **disk-backed** one is *closed*: the file lock released, the directory left exactly
  as it was. The same directory can then be loaded again, or opened by another process.

So the `!` in `unload!` is about the memory case, which does destroy something. Unloading
an attached daemon, or a KB registered by a caller that owns it, releases nothing at all.

Unloading the active entry falls back to the most recent one still loaded, so the browser
is never left pointing at nothing while a KB is sitting right there.

## And back out again

`export-entry!` writes a loaded KB out as an export dump,
on the same discipline a load runs on: its own thread, progress recorded where the page
already looks for it, and cancellation by the progress callback throwing — which
`export!` calls at each chunk boundary, the only point at which stopping leaves a
directory rather than a file half-written.

It is deliberately **not** an entry. An export produces no KB, and filing it as one would
put a second handle on a KB somebody could then unload out from under the writer. One
slot holds the running job and, after it, the last report — which is what lets the panel
say where the dump went.

That closes the loop. `classify` keys on `meta.edn` and `export!` writes it **last**, so
the moment a dump lands under the search path it is a `:dump` source, and export-then-reload
is two clicks that never leave the browser. The same ordering is what keeps a **partial**
dump out: a cancelled or failed export leaves a directory with no `meta.edn`, which
`classify` does not recognise and `sources` does not offer.

Three refusals, each about something an export cannot be correct in the face of:

* **another export is running.** One at a time. A *load* is not refused and does not
  refuse this — a load fills some other KB, and blocking on one would be a rule about
  this process's busyness rather than about the dump.
* **the entry is not an in-process KB.** A daemon serves its KB from another host, and
  that is where its dump would be written — so the export belongs to the daemon's own
  surface, not to a form here naming a path on the wrong machine.
* **the KB is still loading** (`write-blocked?`). `export!` walks it record by record
  with no snapshot to walk instead, so a dump of a KB something is still writing is a
  dump of no single state.

The `!` in `export-entry!` / `cancel-export!` is for what a stopped one leaves behind: a
directory holding part of a dump. Not a *loadable* dump — but bytes on disk that nothing
here will clean up.

## What it costs to hold

Loading a corpus is mostly a memory decision, so the catalog answers two questions of
different kinds and keeps them visibly apart.

`heap` is a **measurement** — `{:used :committed :max}` off the memory MX bean — and it
belongs to the whole JVM: every loaded KB, the browser itself, and whatever garbage has
not been collected yet, in one figure that cannot be attributed to anybody. `:used` drifts
up between collections and drops without anything being freed, so it is the shape of a
curve rather than a number to subtract KBs from.

`footprint` is an **estimate** for one KB, and the only per-KB answer there is: the
alternative is to unload it and diff the heap, which is not something a page may do to a
KB somebody is reading. It multiplies the stored sentex count — one O(1) trie read, so
this is cheap enough to run on a page that polls — by what a sentex measured per resident
component (`resident-bytes-per-sentex`, from the `lein bench-scale` sizing runs):
~1,549 B of index, ~279 B of records, ~467 B of truth-maintenance network. Two adjustments make it about *this* KB: a `:disk` KB
pages its records, so that term drops (what stays resident is the bounded hot-record LRU,
which does not grow with the corpus), and a KB loaded without belief — an import with
`:belief? false`, a store opened without `:recover?` — has no network, so that term drops
too.

The error term is **sentence shape**: a lean arity-2 fact indexes at the coefficient
above, a rich one with compound arguments measured ~2,158 B. The leaner figure is used, so
a corpus of fat sentences reads low. `predicted-footprint` puts a source's own count of
what it holds through the same coefficients — what loading it *would* cost, which is the
number that decides whether to load it at all.

## The switch

`holder` is a deref-able that yields the active KB (or a fallback when nothing is
loaded). `vaelii.impl.web/app` takes one of those in place of a KB and resolves it **per
request**, so activating another entry re-points every page at once with no restart and
no handler rebuild. A KB or an access value still works — `app` takes any of the three.

Anything **holding a KB** can be activated, a load still running included. The only
refusal is an entry with no KB yet, and that is a statement about there being nothing to
read rather than about the load.

A half-loaded KB answers about what has landed, which is a *prefix* and not a wrong
answer — the ordinary open-world condition this engine is built on, where an absent fact
never means a false one. Reading beside the loader is sound for the same reason a reader
thread beside the writer is: one writer, and every store mutation lands atomically
([storage.md](storage.md), the single-writer contract). So what a reader is owed is being
*told*, not being refused.

`active-caveat` is what tells them — nil when the active KB is finished and believed,
otherwise the two things that can be less than the whole truth, reported separately
because they are independent:

* the load is **still running** (or stopped part-way), so what is stored is a prefix of
  what was asked for;
* **belief and the taxonomy are not built** — `recover` builds them together and
  `:belief? false` skips them together. That empties more than queries: with no JTMS
  every believed answer is empty, and with no genl/genlContext closures there is no type
  hierarchy either, so a fully stored KB renders as one holding no types and no contexts
  at all.

The second is the one that matters most, because it **outlives** the first. A store
opened without `:recover?` is `:ready` and stays that way, and so does a dump imported
with `:belief? false` — the dangerous case is the one that looks finished. The browser
puts both at the top of every page ([web.md](web.md)).

What activating a half-loaded KB costs is exactly one thing: **the right to change it.**
`write-blocked?` says so — the loader is already this process's writer, and two
interleaved writers are not serializable, so the reads stay open and the writes wait. It
is asked of a *KB*, by identity, rather than of whichever entry is active: a second KB
loading in the background is no reason to stop writing to the one on screen, and a caller
holding a KB the catalog never heard of is nobody's loader's business.

This is what makes fast open worth having twice over. A `:store` that opens in seconds is
browsable while `recover` rebuilds belief behind it, and a corpus is browsable from its
first thousand sentexes — the wait stops being a wait.

## Generating a KB

`vaelii.impl.io.generate` synthesizes a KB from a handful of numbers — types,
individuals, predicates, facts, rules, the forward/backward mix, how many are defeasible,
how deep the type tree branches, how many contexts the facts spread over, and the seed.

Two properties make it a measurement rather than noise:

* **Deterministic.** Everything is drawn from one seeded `java.util.Random` in a fixed
  order, so the same parameters give the same KB. `plan` is pure — the whole KB as data,
  nothing asserted — and `load-into` asserts it.
* **Stratified.** Predicates are split into layers; facts populate layer 0, and a rule
  concluding a layer-*k* predicate draws its antecedents only from below *k*. The rule set
  is acyclic, so forward chaining cascades base → derived → further-derived and
  terminates. The chain is additionally bounded at `layers + 1`, since a derivation over
  this rule set cannot legitimately go deeper: anything that does is a join fanning out
  over itself, and the bound turns that into a *truncated* run rather than one that does
  not come back.

Individuals and predicates are Zipf-sampled, so the corpus has hot terms and a long tail
like a real one. Generated names carry their role in their spelling, as the naming
invariants require: `gen_type_7`, `GenInd42`, `genRel3`, `GenBand0Context`.

The fact contexts are a **chain**, not a fan of siblings. Two incomparable microtheories
have no common descendant, so a rule joining a fact from each would complete with nowhere
to put its conclusion (`:no-placement`, in `violations`). Down a chain every pair is
comparable and the conclusion lands in the deeper of the two.

## What this is not

The catalog is **process-local**: it is the browser's own state, not a KB's, so nothing
about it is stored, nothing survives a restart, and the daemon (`vaelii.impl.serve`) does
not serve it. A browser started with `--attach` registers the daemon as an entry it reads
and can load local KBs beside it, but it cannot make the daemon load anything.

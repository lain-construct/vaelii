# Adding a predicate the engine interprets

- **Covers:** the declaration every term of the engine's own grammar carries in
  `vaelii.impl.predicates` — its nine fields and the five closed vocabularies they are
  written from — how it is joined to the arms in `vaelii.impl.special`, which rosters
  derive from it, what is refused at namespace load, and what a new interpreted term owes.
- **Not here:** adding an ordinary domain predicate, which is a KB edit and no code at all
  → [naming.md](naming.md), [taxonomy.md](taxonomy.md), [argtypes.md](argtypes.md); what
  any one existing declaration *does* → the subsystem page that owns it; the public
  functions that read the answer back → [api.md](api.md).
- **Assumes:** predicate, sentex, context, handle, belief, taxonomy prop, `genl` →
  [glossary.md](glossary.md).

## Most new predicates need no code

A domain predicate is knowledge, not machinery. `marriedTo` is added by writing it down:

```
(comment marriedTo "Spouse of, as a civil or religious status. Symmetric, and holding at a time rather than forever.")
(binary_predicate marriedTo)
(arg marriedTo 1 person)
(arg marriedTo 2 person)
(symmetric marriedTo)
```

Every line there is a sentex like any other — asserted, indexed, believed, retractable.
Nothing in `src/` mentions `marriedTo`, and nothing has to: the predicate is *described*
using declarations the engine already interprets, and `symmetric` is doing the work. That
is the normal case and the rest of this page does not apply to it.

The question that sends you further is narrow:

> **Does a code path have to run when a sentex with this functor is asserted, retracted or
> recovered?**

If a new term maintains a cache, or refuses a malformed sentence at the door, or is
answered by a prover rather than stored, then the engine reads the *functor itself* and
the term has to be declared. `symmetric` is such a term. `marriedTo` is not, and the
distance between them is the whole subject below.

## One term, one entry

An interpreted predicate is a fact about a functor that nine different namespaces each
need a piece of, and the twenty-odd rosters keyed on functor names are all projections of
it. `vaelii.impl.predicates` is where the fact is written once; a roster that reads the
entry is a **view**, not a second copy, and cannot drift from it.

Five namespaces read it today — `special`, `taxonomy`, `settle`, `spec` and `vocabulary`,
enumerated below, and a roster one of them owns can itself be a view read once more
(`provers/transitive-predicates` *is* `taxonomy/closure-relations`). The rest still hold
their own list: `checks`' four, `provers/evaluable-predicates`, `sentex`'s three
(`sentex/aggregate-functors`, `sentex/rule-direction-wrappers`,
`sentex/default-rule-wrapper`), `kb/equality-predicates` and `inherit/declarations`. A term
that belongs in one of those is enrolled there by hand, and that is the part of adding a
predicate this structure does not do for you.

The namespace requires nothing but `clojure.*`, which is not an accident. The arms need
functions from four layers — `taxonomy`, `wff`, `checks`, `settle` — so a namespace
holding data *and* arms could only ever sit at the top of the stack, where `taxonomy` and
`wff` cannot reach it. Splitting them puts the data at the bottom, where everyone can
([defenses.md](defenses.md#what-a-term-says-lives-below-what-the-engine-does-about-it)):

```
predicates  ←  taxonomy  ←  wff  ←  checks  ←  special  ←  settle  ←  vocabulary
```

`entries` is a **vector**, not a map, because the order is content: `special/entries` is
that order filtered, and `special/rebuild-taxonomy` replays it top to bottom with a
rebuild arm allowed to read what an earlier one wrote.

## The declaration record

Nine fields. Six are structure the engine dispatches on; three are prose — one finding,
and the two exclusive answers to *does anything read this*.

| Field | Says |
|---|---|
| `:shape` | how the term is written as a sentence — `{:args [kind …]}`, optionally `:optional [kind …]` for a trailing argument that may be omitted or `:variadic kind` for an open tail. Arity is `(count :args)`. `nil` for a term that is never a sentence functor (a collection: `string`, `thing`, `binary_predicate`) |
| `:storage` | `[kind target]` — which of a closed set of storage shapes the declaration is cached under, and which table it lands in. `[:none]` for a term nothing caches |
| `:checked` | does `special/entries` give the functor a structural well-formedness arm |
| `:facets` | a set from the closed `facets` vocabulary — the lanes the term takes part in |
| `:family` | the family whose spellings must move together, or `nil` |
| `:sweeps` | what this declaration *arriving after* the content it constrains puts back in question, or absent |
| `:notes` | prose, only where the term does something the facet vocabulary has no word for. A note is a **finding**, not a description |
| `:enforced` | prose naming the code path that reads the term — what `interpreted` hands a KB author who asks whether a declaration does anything |
| `:inert` | prose recording that nothing reads the term **and that this is a decision**. Written by the `inert` constructor, which sets the facet with it, so the class is never a second opinion about the facets |

`:enforced` and `:inert` are exclusive and the constructor is what makes them so — an entry
cannot claim a lane and be classified inert, because claiming a lane means carrying a facet
and `inert` replaces the facet set outright. The **class** is read off `:facets`, never off
which key the prose was written under.

Entries are written through constructors — `prop`, `mark`, `pair`, `wff-only`, `operator`,
`collection`, `structural` — for the same reason the vocabularies below are closed: an entry
a couple of parameters *construct* has no way for its fields to disagree with each other,
and the twenty-eight predicate marks differ in exactly one keyword. `symmetric`'s entry is
the whole of what the engine is told about it:

```clojure
['symmetric (enforced (prop :symmetric)
                      (str "taxonomy prop :symmetric — canonical argument order, so both"
                           " spellings are one sentex; also a binary_predicate type"))]
```

`prop` fills in the rest: the sentence shape `(symmetric P)` with argument 1 a predicate,
`[:prop :symmetric]` storage, `:checked true`, and `#{:cached :derived}` — the `:derived`
facet because a mark that arrives by *derivation* has to install like an asserted one, or a
restart changes the answer. A mark that also convicts stored content says so and says what
it sweeps:

```clojure
['asymmetric (enforced (prop :asymmetric :facets #{:reach :convicts :arbitrable}
                             :sweeps :predicate-marked)
                       "checks/asymmetry-problem — a nogood against the converse; also a binary_predicate type")]
```

## The five closed vocabularies

Closed on purpose. Growing one is a single commit that adds the keyword *and* the rule
governing it, so a keyword can never come to mean whatever its first user assumed.

| Vocabulary | Members | What a member commits you to |
|---|---|---|
| `argument-kinds` | `:predicate` `:relation` `:relation-name` `:type` `:context` `:function` `:position` `:integer` `:term` `:sentence` | a kind here is one a well-formedness arm can be **generated** from; a position no kind fits is a position whose check stays hand-written |
| `storage-kinds` | `:prop` `:mark` `:edge` `:keyed-pair` `:pred-position` `:none` | each names what the add / drop / rebuild triple looks like. `:prop` means the `tax/props` roster specifically, whose keys `spec/::prop-kind` pins — a one-term mark into a table of its own is `:mark`, not `:prop` |
| `facets` | `:cached` `:derived` `:migrates` `:arbitrable` `:reach` `:query-only` `:answers` `:retriggers` `:convicts` `:inert` | the lanes that read the term. Six are reconstructible from a live data structure and are pinned that way; `:answers`, `:retriggers`, `:convicts` and `:inert` are *claims*, which is exactly why they are the ones that go wrong quietly |
| `sweep-kinds` | `:type-separating` `:predicate-marked` `:both` | carrying one **is** being a clash declaration, so `settle`'s exposure pass has an arm for it. Absent is the answer for a term whose retroactive half is a different mechanism |
| `mark-families` | `:functional` `:argument-constraint` | a family lives in more than one lane. Naming it once is what makes a third spelling reach every lane at once |

The distinction worth reading twice is `:predicate` against `:relation` in the first row. A
mark read off a sentence's functor holds its subject to a symbol that is not an individual.
An argument *constraint* is looser on purpose: a function has argument positions exactly as
a predicate does, a function is CapitalCamelCase and so reads as an individual, and a
relation may be denoted by a NAT rather than named. Collapsing the two refuses the
conventional spelling and waves the exotic one through.

A family is **not** a storage roster. `functional` stores under the `:functional` prop where
`functionalInArg` stores `[pred n]` pairs; the two have no common storage to be rostered by,
only a common family and a common argument 1.

## The arms, and the join

`vaelii.impl.special` holds what the engine *does* — the `:integrate` / `:disintegrate` /
`:rebuild` triple and the structural `:wff` check — as a **map** keyed by functor. It has
no order of its own, deliberately: the order is the declaration's, so the table cannot have
two orders that must agree and no way to notice when they stop.

`special/entries` is the join. It walks `predicates/entries`, keeps the functors this table
holds an entry for, and merges each declaration's half (the `:props` kind a mark maintains,
and whether its arms run on the derivation path as well as the assert path) with the arms.
That single ordered vector is *the* enumeration all four walks use — integrate,
disintegrate, rebuild and wff — so a predicate declared and armed joins all four at once.

## What the declaration is read for

Once the entry exists, these follow from it. None of them is a list you also edit.

| Reader | What it takes |
|---|---|
| `special/entries` | the table's order, each `:props` kind, each derivation-path flag |
| `taxonomy/closure-relations` | every term whose storage kind is `:edge` — being cached as a closure and being in this set are one fact |
| `taxonomy/arg-declaration-props` | the `:argument-constraint` family, each paired with its own prop keyword |
| `taxonomy/functional-family-marks` | the `:functional` family, each spelling with the shape its own argument list implies |
| `settle`'s eight clash and trigger rosters | `:arbitrable` marks paired with their prop keyword, the `:sweeps` field grouped by kind, and the `:edge` storage kind |
| `spec/::prop-kind` | the set of `tax/props` keywords the grammar declares |
| `vocabulary/roster` | the `:enforced` / `:inert` prose, classed by `:facets` — and through it `interpreted` and `vocabulary-audit` |

Case conversion is not an alternative to pairing a functor with its prop keyword and never
was: `anti_transitive` stores under `:anti-transitive`. The declaration states the keyword.

## Refused at namespace load

Four validators, nine refusals, and **one** `ex-info` `:type` between them —
`:bad-table-entry`, discriminated by a `:mismatch` key. Whichever way the table is bad, the
caller catching it is the namespace load, and there is nothing a second keyword would let
that caller do.

| Validator | Refuses |
|---|---|
| `predicates/check-families` | a mark family whose spellings disagree about what they sweep (`:mismatch :family`); a term that sweeps and declares no shape (`:mismatch :sweeps`) |
| `special/check-entries` | an entry with *some* of the cache triple — the cache would fill on assert and leak on retract, or come back wrong after a recover; and an entry with no arm at all, which is a typo |
| `special/check-declarations` | a functor with arms and no declaration or the reverse (`:mismatch :enumeration`); a `:cached` declaration whose arms have no triple, or the reverse (`:mismatch :cached`); a `:checked` declaration with no `:wff` arm, or the reverse (`:mismatch :checked`) |
| `settle/clash-declaration-kinds` | a sweep kind the exposure pass has no arm for, and a definitional mark that does not sweep what it convicts (`:mismatch :reach`) |

`check-entries` and `check-declarations` are two validators at two layers rather than one
duplicated: the first sees only the arms and so can check only that they mirror each other,
and the second is the cross-layer half. Neither can catch an arm attached to the *wrong*
functor, which is what the tests are for.

The failures these prevent are the ones the engine cannot report. A family joined to one
lane and not another does not throw — the merge simply does not happen, or the clash simply
is not reported, in the one arrival order that route was the only way into.

## Adding one, end to end

1. **Write the term into the ontology.** `resources/kb/CxCore.txt`, term-centric: a
   `comment`, the predicate class, an `arg` per position, and any marks it carries. This is
   the KB half and it is data.
2. **Declare it** in `predicates/entries`, through a constructor where one fits. Position
   matters: the functors `special/entries` holds come first, in the table's own order.
3. **Give it arms** in `special`'s `arms` map, if it is `:cached` or `:checked` — the
   triple, the `:wff` check, or both. Declaring `:checked true` with no `:wff` arm will not
   load, and neither will the reverse.
4. **Answer for it.** Either `:enforced` prose naming the path that reads it, or the `inert`
   constructor with the reason nothing does. A term CxCore comments and nobody answers for
   lands in `vocabulary-audit`'s `:unclassified`.
5. **Let the views follow.** Do not add the functor to `taxonomy`'s three rosters,
   `settle`'s eight, `spec/::prop-kind` or `vocabulary/roster` — they are reads, and adding
   it by hand puts back exactly the drift this structure removed. The rosters that are *not*
   views, listed under "One term, one entry" above, are the ones that still need the entry
   written into them.

### What a new term owes

| Test | Because |
|---|---|
| `predicates_test` | the declaration's own contract: every inert term carries a stated reason, every note names a lane the facet vocabulary does not reach, and a roster that has moved states its value as a **literal** — reconstructing a derived var proves the wiring and nothing about what it holds |
| `special_table_test` | the table's order, each `:props` kind and each derivation-path flag, frozen in a table written out that nothing derives |
| `vocabulary_audit_test` | `:unclassified`, `:retired` and `:contradicted` are empty on the shipped ontology |
| `core_context_test` | the CxCore sentex count, which [kbs.md](kbs.md)'s shipped-KB table quotes and nothing else pins — update both together |
| `refusal_roster_test`, `type_contract_test` | only if a new `ex-info` `:type` is introduced. Reusing `:bad-table-entry` with a new `:mismatch` value is the cheaper move and needs neither |

Then `lein gate`, and `lein test-matrix --owed`: a declaration change reaches inference,
TMS and planning, so the matrix is owed.

## Reading the answer back

`(interpreted term)` returns `{:enforced "where"}`, `{:inert "why"}`, or `nil`, and
`(vocabulary-audit kb)` gives the whole picture — including `:unclassified`, the finding it
exists to surface: a declaration that landed in the grammar without anybody deciding whether
the engine reads it. Both are on `vaelii.core`; see [api.md](api.md).

`nil` is **not** "nothing reads it". The question is asked of the engine's own grammar, so
an ordinary domain predicate — `marriedTo`, at the top of this page — is simply not a term
this question is about.

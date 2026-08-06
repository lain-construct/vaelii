# Equality: `rewriteOf`, `sameAs`, `equals`, and `different`

How two names come to denote one thing, and why the unique-name assumption survives it.

## The problem

Nothing in the engine can say two names denote the same individual. Dedup is
syntactic — `find-or-create-sentex` keys on the canonical sentence — so `Obama`
and `BarackObama` are two individuals with two disjoint fact sets, two type sets,
two argument roots, and no way to ever connect them.

That caps the KB at hand-curated single-source data. Every real ingest pipeline
produces co-referents on day one, so this is the precondition for an import path,
not a refinement of one.

It also makes the most useful common-sense constraint unusable. Without equality,
`(functional motherOf)` plus `(motherOf Tom Mary)` and `(motherOf Tom MrsSmith)` can only
be a hard error at assert time, even when they are the same woman — and functional roles
(mother, birthplace, age) are exactly where co-reference shows up.

## Three assertable relations, one closure

| relation | scope | contract |
|----------|-------|----------|
| `(rewriteOf P D)` | any term | directional: `D` is **deprecated**, migrate off it |
| `(sameAs A B)` | individuals | OWL: reflexive, symmetric, transitive, substitutive |
| `(equals A B)` | any terms | equality without OWL's individual restriction |

All three feed **one equivalence closure**. They differ in what they say *about*
the members, not in the classes they produce:

- `rewriteOf` names the representative and marks the loser deprecated. Because it
  is about *spelling* rather than identity, it applies to predicates and types as
  well — which is what vocabulary alignment on import needs.
- `sameAs` follows OWL, which uses `sameAs` for individuals, `equivalentClass` for
  classes and `equivalentProperty` for properties. Both names stay first-class;
  neither is deprecated; the representative is an internal detail.
- `equals` is `sameAs` without the individuals-only restriction, kept deliberately
  cheap — see "What is not built" below.

Picking a canonical representative and rewriting to it is how OWL reasoners
implement `sameAs` anyway, so one mechanism serves all three.

### Choosing the representative

Order independence is non-negotiable ([nmtms.md](nmtms.md)), so the choice can
never depend on handle ids or arrival order — handles are allocated in assertion
order, and keying on one is how the Nixon diamond starts answering differently
depending on which side was asserted first.

1. If a `rewriteOf` edge in the class names a preferred term, it wins. Chains
   compose: `rewriteOf A B` and `rewriteOf B C` make `A` the representative of all
   three.
2. Otherwise, and to break a tie among several preferred candidates, the
   **lexicographically smallest symbol**. Arbitrary but content-keyed and stable,
   the same discipline as `solve/content-key`.

A `rewriteOf` cycle has no representative and is rejected by `wff`, like a `genl`
cycle.

## The unique-name assumption survives

OWL drops UNA. We do not. `(different X Y)` is **provable exactly when the
arguments lie in no shared equivalence class** — so distinct symbols denote
distinct individuals until an equality sentex says otherwise.

This is negation as failure over the equality closure, and it is what keeps
counting meaningful: counting distinct symbols stays correct except for terms
somebody explicitly merged, so `count-with-arg` and friends do not acquire a
blanket caveat.

`different` is:

- **Variable arity.** `(different A B C)` asserts the arguments are pairwise
  distinct.
- **Not assertible.** It is answered by a prover and never stored. Asserting it is
  rejected. (An assertible `different` would be OWL's `differentFrom` — a positive
  commitment that makes a later `sameAs` contradictory. Deliberately not built.)
- **Ground only.** The prover is inapplicable unless every argument is bound.
  `(different ?x Y)` would enumerate every term in the KB that is not `Y`, so it is
  refused rather than answered explosively.
- **Not canonicalized.** No chain merging, no clique merging, no subsumption
  elimination, no argument sorting.
- **At least two arguments.** Fewer is inapplicable, matching the evaluable
  provers. `(different A)` asserts nothing and `(different)` is meaningless.

Two contract details the closure must pin down, because `different` reads them:

- **A term the closure has never seen is its own singleton class.** So
  `same-class?` is reflexive everywhere, and an unmerged symbol is different from
  every other unmerged symbol. (The prover short-circuits `(different A A)` before
  consulting the closure, so it stays correct either way — but the closure should
  not leave the question open.)
- **The closure holds symbols, not compound terms.** Equality *between* compounds
  is the equational-theory case deliberated away below, so `sameAs` / `equals` /
  `rewriteOf` take symbols and `wff` rejects a compound argument. `different`,
  though, may compare ground compounds: it normalizes each argument by replacing
  its symbols with their representatives and compares the results, which is
  congruence-consistent and needs no theory.

That last point deserves its reason, because the obvious analogy is wrong.
`lessThan` merges chains because it is **transitive**: `a<b` and `b<c` give `a<b<c`
for free. `different` is **not** transitive — `A≠B` and `B≠C` say nothing about `A`
and `C` — so chain-merging it would manufacture a claim nobody made. The only
sound merge would be a *clique* (every pair present), which is more machinery than
the feature is worth. And since `different` is never stored, there is nothing to
canonicalize *for*: canonical form exists to make logically identical knowledge
store once, and this stores never.

Because it consumes bindings rather than producing them, `different` is a
**deferred literal**, the same class as `lessThan` / `greaterThan` / `evaluate`.
`sentex/canonical-conjunction` holds that whole class back in the author's order —
`held?` there asks the public `sentex/deferred-literal?` — because their position is
operational rather than logical. (`sentex/cmp-term` is the total order the *generators*
are sorted by, and never sees them.)

## What a merge does

Four parts, all reusing machinery that already exists:

1. **Migrate.** `find-sentexes` returns every sentex containing the non-preferred
   term, at any nesting depth, in one index lookup. Each gets a rewritten twin
   under the representative, **derived and justified** by `[the original sentex,
   the equality sentex]`. Dedup falls out: when the rewritten form already exists,
   find-or-create returns that handle and it simply gains a second justification.
   One twin per *reader* whose election differs, placed where that reader lives —
   "Scope, context, and re-election" below.
2. **Supersede the original.** The stale spelling stays stored but is not believed
   and does not match. Handles that callers already hold stay valid.

   This needs **new TMS state**. `exceptWhen`'s `:blocked` is a set of
   *justification* ids read by `valid?`, but a directly asserted
   `(bornIn Dep Chicago)` is a **premise** with no justification at all, and
   `relabel` holds a premise IN unconditionally. So superseding a premise needs a
   force-OUT set over *datums*, alongside `defeated`, carrying its own reason so
   `why-not` can tell the two apart.

   It also deliberately reintroduces the stored-but-not-believed state that
   [`exceptWhen`](exceptions.md) refuses, and the difference is in what is at stake
   either side of it. An excepted conclusion is the *engine's* own derivation, so
   deleting it loses nothing that cannot be recomputed. A superseded spelling is
   the **caller's premise**. The KB may not delete what someone asserted merely
   because it learned two names denote one thing — retracting the equality has to
   give it back.
3. **Rewrite goals.** A query naming a non-representative is rewritten before
   lookup, since its own sentexes are no longer believed.
4. **Queue the re-check.** Steps 2 and 3 are exactly what a closed-world condition —
   an `exceptWhen` query, an `unknown`, an aggregate's census — cannot see coming. A
   retired spelling leaves no fact arriving or departing on its predicate, and a
   rewritten goal changes an answer with nothing on the queried predicate moving at
   all, so neither the predicate keying nor the firing keying that narrows the taxonomy
   triggers can reach it. `special/recheck-equality-edge` therefore queues every rule
   carrying such a condition, both when the closure grows and when it splits, and
   `chain/settled-bindings` rewrites the firing's stored bindings before the condition
   is re-evaluated — a justification records what matched when it fired, and a merge
   does not go back and edit it. [exceptions.md](exceptions.md) is where that channel
   sits beside the other three.

**`different` is exempt from step 3.** Rewriting a `different` goal would map every
argument to its class representative, so a merged pair would compare equal — and
since the whole job of `different` is to *read* class membership, every goal would
come out false the moment anything merged. Its arguments are already
rewrite-invariant: the prover consults the closure directly. Exempt it explicitly
rather than relying on the rewrite being a no-op.

Dropping the equality invalidates the derivations, the dependency-directed sweep
collects the twins, and un-superseding revives the originals.

### Scope, context, and re-election

**An equality applies where it is visible.** A merge asserted in `CoreContext`
applies everywhere; one asserted in a context applies there and below, by the
ordinary `genlContext` up-closure. That answers "is equality global or scoped" the
same way everything else in the engine answers it, and it is what lets a story
merge two characters without leaking into an unrelated one.

That holds on the **question** as much as on the answer. `kb/rewrite-goal` takes the
goal's context and rewrites only by the merges it can see; the class reads
(`representative` / `same-class?` / `equiv-class` / `deprecated?`) take one too, and
`different` reads the scoped partition, since the unique-name assumption is what a
context holds until *it* is told otherwise. Scoping migration alone would be worse
than scoping nothing: the goal would be renamed to a spelling migration correctly
declined to create, and the asking context would lose a fact it still believes, under
either name. An invisible edge can **split** a class, so the scoped read is its own
election over the visible edges rather than a filter of the global answer
(docs/taxonomy.md).

#### The reader is not the fact's own context

Which makes the twin's placement the hard half, because **a fact and the merge that
restates it need not live in the same context**, and the party whose spelling is at
stake is neither of them — it is whoever *reads* the fact, which is any context below
it, each electing over a different set of visible edges.

Two shapes make the point, both with `Leaf` under `Mid`:

- The merge sits **below** the fact. `(likes Tom Bravo)` in `Mid`, `(rewriteOf Alpha
  Bravo)` in `Leaf`. `Mid` has been told nothing and keeps its spelling. `Leaf` sees
  both, so `Leaf` elects `Alpha` — and a context that can see a fact has to be able to
  ask for it. One normal form computed at the fact's context serves `Mid` and leaves
  `Leaf` asking under two names that both miss.
- The class is **split across** the chain. `(rewriteOf Bravo Charlie)` in `Mid` and
  `(rewriteOf Alpha Bravo)` in `Leaf` put `Mid` and `Leaf` on different heads of one
  `rewriteOf` chain: `Mid` elects `Bravo`, `Leaf` elects `Alpha`. One normal form
  computed *globally* serves `Leaf` and hands `Mid` a spelling only `Leaf`'s edge
  produces — while `Mid`'s own fact, superseded, is retrievable under nothing.

So migration runs **once per reader whose election differs**, and each twin is placed
in the context that elected it. The readers are the fact's context closed under where
it meets the equalities' — `tax/meet-closure`, the same enumeration a qualitative
network takes over the contexts holding its facts ([qcn.md](qcn.md)) and for the same
reason: knowledge stated in several contexts is read by whoever inherits some
combination of them, and which combination changes the answer. Two readers electing the
same form share one twin, at the more general of them; a reader that changes nothing
costs one rewrite. The candidate set is the whole **class**, not the edges incident on
the sentence's own terms — chain composition means an edge touching nothing in the
sentence still moves what its terms rewrite to.

The fact's own context is always a reader, and it is the one that supersedes: a reader
*below* it restates the fact for itself and leaves the original believed where it
lives, because that context has been told nothing.

**Which leaves supersession short by one, and the shortfall is a read filter.**
`jtms/superseded` is per *datum* — a sentex lives in one context, so one flag answers
for one context — while staleness is per *reader*. `Leaf` inheriting `Mid`'s
un-superseded spelling alongside the twin it elected would report one fact twice, under
two names it knows denote one thing, and every count over the answer set would double.
`res/without-retired` drops the matches whose stored spelling the asking context has
retired, beside the `except` filter that already removes what a context may not see.
It is gated on the closure being non-empty, so a KB that has merged nothing pays one
set-empty test per query.

**A late `rewriteOf` can move a representative, and that means re-migration.**
`(sameAs A B)` elects a representative lexicographically; a later `(rewriteOf B A)`
names `B` preferred and re-elects it. Everything already migrated to `A` has to
migrate again. The machinery handles it — invalidate the old twins, create new ones
— but it is the expensive case and it must be recognised rather than discovered.

### Choosing among class members

The candidate set for the representative is **preferred minus deprecated**, not all
members. Given `(rewriteOf A B)` and `(sameAs B Aardvark)`, the representative is
`A` — the head of the `rewriteOf` chain — even though `Aardvark` is
lexicographically smaller. Chain composition is what makes `rewriteOf` mean
anything; a plain member joining the class must not displace the head.

The taxonomy's representative function stays **total**. A `rewriteOf` cycle has no
head, and `wff` rejects one, but `wff` runs above the taxonomy and the closure must
still answer — so it falls back to lexicographic order over the preferred set, then
over all members. The closure never returns nil for a term it holds.

A **preference is per-supporter**, not per-edge. One edge may be supported by a
`sameAs` and a `rewriteOf` at once; disbelieving the `rewriteOf` withdraws the
deprecation while the merge survives on the `sameAs`.

`(sameAs A A)` is accepted — OWL makes `sameAs` reflexive. `(rewriteOf A A)` is
rejected: it is the degenerate cycle, it deprecates a term in favour of itself, and
it is what a sloppy import pipeline actually emits.

### Congruence comes free

Congruence — if `a = b` then any term containing `a` equals the same term with `b`
substituted — is normally the expensive half of equality reasoning.

Here it is a side effect of the cheap implementation. The inverted term index
locates a term at **any nesting depth**, and migration rewrites it there, so
merging performs congruence closure eagerly over all ground content. No congruence
algorithm is written, because the index already answers the question it would ask.

## `functional` infers equality instead of throwing

`(functional P)` plus two different **symbols** for the same first argument
**derives `(equals V1 V2)`**, with antecedents `[both facts, the functional
declaration]`. Everything else — two numbers, two strings, a compound — stays the hard
contradiction it is, because no merge can make two numbers one thing.

`equals` specifically, not `sameAs`: a functional value need not be an individual —
a birth year, a measurement — and `sameAs` is individuals-only by OWL. `equals` is
the only one of the three that always type-checks here.

Making it a real justification rather than a side effect is what makes it safe. The
risk of auto-inference is that one wrong `functional` declaration silently merges
two real individuals across the whole KB — so the merge is justified, `why` names
exactly which declaration and which two facts caused it, and retracting any one of
them runs the existing sweep and un-merges. An opaque merge would be dangerous; an
inspectable, reversible one is knowledge.

**Both directions, because a declaration reaches the facts already stored exactly as it
reaches the facts that follow.** `special/derive-functional-equalities` is a fact meeting
the declaration — it runs on every asserted fact and on every derived conclusion — and
`special/equate-existing` is the declaration meeting the facts, sweeping `P`'s extent off
the functor root when `(functional P)` itself arrives. Whether two spellings denote one
woman is a question about the KB's content, and an answer that depended on whether the
schema or the facts were loaded first would be an answer about the file. Written the
ordinary way — declaration first — the sweep finds an empty extent and costs one root
read.

The two directions ask one question from two sides, so neither can drift about what a
functional slot licenses: the equality names both facts and the declaration whichever way
round it was reached, and retracting any of the three un-merges. Re-deriving is
idempotent — `same-class?` skips a pair the closure already holds and `has-justification?`
skips an argument it already has — so a slot filled by three values collapses to one class
rather than to the first pair walked. The sweep reads what is **stored** rather than what
is believed, for `entail-existing`'s reason: an equality derived off a defeated fact rests
on that fact and is defeated with it, where skipping it would leave the merge missing when
the fact revives.

## Storage

The closure is a fourth cached relation in `vaelii.impl.taxonomy`, beside `genl`,
`genlContext` and the predicate metadata, and inherits their belief-following
`:support` discipline: an edge is active only while some sentex asserting it is
believed, and `refresh-beliefs` reconciles at the end of every `settle`.

It is an **equivalence**, not a partial order, so it is stored as a partition —
member → class, class → members and representative — rather than as up/down
closures. Insertion is a union and cheap. Deletion can **split** a class, which
union-find cannot undo, so a retraction rebuilds the affected class from its
remaining believed edges — the same shape as the cone-local `genl` deletion, and
bounded by the class rather than the KB.

`closures`-style from-scratch recomputation survives as the oracle, and the
incremental result is checked against it after every edit, as
[taxonomy.md](taxonomy.md) describes for `genl`.

## Public surface

`genl` has `genls` / `specs` / `genl?`; `genlContext` has `context-up` / `sees?`.
Equality gets the same treatment, or an application cannot see what merged:
`representative`, `same-class?`, `equiv-class`, `deprecated?`. Without
`deprecated?` in particular, nothing outside representative *selection*
distinguishes `rewriteOf` from `sameAs` at all, and the doc's claim that one
deprecates and the other does not would be unobservable.

All four take an optional context, and all four have to: they read one partition, so a
scoped `representative` electing `Bravo` beside an unscoped `deprecated?` calling
`Bravo` retired is two answers about one context. The unscoped arity asks about the KB
rather than from a vantage, which is what a `?ctx` goal means everywhere else.

`why-not` gains a reason. A superseded spelling is none of `:not-stored`,
`:defeated` or `:unsupported` — it is `:superseded`, naming the representative that
displaced it.

## Interactions

- **Disjointness.** A merge can *create* a violation: `(dog Rex)` + `(cat Fluffy)`
  + merge makes one individual both. So migration runs the integrity checks that
  `place-conclusion` already runs, and a derived violation is reported through
  `violations` rather than thrown.
- **Stratification.** `different` in a rule antecedent is a **negative
  dependency**, so it joins the rule dependency graph beside `exceptWhen`
  ([exceptions.md](exceptions.md)). A rule concluding an equality from a
  `different` antecedent is a cycle through negation and is rejected — otherwise
  belief would depend on arrival order.
- **Symmetric predicates.** Argument sorting for a symmetric predicate is done at
  canonicalization time against the *stored* symbols. A later merge changes what
  the sorted order should be, so migration must re-canonicalize rather than
  substitute textually.

- **Deferred literals are evaluated in a forward join** — `different` included.
  Being deferred is about *ordering*, and ordering is not evaluation. A forward join
  that matched every antecedent against the index would look a `different` (or
  `lessThan`, or `evaluate`) antecedent up as a fact nobody stores, find nothing, and
  kill the join; `chain/join-antecedent` instead sends a deferred antecedent to
  `provers/solve-goal`, the same registry the backward chainers discharge it through.
  The two ask at **different contexts**, though, and `different` is one of the two
  deferred literals that notices: the forward join asks at the wildcard `'?ctx`, so it
  reads the whole equality partition, where a backward search reads the partition its
  goal's context sees. See [inference.md](inference.md) for the pair and for what the
  justification records.

## What is not built

**Symbolic equational reasoning is built — as oriented term rewriting.** A
schematic `(equals L R)` whose sides carry variables —
`(equals (fatherOf (fatherOf ?x)) (grandfatherOf ?x))` — is **oriented by a
reduction order** (KBO with unit weights) into a terminating rewrite `L → R`, cached
in the taxonomy's rewrite-rule set (belief-following like the partition).
`rewrite-term` normalizes both stored terms and query goals to one normal form, and
migration justifies each rewritten twin by `[original, equation]`, so retracting the
equation collects the rewrites and revives the originals — the same discipline
ground congruence has. Orientation is content-derived (the bigger side by term size
shrinks, under the variable condition), so it is order-independent and rewriting
always terminates. See [equational.md](equational.md) for the full mechanism.

Compound equality over **reifiable NATs** — `(equals (MotherOf A) (MotherOf B))`,
*A and B share a mother* — needs nothing new: each side reifies to its constant
before it reaches the closure ([nat.md](nat.md)), reducing to an ordinary symbol
merge that the partition + migration already handle.

Orientation is the **full Knuth-Bendix order** (`rewrite/kbo>`): unit weights decide
unequal sizes, and an equal-size pair is oriented by a fixed symbol precedence, so
`(f (g ?x)) = (g (f ?x))` orients too. Only a **permutative** equation —
`(rel ?x ?y) = (rel ?y ?x)`, which no term order can orient — is refused; that needs
AC-rewriting, a separate mechanism. Normalization reaches all four query paths:
`sentexes-matching`, `ask`, `prove`, and `query` all rewrite the top goal — the last two
through `core/prepare-goal-for-read`, which is what keeps a goal naming a merged spelling
from being answered by `ask` and silently missed by `prove`. `different` is exempt, since
its arguments must stay un-rewritten to read class membership.

What stays unbuilt is the **open-goal / search** half. No **E-unification or
paramodulation** — proving `(equals ?x ?y)` by searching rewrites of a goal on
demand — which is non-terminating without careful control; the oriented path covers
the term-definition case that motivates it. No **Knuth-Bendix completion** — a
non-confluent rule set is *detected and reported* (a `:non-confluent` violation when
two equations disagree about a shared term) but not made confluent; the normal form
stays deterministic and `unify` stays the arbiter, so a match is never *wrong*, only
sometimes missed (see [equational.md](equational.md), "Confluence"). And equality over
**structural NAT / evaluated** functions is the compute provers' job (`sameQuantity`,
`evaluate`), never the closure's.

**`differentFrom`.** See above: `different` is not assertible, so there is no way
to positively commit to two things being distinct. UNA covers the default case,
which is the common one.

## Merging predicates and types

`rewriteOf` reaches predicates and types, not only individuals — vocabulary
alignment on import (`birthplaceOf ⇒ bornIn`, `dog ⇒ canine`) produces co-referent
*predicate* and *type* names on day one. Because a merged term now heads sentences
(functor position) as well as filling arguments, the migration reaches further than
individual merging:

- **Facts and declarations** headed by the retired term are re-canonicalized under
  the representative and stored as justified twins, exactly as an argument-position
  occurrence is. So `(birthplaceOf Ada London)` becomes `(bornIn Ada London)`, and
  the functor root `[:functor-root birthplaceOf]` no longer answers a believed query.
- **The `genl` closure** moves with a merged type: `(genl dog animal)` migrates to
  `(genl canine animal)` and `isa?` / `genls` / `specs` answer under the
  representative, the retired type's edge dropping as its declaration is superseded.
- **The flat caches** — `disjoint`, the predicate metadata (`transitive`,
  `symmetric`, `inverse`, `functional`, …), metatype membership — follow, since each
  declaration is a sentex the merge re-canonicalizes.
- **Rules** are migrated too (the gate above), through the same justified-twin path:
  the rewritten rule re-posts under the representative's predicates in the rule
  index, keeps its `:direction` / `:defeasible` (re-applied by `rules/rewrap`,
  since the wrappers ride the record, not the stored sentence), and fires under the
  representative while the original is superseded.
- **A rule's guard travels with it.** An `exceptWhen` exception rides a separate
  meta-sentex keyed by the rule's handle — `(exceptWhen <query> (sentexHandle H))` —
  so migrating the rule to a new handle H′ would strand it. `migrate-rule-exceptions`
  re-points each of the rule's exceptions onto the twin (query rewritten too), derived
  and justified by `[the meta, the equality]`, so the twin fires *guarded* and
  retracting the merge collects the exception twins and revives the originals. A NAF
  `(unknown …)` antecedent lives *in* the rule sentence, so it rewrites with the rule
  and re-posts through the twin's own `index-rule-sentex`. A predicate merged only in
  an exception's *query* (the rule itself not migrated — `penguin` in
  `bird ⇒ flies exceptWhen penguin`) is handled by the ordinary meta-sentex migration,
  which rewrites the query onto the representative so it keeps blocking the migrated
  facts.

`rewriteOf` is the spelling relation, so it is the one that carries alignment across
predicates and types, and
`wff` enforces that a `rewriteOf`'s two sides are the **same role** —
predicate-with-predicate, type-with-type, individual-with-individual — since a
cross-role merge is meaningless and a likely import bug. A bare lowercase word is
`:either` and accepts any non-individual partner; a **namespaced** symbol is `:opaque`
and accepts every partner, because the roles are conventions over names a person chose
and a reified NAT constant ([nat.md](nat.md)) is one the engine minted — what it
denotes is settled by its materialized result types, so retiring one into the real term
its function's corresponding predicate names is exactly the move this check must not
refuse.

## Where the pieces are

- The closure in `vaelii.impl.taxonomy` — belief-following `:support`, incremental
  union, class-local rebuild on delete, checked against the from-scratch oracle after
  every edit. `representative` / `same-class?` / `equiv-class` / `deprecated?` are
  re-exported on `vaelii.core`.
- The `different` prover: ground-only, refuses an open goal, reads the closure.
- Routing in `special/integrate-sentex` / `disintegrate-sentex!`, beside `genl` and the
  predicate metadata. `different` is refused by `wff` on the way in.
- Migration (`migrate-sentex` / `migrate-class`): re-canonicalized rather than
  substituted, one justification per incident equality edge, and applied only where the
  equality is *visible* by the `genlContext` up-closure — once per **reader** whose
  election differs (`reader-contexts-for`, over `tax/meet-closure`), each twin placed in
  the context that elected it. Runs over the whole class, so a late `rewriteOf`
  re-electing the representative re-migrates with no separate code path.
- Supersession as **new TMS state** — `jtms`'s `:superseded`, a `datum -> {old-term
  representative}` map beside `defeated` and `blocked`. It is deliberately *not* a
  forced-OUT inside the fixpoint: the twin is justified by the original, so forcing
  the original out structurally would invalidate the twin and the merge would believe
  neither spelling. What it subtracts is *reported* belief — `in?` and `in-datums`
  read it — so the stale spelling stops matching while everything derived from it
  stands. Recomputed from the closure each `settle`, like the other two, so a
  retracted equality gives the caller's premise back with no un-supersede path. Read
  from the sentex's **own** context, the way migration writes it.
- The reader-scoped half of it, `res/without-retired`, in `matches-visible` and
  `sentexes-matching-as-stored`: a match whose stored spelling the *asking* context has
  retired is dropped, so a reader below a merge reports the fact once, under the name it
  elected. Gated on the closure being non-empty.
- Goal rewriting in `sentexes-matching` and `ask`, with `different` exempt. `handle-of` and the
  `lookup` levels deliberately do not rewrite: they answer about storage, not truth.
  Scoped by the goal's context, so a merge the asker cannot see does not rename what it
  asked.
- `functional` derives `(equals V1 V2)` from `[both facts, the declaration]` on the
  assert path *and* the derivation path, rather than throwing: two values for one
  functional first argument is a claim that they are the same value.
- `wff` refuses a compound argument to all three relations, a `rewriteOf` cycle
  (multi-edge, by reachability over the preference graph) and self-edge, and a
  **cross-role** `rewriteOf` — predicate-with-type, type-with-individual. A
  `rewriteOf` between two predicates or two types is legal and is the point of the
  relation. `(sameAs A A)` is accepted.
- `different` in a rule antecedent is a negative dependency in the stratification
  graph, with its negative edge running to the three equality relations. A rule
  concluding an equality from a `different` antecedent is refused at assert time.
- A merge that creates a disjointness violation is reported through `violations`, not
  thrown, and the impossible twin is dropped rather than stored. The report is
  appended *after* `chain-all`. The ledger accumulates across runs rather than
  resetting per run (`chain/chain-all`, [nmtms.md](nmtms.md)).
- `recover` rebuilds the partition from the stored `rewriteOf` / `sameAs` / `equals`
  sentexes and recomputes supersession from it.

### Known gaps

- **A functional clash between non-symbols still throws.** The closure is a partition
  over symbols, so `(equals 1980 1990)` is not a sentence the KB can hold — and two
  numbers genuinely cannot be one thing. `checks/mergeable-values?` therefore admits an
  equality only when both values are plain symbols, and `checks/functional-problems`
  keeps the hard `:functional` rejection otherwise. That is the line between a clash
  that is knowledge and a clash that is an error, and it is what lets the numeric
  functional tests stand unchanged.
- **Only the assert-time stratification check sees a `different` antecedent.** A rule
  carrying one is not added to the `exception-rules` index, so `edge-negation-cycle` —
  which walks out from excepted rules when a `genl` edge arrives — cannot start at it.
  A cycle closed by a *later taxonomy edge* underneath a stored `different` rule would
  be missed.
- **An individual merge does not migrate a rule.** `rewritable-sentex?` holds a rule
  back when the merge only touches an individual constant: rewriting it is congruence
  over a schema rather than over ground content, and the rewritten copy would fire
  alongside its original. A **predicate or type** merge does migrate the rule (see
  "Merging predicates and types"), because it changes a functor the rule reasons
  over and the original is superseded — carrying the rule's `exceptWhen` exceptions
  (re-pointed onto the twin) and its NAF antecedents (rewritten in the sentence) with
  it, so the twin fires guarded.

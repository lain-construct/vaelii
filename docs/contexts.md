# Contexts

- **Covers:** how a sentex is scoped to a context, how the `genlContext` closure orders
  contexts into the shipped spindle, and where a forward-derived or lifted fact is placed.
- **Not here:** `genl`, the sibling closure over types rather than contexts →
  [taxonomy.md](taxonomy.md); a storage-level private copy of a whole KB, which a context
  does not provide → [overlay.md](overlay.md).
- **Assumes:** sentex, belief, `genl`, taxonomy → [glossary.md](glossary.md).

Every sentex is in exactly one **context** (a CapitalCamelCase symbol ending in `Context`). Contexts
partition and scope belief.

## genlContext: the context hierarchy

`(genlContext Sub Super)` means `Sub` *sees* `Super` — a specific context inherits the
assertions of the more general ones. `vaelii.impl.taxonomy` caches the reflexive-
transitive up/down closure (`context-up`, `context-down`, `sees?`), recomputed when a
`genlContext` edge is asserted/retracted. A context `K` sees a sentex in context `Y`
iff `Y ∈ context-up(K)`.

**Two contexts may see each other.** Unlike `genl`, a `genlContext` cycle is admitted:
visibility is a preorder, not an order, and mutual visibility is a claim an ontology
makes — OpenCyc's `genlMt` graph has 49 such components, one of them BaseKB's own
(`BaseKB ↔ UniversalVocabularyMt ↔ CycAgencyTheoryMt ↔ …`). Reachability over a cycle
is perfectly well defined, so the closures answer it directly; the taxonomy keeps its
depth potential over the **condensation** and reads a mutually-visible pair in O(1)
(see [taxonomy.md](taxonomy.md)).

What a cycle is *not* is a merge. The contexts stay distinct records with distinct
extents, because a context is where a sentex is **stored** and not only what it can see:
`sentexes-matching` is exact-context, `(ist BaseKB S)` and `(ist UniversalVocabularyMt S)` are two
sentexes, and collapsing them would throw away which context an assertion was made
in — the one thing an ontology import exists to carry. The claim "each sees the other"
is weaker than "these are the same place", and only the weaker one was made.

The single point where the engine needs a unique answer is **placement**, since every
member of a component is an equally maximal common descendant and the conclusion should
land once rather than once per name. `taxonomy/placement-rep` picks the component's
`term-min` — content-keyed, so it cannot depend on the order a firing's antecedents were
listed in — and every one of `maximal-common-descendant-contexts`' exits runs through it,
the single-context fast path included.

That answer is only as good as `:scc`, which makes the component map the one piece of
derived state here that is **more than a pruning**. A dissolved-but-unrepaired component
does not merely cost `sees?` a walk; it leaves the group with no name, so
`placement-rep` hands back whichever member the caller happened to ask about. Belief is
what can dissolve one without a sentex moving — an edge defeated out of a cycle, or
revived back into one — so `settle` repairs the potential **after** it reconciles belief
as well as before, and no firing ever runs against a component the reconcile unmade.
Deferred to the next settle instead, one conclusion would land in `AlphaContext` and the
next in `BetaContext` for no reason but how many settles had run since the defeat.

## The context spindle

The default topology is a **five-layer spindle**, most general (top) to most specific
(bottom): the vocabulary head, a *definitional* band, a mid anchor, a *theory* band,
and a bottom anchor. Data hangs below the bottom.

- **CoreContext** — the spindle *head*: the code-supported vocabulary (every special
  predicate the engine interprets), asserted by `vaelii.impl.core-context`. The root —
  every context sees it.
- **upper** — the *definitional* band, between Core and Universe: what things *are*,
  always true, like `genl`. One context per domain (`vaelii.impl.starter`), each
  seeing CoreContext and seen by UniverseContext:
  - `AbstractContext` — the abstract type skeleton (`intangible`/`physical_object` and
    their kinds) plus the structural relations `partOf`/`locatedIn`.
  - `OrganismContext` — the biological taxonomy and its disjointness.
  - `LifeContext` — the organism relations (`parentOf`, `siblingOf`, `flies`, `mortal`,
    `birthYearOf`, `olderThan`, …) with their argIsa and metadata.
  - `SocietyContext` — the social relations (`marriedTo`, `likes`, `owns`).
  - `MeasureContext` — the theory of measurement: the two measure terms, the
    `dimensionOf`/`conversionFactor` table, the five comparisons ([quantity.md](quantity.md)).
  - `SpaceContext` — qualitative space, four independent calculi in one context because
    all four are *about* space: RCC-8 topology, cardinal direction, relative direction
    and qualitative distance, fifty predicates between them ([space.md](space.md)).
  - `TimeContext` — qualitative time in three layers over the same subject: Allen's
    thirteen interval relations plus seven derived disjunctions, the point algebra over
    instants with the endpoint predicates that bridge the two, and the metric layer
    (`temporalDistance`) that puts real measures on the gaps ([time.md](time.md),
    [stp.md](stp.md)). The `length` / `totalDuration` / `overlapDuration` vocabulary the
    duration arithmetic computes over lives here too ([duration.md](duration.md)).
- **UniverseContext** — the mid *anchor*, left free for **lifting**: universally-true
  facts collect here (`decontextualizedPredicate` justifications and the forced `genlContext`
  extent). It sees every upper context and is seen by every middle context.
- **middle** — the *theory* band, between Universe and Well: how the definitional
  things *interrelate*, where several overlapping theories can coexist. One context
  per theory, each seeing UniverseContext and seen by WellContext:
  - `KinshipContext` — grandparentOf, ancestorOf, olderThan.
  - `MereologyContext` — a part is located where its whole is; owning a whole entails
    owning its parts.
  - `BiologyContext` — birds fly by default except penguins; living things are mortal;
    flight enables travel.
  - `AnatomyContext` — what kinds of thing have what kinds of part, entirely in
    `partType` claims. Nothing here concludes anything about an individual, which is
    deliberate: "birds have wings" to "Pingu has a wing" needs a quantifier reading.
  - `SizeContext` — comparative size said the two ways it can be said: `largerThan`
    among kinds, and a comparison computed between two objects' measures. The worked
    example of `argPreserving` ([inherit.md](inherit.md)).
  - `SocialContext` — what acquaintance follows from, and how employment relates to
    membership. Every rule runs one way only, because `knows` is deliberately not
    symmetric.
- **WellContext** — the bottom *anchor*: it sees every middle theory, so it (and any
  context hung beneath it) transitively sees the whole ontology.

Each upper/middle file wires *itself* into the axis with two `genlContext` edges, so
the topology is **data** — dropping a `<Context>.txt` in `resources/kb/upper/` or `resources/kb/middle/`
adds a context, no code change, and every context present is loaded on kb start by
default. There is **no** direct `(genlContext WellContext CoreContext)` edge; Well
reaches Core through the whole axis (middle → Universe → upper → Core).

`vaelii.impl.core-context` loads only the head (CoreContext); the bands are the starter's,
so a **CoreContext-only KB is just the vocabulary** — no spindle bands at all.

### The shipped KB is schema only

The starter ships **no individuals and no facts** — only types, relation definitions,
and the theory rules. Contingent data (a cast, worked examples, the Aesop fables)
belongs **below WellContext** and lives in the tests that need it: `test/vaelii/world.clj`
hangs `NaturalWorldContext` / `SocialWorldContext` off WellContext, and
`test/vaelii/world_fables.clj` hangs `StoriesContext` there with a context per fable
beneath it.
Because a middle theory is seen by every WellContext descendant, a rule firing over
cast facts in `NaturalWorldContext` places its conclusion back in `NaturalWorldContext`
(the maximal common descendant), where a query finds it.

### Adding a sibling context

A user adds their **own sibling** in either band. A *definitional* sibling sees
CoreContext and is seen by UniverseContext (`(genlContext MyContext CoreContext)` and
`(genlContext UniverseContext MyContext)`); a *theory* sibling sees UniverseContext and
is seen by WellContext. Its vocabulary is visible from every data context below Well
without touching the shipped bands.

## Context-aware inference

`res/matches-visible` restricts matching to facts visible from a query context
(its `context-up` closure). Backward chaining (`query`, `prove`) uses it, so
proving a goal *in* a specific context can use facts asserted in the general
contexts it inherits — but not the other way around.

## Context placement of justifications

Forward chaining matches antecedent facts across *any* context, then places the
derived sentex in the **maximal** contexts that see the rule and all the matched
facts: `taxonomy/maximal-common-descendant-contexts` = the most-general elements of the
intersection of the facts' + rule's `context-down` closures. This can be several
(incomparable maxima) or none (no common view ⇒ no justification). A universal rule
firing on specific facts lands its conclusion in the specific context — unless the
consequent is an `(ist Ctx S)` form, which directs it into `Ctx` explicitly (below).

### Enumerating the readers

`taxonomy/meet-closure` is the same primitive asked the other way round: given the
contexts some knowledge is *stated* in, which contexts *read* it — the members
themselves, closed under `maximal-common-descendant-contexts` over their pairs. Two
subsystems need it, and neither can settle for "the contexts holding a fact":

- a qualitative network composes only what one reader can see, so a context inheriting
  two contexts entails what neither entails alone ([qcn.md](qcn.md));
- an equality election runs only over the edges one reader can see, so a fact above a
  merge is restated differently by different readers ([equality.md](equality.md)).

Pairs reach every subset: a common descendant of three is a common descendant of two of
them, hence under a maximal one, hence under a maximal common descendant of *that* and
the third. The closure may therefore hold a context that is maximal for no subset, which
costs a read and cannot cost an answer — a more specific reader sees a superset of the
knowledge, so it either agrees with a more general one or refines it. **Fewer than two
contexts closes immediately**, which is every KB that has not divided the knowledge in
question between contexts: there is nothing for a second to meet.

The starter's owns-parts rule shows both outcomes. The rule `(implies (and (owns ?p
?whole) (partOf ?part ?whole)) (owns ?p ?part))` is a middle theory (`MereologyContext`,
seen by every data context below Well), and the test-world cast supplies the facts. It
derives `(owns Tom Roof1)`: both `(owns Tom House1)` and `(partOf Roof1 House1)` sit in
SocialWorldContext, so the intersection is non-empty and the conclusion lands there.
But `(owns Tom Engine1)` is **not** derived — `(owns Tom Car1)` is in SocialWorldContext
while `(partOf Engine1 Car1)` is in NaturalWorldContext (sibling data contexts with no
common view), so the placement intersection is empty and no justification is made.

## except: removing visibility down a context subtree

`(except (sentexHandle H))` asserted in context C removes visibility of the sentex `H`
from C **and every context that sees C** — its `context-down` closure — while leaving
the more general contexts C sees untouched. It is a **meta-sentex**: `(sentexHandle H)`
is the term form of a stored sentex's handle (`sentex/sentex-handle`), so the except
names the sentex it hides rather than restating it. Like every other fact it is
belief-following — retracting or defeating the except restores the hidden sentex — and
it rides the ordinary `genlContext` up-closure, visible from exactly the contexts where
it hides its target.

The removal is **total**, not just for reads:

- **Reads.** `res/matches-visible` and `sentexes-matching` drop a handle in
  `res/excepted-handles` of the view context — the believed excepts visible from
  there, resolved through `context-up`. Gated on the `except` functor root, so a KB
  using no `except` pays one count.
- **Derivations.** A rule firing that used `H` as an antecedent and placed its
  conclusion in the cone rests on a fact that context can no longer see, so the
  conclusion is **blocked and swept** — the derivation-side twin of `exceptWhen`, run
  through the same block/sweep/revive machinery (`chain/justification-excepted?` and
  `place-conseq` read the hidden set per placement). A firing that arrives *after* the
  except is never placed in the cone; a late except sweeps what already fired; and
  retracting the except **re-derives** what it was hiding. A conclusion placed *above*
  the cone (a context that does not see the except) is untouched.

The re-check triggers are the except arriving or leaving (`special/recheck-except`,
keyed on the handle it names rather than a predicate) and any `genlContext` edge change
(`special/recheck-except-cone` — a visibility move changes which contexts see the
excepting context, hence what each hides).

## ist: find or create in a context

`ist` — "is true in", the operator from the literature — expresses that S holds in
Ctx. `(ist Ctx S)` is **not** stored as a sentex; given to `assert` (or via
`ist kb Ctx S`) it finds or creates S in context Ctx and returns S's handle
(idempotent).

- `ist kb Ctx S` — find or create S in Ctx.
- `contexts-of kb S` — the contexts S is asserted in.
- `find-sentexes kb S` — any sentex containing S (via the term index).

**ist in a rule consequent.** A rule whose consequent is `(ist Ctx S)` places `S`
into the named context `Ctx` instead of the computed placement — overriding the
default maximal-contexts rule. `Ctx` may be a variable bound by an antecedent (e.g.
`(genlContext ?c UniverseContext) ⇒ (ist ?c ...)`). The rule is indexed by `S`'s predicate,
not by `ist`, and range-restriction covers the inner sentence and the context slot.

**The predicate meta-ontology** is a worked example. Predicates are reified as
individuals under `predicate` (itself a `thing`): `unaryPredicate` (types and
one-place properties), `binaryPredicate`, `ternaryPredicate`, and the algebraic
subtypes of `binaryPredicate` — `symmetricPredicate` / `asymmetricPredicate` /
`transitivePredicate` / `reflexivePredicate` / `functionalPredicate`. The algebraic five
are **derived** from the predicate metadata by CoreContext rules, so a `(symmetric siblingOf)` declaration
yields `(symmetricPredicate siblingOf)` and `isa? siblingOf symmetricPredicate` holds —
exactly as `isa? dog unaryPredicate` does for a type. Those rules deliberately name **no**
context and place by the ordinary rule: every context sees CoreContext, so a declaration
made there still concludes there, and one made in a context concludes in that
context rather than becoming vocabulary the whole KB reads (see "The consumers"
below).

## decontextualizedPredicate: a fact that belongs to the KB, not to one theory

`(decontextualizedPredicate P)` takes every `(P ...)` out of the context it was stated
in. Each one — asserted, or concluded by a rule — is additionally **deduced into
UniverseContext**, supported by the placement sentex *and* the
`(decontextualizedPredicate P)` sentex. Since every context sees UniverseContext,
the fact becomes visible everywhere, even from a *sibling* context that cannot see
where it was stated. Retracting or defeating either the original or the declaration
withdraws the copy through the JTMS, and declaring it retroactively lifts the `(P ...)`
facts already present.

The mechanism is documented in the KB in its own representation by an inert rule,
`(set/inertRule (implies (?pred . ?args) (ist UniverseContext (?pred . ?args))))` — the
dotted rest pattern quantifies over any predicate and its arguments (see
[inference.md](inference.md)). It is `inertRule` because the behavior is implemented
in code, so the rule is never indexed or fired; it only records the intent. The
declaration is ordinary predicate metadata, read back with
`(has-prop? kb :decontextualized pred)`.

### Why UniverseContext, and not a target the declaration names

A lift into a context the declaration picks out is the obvious generalization, and it
is unsound. The definitional checks — disjointness, functionality, `argIsa` — are
**context-scoped**: they run where the fact is stated, against what is visible from
there. Lifting into a context the stating context cannot see moves the fact somewhere
those checks never looked, and two facts that are each admissible where they were
stated meet in the target as a violation nothing reports:

```clojure
(disjoint dog mouse)
(dog Rex)   @AContext   →  copy in TContext      ; fine in A — B is invisible from A
(mouse Rex) @BContext   →  copy in TContext      ; fine in B — A is invisible from B
;; TContext now believes Rex is both, and no check ever considered the pair
```

UniverseContext is the target that closes this, because it is the one context every
context sees: the first copy is visible to the *next* assert, so the ordinary
context-scoped check catches the clash at its source, and the second assert is refused
where it is made. That is not a lucky property of a well-known context — it is the
whole reason the target is fixed.

The residual case is a context wired outside the spindle, which sees neither its
siblings nor UniverseContext. There the stating context could not have run the check
either, so the lift runs it on the copy itself (`unchecked-target?` — one `sees?` per
lift, and only that case pays anything more), dropping the copy and recording a
`violations` entry that names the context it was lifted from.

### The lift is about the predicate, so derived content is lifted too

The declaration runs at **both** points new content is stored: `assert`, and forward
chaining's `place-conclusion`. A rule concluding `(P ...)` gets its conclusion lifted
exactly as a caller asserting `(P ...)` does, because the declaration is a claim about
the *predicate*, not about how a particular sentence arrived.

That is not a convenience — lifting only asserted content makes belief depend on
arrival order, which [nmtms.md](nmtms.md) forbids. Declare, then let a rule conclude
`(P a)`: the conclusion stays where it was concluded. Let the rule conclude first and
declare afterwards: the retroactive sweep lifts it. Same three sentences, two different
answers. The engine's own invariant decides the question, and it decides it in favour
of lifting.

Each copy is a **new datum in a context that did not have it**, so it goes on the
chaining agenda and reaches the derivation-path choke point like any rule conclusion:
its arrival re-triggers any `exceptWhen` stated over that predicate, and rules keyed on
the predicate fire on the copy as well as on the original.

That second firing is the point, and it is about **placement**, not about what a rule
can see — forward chaining already matches antecedents across every context. Firing on
the original places the conclusion in the source context; firing on the copy places
it in UniverseContext. So a consequence of a decontextualized fact is decontextualized
in turn, which is what you want (if `(edgeTo A B)` holds everywhere, so does what a
universal rule concludes from it) and what it costs: **two stored sentexes for one
conclusion**, and the rule fires twice.

The fixpoint still terminates for the ordinary reason — re-deriving a sentence already
stored adds a justification, not a handle, so the agenda drains — and each copy carries
`1 + max` antecedent depth, so the `:max-depth` guard bounds a chain of lifts exactly as
it bounds a chain of rules.

Two boundaries, both deliberate:

- **A negative fact is not lifted.** `(not (P a))` has functor `not`, so a declaration
  about `P` does not reach it. The positive extent becomes universal and the negative
  one stays in its context.
- **Declaring is O(extent).** The retroactive sweep creates one copy per stored
  `(P ...)` inside a single synchronous `assert` — measured at ~0.09 ms a fact, flat, so
  a predicate with a large extent is a long assert. Declare before loading where you
  can.

### What the shipped ontology declares it of

Every shipped declaration is a claim about a **predicate** rather than about a world.
`functional`, `inverse`, `reflexive`, `symmetric`, `asymmetric` and `transitive` carry
the mark — so a `(symmetric P)` stated in one theory is the KB's claim about `P` and not
that theory's — and `genlContext` carries the forced variant below. **No domain relation
carries either**, and two things hold that line:

- **A domain fact is what a theory is for.** A marriage, an ownership, a location holds
  in the context that states it, and a story, a jurisdiction or a hypothesis is entitled
  to state one the rest of the KB does not share. A mark on `marriedTo` makes every
  fiction's marriage a claim of the whole KB.
- **The mark travels down the rules.** A conclusion drawn from a lifted copy is lifted
  in turn (above), so a mark on one predicate reaches whatever the rules over it
  conclude: `SocialContext`'s `(implies (and (marriedTo ?x ?y)) (knows ?x ?y))` would put
  `knows` within reach of every data context without `knows` being declared anything.

`abduciblePredicate` is the near-miss on the other side, and is scoped for the
converse reason: willingness to assume a `(P …)` is a policy of the context that grants
it rather than a property of `P` ([abduction.md](abduction.md)).

## forcedDecontextualizedPredicate: a canonical home in UniverseContext

`(forcedDecontextualizedPredicate P)` is the stronger variant. Instead of leaving the
original where it was asserted and deducing a copy, it **forces the storage context
of every `(P ...)` to UniverseContext** on assert — no separate justification, the fact's
extent simply lives there. `genlContext` is declared this way (the vocabulary head asserts
`(forcedDecontextualizedPredicate genlContext)` before any `genlContext` edge), so the whole context
topology has one canonical home rather than being scattered across the contexts each
edge was asserted in.

Both are wff-checked at assert time, like the other special predicates:
`decontextualizedPredicate` routes through the same `prop-problems` check as
`transitive` / `symmetric` / `functional`, since it is a one-argument mark on a
predicate like they are.

## Context-scoped constraint checks

`argIsa` arg checks and disjointness checks are **not global**: when asserting in
context K they consider only constraints and type memberships *visible from* K
(its `context-up` closure). So shared vocabulary must live in a context K sees — in the
starter, the CoreContext vocabulary and the upper definitional contexts sit at the top
of the spindle (every data context reaches them through the axis), so their `argIsa`
constraints, comments, and type memberships are visible everywhere.

The `genl` closure reads are scoped the same way (docs/taxonomy.md): `genls` /
`specs` / `genl?` / `disjoint?` take a context, and a read asked from K walks only
the edges some believed supporter asserts from K's cone.  The **`genlContext`
closure itself stays global, as a stated exception** — visibility scoped by
visibility would be circular, `forcedDecontextualizedPredicate` already forces
every `genlContext` edge universal, and the scoped reads' interning is keyed on
that closure being context-independent.  A clash no single writer could see —
admissible where each half was stated, jointly visible from some descendant — is
reported by `settle`'s exposure pass in `(violations kb)`, never by refusing a
writer on grounds it cannot see.

Under a KB's `:arbitrate` constraint policy it is also **weighed**, and by the same
scoped check: `settle` runs each candidate's definitional question from its own context
*and* from the maximal common descendant of that context and each context holding a
sentex it could pair with. That chooses the asker rather than widening what an asker
sees — a vantage already sees both halves — and it is what stops the same three
sentences from landing on a defeat or on two coexisting claims according to which half
was written last ([nmtms.md](nmtms.md)). Under `:refuse` the pass files the report and
belief is untouched.

**The pass asks its question of the scoped read, not of an enumeration.** For a
candidate pair of held memberships it must answer "does any context see both of these
*and* a complete derivation of their disjointness". Read forwards, that is a search
over derivations — one witness per ancestor path per separated pair per supporter
choice, which is exponential in a multiply-inheriting hierarchy, and a pair that turns
out *not* to be jointly visible exhausts every one of them to find out. Read
backwards it is a property of a context: `disjoint? t1 t2 K` scoped to K walks only
edges visible from K, so it is true exactly when K sees some whole derivation. So the
pass asks `∃K ∈ common-descendants(c1, c2)` off the cached closures, and enumerates a
witness only for the *report* — where one is now known to exist, so the search stops
at it rather than running out. The two directions decide the same question, and the
gate is what keeps the sweep bounded on a large ontology.

Both answers are memoized per pass on the pair `[t1 c1 t2 c2]`, which is what they
are functions of — the term appears in the reported message and nowhere else — so a
corpus where thousands of individuals hold the same two types in the same two
contexts asks once.

## The consumers, and what each of them may reach

Scoping the closure reads is half the job; the other half is every place the engine
reaches for an edge, a rule, an equality, or a metadata mark *on some context's
behalf*. `context_scoping_test` is the standing guard, one pair of tests per mechanism
— the leak and its control, since a scoping test that only checks the negative passes
just as well when the feature is broken outright.

- **A forward firing rests on three ingredients, not two** — the rule, the antecedent
  facts, and the `genl` edges the match subsumed through — and **one rule governs all
  three**: the conclusion is placed in the maximal contexts that see every one of them,
  and it **names every one of them in its justification**. A rule on `(parentOf ?x ?y)`
  matched by a stored `(fatherOf Tom Bob)` is using `(genl fatherOf parentOf)`, so
  `chain/placement-ingredients` asks `taxonomy/reach-support` for a *witness* path from
  the fact's functor up to the antecedent's, and feeds its supporters' asserting
  contexts to `maximal-common-descendant-contexts` beside the rule's and the facts'.
  Every placement that comes back sees every named edge by construction — the scoping
  guarantee is structural rather than a filter — and the witness joins the antecedent
  list, so the conclusion goes when the edge does. Both halves are load-bearing: a
  placement decided by re-deriving reachability that the justification does not then
  record leaves the conclusion standing on nothing once the edge is retracted. The
  join itself stays global (which facts exist is not
  placement's question), and the links are collected only for a matched fact whose
  functor is not the functor of the antecedent it satisfied, so an ordinary firing pays
  a `not=`.

  The witness is chosen to **constrain the placement least**, which is what makes this a
  widening of the two-ingredient rule rather than a different one. Where a maximal
  context seeing the rule and the facts can also see a path, the edges add no constraint
  and the placement is unchanged — asked per candidate, since two incomparable
  candidates may see different supporters of one edge and a single global witness would
  drop whichever cannot see it. Only where *no* candidate can is the taxonomy binding,
  and the conclusion **descends** to the maximal contexts that see the edges too. A rule
  and a fact in one context, over a hierarchy stated in a sibling, therefore
  conclude in the contexts below both instead of concluding nowhere. An `(ist Ctx S)`
  consequent is not lowered: the target is named rather than derived, so it places
  where the author said or not at all. A drop is a `:no-placement` entry naming the
  subsumption and the contexts that would have taken it but for the edges, since "your
  context cannot see that edge" is a different thing to fix from "your facts are in
  sibling contexts".

  Which fact satisfied which antecedent is not recoverable from the justification's
  handle list — the join runs in cost order — so `chain/join-antecedent` records the
  pairing as it matches (`:matched`), and `subsumption-links` reads the links off that.

  The witness is **one path, one supporter per edge**, chosen by content — the walk
  expands neighbours in name order, and per edge it takes the *most general* supporter
  available (the one every other supporter's context sees), since a needlessly specific
  choice would drag the conclusion down with it. Nothing about it depends on the order
  the hierarchy was built in. A second route — the same edge asserted from a second
  context, or a second path around it — does not carry a second justification, because
  that would be one justification per path through a hierarchy where paths multiply. It
  costs a **re-derivation** instead: the same bargain the qualitative support makes
  (docs/qcn.md), and the same one `exceptWhen` revival makes. Across *paths* the witness
  is the shortest one; a longer route through more general contexts might place the
  conclusion higher, and is deliberately not searched for.

  The same edge has to work in both time directions. Arriving **after** the facts, it
  makes them matchable at a supertype they did not have, and the semi-naive agenda
  never sees that (the arriving datum is the edge); `special/subsumption-seeds` puts
  the sub's spec subtree back on the agenda — the taxonomy twin of the retroactive
  `decontextualizedPredicate` lift, and free on the ordinary load order, where a
  hierarchy arrives before the facts under it. **Leaving**, it withdraws what it
  licensed through the ordinary dependency-directed sweep, and
  `special/resubsumption-seeds` puts the same subtree back when the reachability
  outlives the supporter that went — so the surviving route re-derives, at a fresh
  handle. `subsumption_support_test` is the standing guard for all of it.

  **A `genlContext` edge owes the same debt through the other closure**, and
  `special/visibility-seeds` is the twin that pays it. Matching fans an antecedent up the
  *visibility* cone, so an edge arriving after both the rule and the facts changes which
  facts the rule can see — and again the arriving datum is the edge, so firing the rules
  keyed on `genlContext` is not the same thing as re-joining the rules the edge just gave
  a wider view.

  It seeds **both** cones, because an edge pairs rules and facts in two directions. A
  rule below can now see facts above; and a rule stated *above* is inherited into the
  context newly wired under it, so the edge equally hands the general rule the
  context's own facts and places the conclusion there. Seeding is by fact, so the
  seeds are the believed sentexes of `super`'s up-cone together with those of `sub`'s
  down-cone.

  **It is enumerated from the rules, and each half is gated on the other holding one.**
  Both are about cost, and the cost is asymptotic rather than constant. Walking the cone
  and keeping the facts a rule could match is a record fetch per sentex *in the cone*, so
  wiring N contexts under a `UniverseContext` holding K facts is O(N·K) against
  O(N+K) without it, and a spindle D deep is O(D²) because each edge's up-cone is the
  whole chain above. Two ref-counted rosters maintained at the rule index/unindex choke
  points — `:rule-antecedents`, the predicates some rule takes as an antecedent, and
  `:rule-contexts`, the contexts rules are stated in, both beside `:opposed` and both
  replayed by `recover` — turn it around: walk those predicates' extents, keep what falls
  in the cone, and skip a half entirely when the other side holds no rule to benefit.
  Wiring an *empty* context under a full one is the commonest edge there is and now
  seeds nothing, where the ungated version re-seeded the whole ontology above it and
  re-joined rules that had already fired on every fact of it. Measured on the starter
  load: 1.80x ungated, 1.04x with both. The removal side needs no twin: dropping an edge
  *narrows* what a rule sees, and the dependency-directed sweep already withdraws a firing
  whose antecedent stopped being visible.

- **A rule is a sentex**, so a context backward-chains with the rules it inherits and
  no others (`res/rule-visible-from?`, shared by every caller of
  `provers/candidate-rules`). Without it the two chainers disagree about one KB: the
  forward firing of a sibling's rule correctly evaporates for want of a placement while
  a backward search answers from it.

- **An equality applies where it is visible on the question as well as on the answer.**
  Migration and supersession check per sentex; the *goal* rewrite has to check too, or
  an invisible `(rewriteOf Superman Clark)` renames a context's question to a
  spelling that exists nowhere and it loses a fact it still believes, under either
  name. `kb/rewrite-goal` takes the context, `different` reads the scoped partition
  (the unique-name assumption is what a context holds until *it* is told
  otherwise), and the public reads take the context too (docs/taxonomy.md).

- **`argPreserving` walks the edges the asker can see** — `inherit/witness-terms`
  scopes its `genl` walk as it already scoped its `fact-reach`, and re-reads the
  relation's transitivity from the same vantage.

- **The predicate meta-ontology concludes where it was declared.** The metadata rules
  in `kb/CoreContext.txt` place by the ordinary rule and name no context, so a
  `(symmetric myRel)` stated in a context concludes `(symmetricPredicate myRel)`
  *there*. **Do not name CoreContext in them.** Doing so publishes the conclusion: `isa?`
  would answer from a context that cannot see the declaration, while `has-prop?`, asked
  of the same declaration from the same context, answers false.

An **`(ist Ctx S)` consequent remains an explicit escape hatch** and is not scoped —
that is what it is for. A rule author writing one is choosing the target, the same way
`forcedDecontextualizedPredicate` chooses UniverseContext; the engine holds them to
the subsumption check above and nothing else.

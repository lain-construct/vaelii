# Argument-position preservation

`(largerThan dog cat)` says something about two *kinds*. Whether it also says something
about `golden_retriever` and `maine_coon` is not decidable from the sentence — it
depends on whether the relation distributes over the kinds' subkinds. Some relations do:
`disjoint` is closed under `genl`, and subtypes of disjoint types are disjoint. Some
emphatically do not: `chihuahua` is a kind of dog, `maine_coon` a kind of cat, and the
maine coon is bigger.

So it is **declared**, per predicate, per argument position:

```clojure
(argPreserving        P n R)   ; a stored (P … W …) licenses (P … A …) when (R A W)
(argPreservingInverse P n R)   ; …licenses it when (R W A)
```

`R` is any **transitive** relation — `genl` and `genlContext` through their cached
closures, or a predicate declared `(transitive R)` walked over the stored facts. With
`R` = `genl`, `argPreserving` is downward inheritance and `argPreservingInverse` is
upward.

Naming the relation is what keeps this from being a `genl` special case. An argument can
be preserved along `partOf` just as readily:

```clojure
(transitive partOf)
(partOf Engine Car)  (partOf Piston Engine)
(argPreserving needsMaintenance 1 partOf)
(needsMaintenance Car)
;; => (needsMaintenance Piston)   two hops, no types involved
```

The inverse form exists so the other direction never requires declaring an inverse
predicate that has no other purpose. Both are ordinary stored sentexes read through
`matches-visible`, exactly as `argIsa` and `argGenl` are — context-scoped and
belief-following, with no cache of their own. Several declarations may name **one**
position; their reaches union, since each independently licenses the claim.

## Two of them ship

`largerThan` and `partType` are in the starter (`resources/kb/upper/AbstractContext.txt`), and the
pair is worth comparing because they are declared **differently on purpose**:

```clojure
(argPreserving largerThan 1 genl)   (argPreserving largerThan 2 genl)
(argPreserving partType   1 genl)
```

`largerThan` preserves on both positions, so `(largerThan mammal insect)` in
`SizeContext` answers `(largerThan dog ant)` with nothing stored about dogs or ants.
`partType` preserves on the **first only**: a kind of bird has whatever parts birds have,
so `(partType bird wing)` answers `(partType penguin wing)` — but birds having wings says
nothing about which *kinds of wing* they have, so position 2 preserves nothing. Each
position is a separate claim about the relation, and this is what that looks like when
somebody has actually made both decisions.

The size claims are also where the sharp edge shows. Preservation runs downward and
`largerThan` is asymmetric, hence irreflexive — so a claim relating a kind to one of its
own subkinds would license `(largerThan K K)` and contradict itself. `(largerThan mammal
mouse)` is not a fact this ontology can hold, however true it sounds; every pair in
`SizeContext` is between kinds that are not `genl`-related, and that is a requirement
rather than a coincidence.

## The transitivity has to have been declared

The reach is walked to a **fixpoint**, so naming a relation nobody said composes would
manufacture transitivity for it — two hops of `begat` licensing a claim only one hop was
ever evidence for. `assert` refuses the declaration:

```clojure
(argPreserving cursed 1 begat)
;; => throws :not-well-formed
;;    "begat is not transitive, and argPreserving walks the relation it names to a
;;     fixpoint — declare (transitive begat) before the preservation, or name one of
;;     genl / genlContext"
```

The refusal lives in `wff` rather than in `(argIsa argPreserving 3 transitivePredicate)`
because `argIsa` is **open-world**: an argument with no type cannot violate it, so the
constraint bites for a relation that happens to carry some other type and waves through
the one that carries none — and naming the relation before typing it is the common
authoring order. The check is also read at *use*, not only at assert, so retracting
`(transitive R)` withdraws the inheritance it licensed: the declaration is still stored,
but a relation nobody currently says composes is one whose reach we have no right to
close.

Because the check reads the store, it is sensitive to what has arrived — which a KB
**file** must not be, since its blocks run in term order and cannot also run in
dependency order. `seed/load-sentences` retries a sentence refused for what has not
arrived yet, and throws only once a round changes nothing, so where an author filed a
sentence is not a property of the knowledge.

## From whose vantage

Everything here is read from the asking context. The declarations come through
`matches-visible`; `witness-terms` walks the `genl` closure **scoped** to the vantage,
so a claim travels the subtype edges the asker can see and no others; and
`usable-relation?` reads `(transitive R)` from there too — a transitivity some invisible
microtheory declares is not a licence this one holds. `genlContext` is the stated
exception and stays global: the context topology is what [taxonomy.md](taxonomy.md)
describes, and a preservation along it is a claim about that topology.

The assert-time refusal is deliberately **unscoped**, and the two are not in tension.
It asks the structural question — is this relation declared transitive anywhere — so a
writer is not refused for a declaration whose transitivity lives somewhere it cannot
see. What that writer may then *do* with it is the read's question, asked again from
each vantage, and answered there by walking nothing.

## Preservation stays on one side of the type/instance line

`genl` relates types, so a claim preserved along it reaches subkinds and stops. It says
nothing about Rex and Whiskers, and that silence is the semantics rather than a gap.
`relationKind` is a `disjointMetatype` over `typeRelationPredicate` and
`instanceRelationPredicate` — one predicate symbol relates kinds *or* instances, never
both — so a `largerThan` that inherited across the line would be a predicate of both
kinds at once, which the meta-ontology refuses.

Preservation moves an **argument** along a relation; the predicate, and the level it
relates at, are left alone. Crossing the line is a different claim: it links two
predicates and has a quantifier reading to pin down (every member? some member?). The
vocabulary for it is `(typeToInstancePred TypePred InstancePred)` — declared in
CoreContext and **deliberately inert**: it records the pairing for a reader and the
engine infers nothing from it, because the quantifier reading is exactly the thing
nothing here fixes.

## Specificity, and why it is not the deleted axis

The interesting case is a claim that inherits *and* a more specific claim that
disagrees. `(typicallyLargerThan dog cat)` reaches `[chihuahua maine_coon]`;
`(typicallyLargerThan maine_coon chihuahua)` is stated directly. The stated one wins,
and the general one **does not fire for that pair** — undercutting, not defeat. Nothing
is derived, so there is nothing to arbitrate, and `contradictions` stays empty.

That distinction matters, because it is what keeps genl-based specificity out of
*arbitration*. Scoring a type by the size of its up-closure is inference **about** the
knowledge rather than **from** it — a numeric proxy that ties silently whenever the
exception is not keyed on a narrower type — and [nmtms.md](nmtms.md) is where the two
defeat classes stop.

Nothing here reconstructs an ordering. Two claims are compared along the very relation
the inheritance travels down — `[maine_coon chihuahua]` is below `[cat dog]` because
`(genl maine_coon cat)` and `(genl chihuahua dog)` are edges the KB holds. Claims that
are genuinely incomparable are not ranked at all: they come back `:ambiguous` and the
prover answers nothing, which is the same thing the engine does with every other
unresolvable clash.

## Strict versus typical, from the strength that was already there

A **`:monotonic`** claim is never undercut. Strength already propagates from a
justification's antecedents, so the two behaviours fall out of how the general claim was
asserted, with no second declaration:

```clojure
(asymmetric largerThan)
(argPreserving largerThan 1 genl)  (argPreserving largerThan 2 genl)

(largerThan dog cat)                        {:strength :monotonic}
(largerThan maine_coon chihuahua)           ; => throws :asymmetric
;   "largerThan cannot hold both ways, and (largerThan dog cat) is known true
;    (which reaches (largerThan chihuahua maine_coon) by argument preservation)"
```

```clojure
(asymmetric typicallyLargerThan)
(argPreserving typicallyLargerThan 1 genl)  (argPreserving typicallyLargerThan 2 genl)

(typicallyLargerThan dog cat)               ; the default :default
(typicallyLargerThan maine_coon chihuahua)  ; => accepted
;; (typicallyLargerThan chihuahua maine_coon)  => false, overridden
;; (typicallyLargerThan dog cat)               => still true
;; (typicallyLargerThan golden_retriever siamese) => true, untouched pairs still inherit
```

Accepted, but not *unremarked*. Where the specific claim genuinely overrides the
inherited one there is nothing to report — the general claim is undercut and never
fires, so no pair exists. Where two claims at equal defeat class really do contradict
each other — `(typicallyLargerThan dog cat)` beside a directly-stated
`(typicallyLargerThan cat dog)` — the pair is a **nogood** like any other, and `settle`
reports it in `(contradictions kb)` with `:kind :asymmetric`. See
[nmtms.md](nmtms.md), "Which door the content came through".

Same vocabulary, same declarations. Known-true content is the fixed background, so
contradicting it is an error; a `:default` generality is something a more specific
statement is entitled to override. The difference is stated on the claim, where it
belongs, rather than split across two predicates in the ontology.

## `(asymmetric P)`

Predicate metadata beside `transitive` / `symmetric` / `reflexive` / `functional`:
`(P a b)` and `(P b a)` cannot both hold, so `P` is irreflexive too. It does two things.

It gives the **converse the standing to deny a claim**, which is what makes the override
above work at all — `(typicallyLargerThan maine_coon chihuahua)` counts as evidence
against the inherited `(typicallyLargerThan chihuahua maine_coon)` only because the two
cannot both hold.

And it makes a strict order **detectable**. Without it, `(largerThan dog cat)` and
`(largerThan cat dog)` coexist silently — zero conflicts, both believed — and with
`(transitive largerThan)` on top you get `(largerThan dog dog)` and nothing objects.
With it, the second claim is judged against the first's **defeat class**, whether the
first was stated directly or reached by preservation: known-true, and it is refused;
merely believed, and the two are admitted as a represented dilemma. Either way the KB
stops holding both directions in silence, which is the whole point of the
declaration.

## Reading it back

`ArgPreservingProver` answers a **ground** goal; an open argument is left to the fact
and rule provers, in the shape `different` and the NAF operators already use.
Enumerating one would mean walking the inverse reach of every stored witness, which is a
much larger question than the one a closed goal asks. `cost :compute`, `completeness
60` — it augments facts and rules rather than replacing them, since a preserved
predicate is still an ordinary predicate whose claims can be stored and derived
directly.

`vaelii.impl.inherit/verdict` is the whole semantics in one function: `:for`,
`:against`, `:ambiguous`, or nil when the predicate declares no preserved position.

Being answered at all is not the same as being *reached*. `ArgPreservingProver` sits in
a registry where a prover claiming `completeness 100` runs alone, and a computed answer
— a taxonomy closure, an arithmetic comparison, a constraint network — cannot contain a
claim nobody stored. So `provers/sole-prover` asks `provers/shadowing-channels` before
letting any claimant run alone, and a declared preserved position puts `:preserving` in
that set, which sends the goal down the union path where this prover is consulted.
Without it, declaring `(argPreserving partOfRegion 1 genl)` beside a registered `:rcc8`
reasoner leaves the declaration inert and `query-plan` listing a prover that never runs.

That read is on the hot path, and it is gated twice over. `positions` is asked by
`ArgPreservingProver.applicable?` *and* by `shadowing-channels`, so it runs for every
goal's functor in the KB, and each real read is two `matches-visible` calls. So
`declared-about?` answers first: a cardinality read on the declaration functors' roots,
false for nearly every KB there is, and only then an intersection with the argument
root at position 1 — where a declaration's predicate sits — which is exact in the
negative direction whatever anyone believes. Ungated, **one** declaration anywhere made
a `genl` goal cost 2.8× what it costs in a KB with none (14.5 µs → 40.4 µs), a tax
every query paid for a feature almost none of them use. Gated, the two cases are 16 µs
and 21 µs, and the difference is the declared predicate's own read.

## What one question costs

A claim bearing on `(P a b)` is a stored sentence whose argument tuple lies in the
**product** of the preserved arguments' reaches. There are two ways to intersect a
product with a store, and which is cheaper is a property of the KB rather than of the
feature:

- **enumerate the product** and probe each tuple — cost: the product, i.e. `reach^k`;
- **read the extent** of the predicate with a variable at every preserved position and
  keep the tuples that land in the product — cost: what was written about that
  predicate.

`found-claims` weighs one against the other per goal: the functor root's cardinality,
narrowed by the most selective pinned argument position, against the product's size.
The pinned position is read at the place the probe will actually **put** it, which is
not always the tuple index — the converse an asymmetric predicate is denied by swaps
them, so a term pinned at tuple index 0 is looked up at argument position 2, and
counting it at position 1 would price a probe nobody is about to make.

Both paths go through `matches-visible`, so subsumption through a sub-predicate, the
symmetric mirror, context visibility and belief are the same set either way — the
choice is retrieval, never semantics, and `inherit_oracle_test` holds the two against
each other on randomized taxonomies (`inherit/*retrieval*` forces one or the other).

That turns the cost from *how deep is the taxonomy* into *how many claims were
written*, which is the quantity the answer actually depends on. Measured by `lein
bench-inherit` on a 32-deep chain with one stored claim, `v/ask?` on a ground goal:

| preserved positions | tuples in the product | product-driven | as it runs |
|---|---|---|---|
| 1 | 32 | 0.380 ms | 0.123 ms |
| 2 | 1,024 | 10.284 ms | 0.142 ms |
| 3 | 32,768 | 323.966 ms | 0.104 ms |

Flat in both the taxonomy's depth and the number of preserved positions, because
neither is what it reads any more.

Two smaller multipliers sit under that, and both are removed by one memo
(`inherit/*memo*`, opened by `with-memo` and reused when a caller already holds one —
the discipline `observe/*reach-memo*` follows for the transitive closure). `positions`
is asked by `applicable?`, `verdict`, `surviving` and `claims`, and each computation is
two `matches-visible` calls; `witness-terms` is asked once per preserved position and
then again per *pair* of claims inside `undercut?`, and for a fact-relation each walk is
a `matches-visible` per node. Neither answer can change while one question is being
answered — a query never mutates belief — so the memo lives for the question and needs
no invalidation protocol. A KB that declares no preservation reaches none of this: an
O(1) gate on the declaration functors having any extent at all sits in front of
`positions`.

`ArgPreservingProver`'s `est-bindings` is **1**, and that is the answer count rather
than the cost — a closed goal has at most the one empty solution. `cost :compute` is
where the work shows.


## Three things that follow from reading claims out of belief

**Every probe per tuple is made, and one tuple can yield several claims.** A KB can hold
both `P` and `(not P)` of one pair — that is a represented dilemma, believed on both
sides and reported by `(contradictions kb)`. Stopping at whichever probe answered first
would read it here as a clean `:for` and hand `verdict` a decision the engine refuses to
make about the very same two sentexes. Collecting both sends it on as the `:ambiguous`
it is, and the prover then answers nothing. The two `:against` sources — an explicit
negation, and an asymmetric predicate's converse — stay separate rather than folding,
since they can be believed at different strengths and undercutting reads that per claim.

The converse is not read at a **self** tuple `[a a]`, where it is the same sentence as
the positive: that would file one sentex on both sides and manufacture a dilemma out of
a single fact. `(P a a)` under an asymmetric `P` is wrong — asymmetry implies
irreflexivity — but it is wrong in a way `contradictions` does not report either, and
inventing a verdict here is not this function's job.

**The strongest visible claim decides, not the first one found.** One sentence can be
stated in several contexts the asker can see, at different strengths, and its
defeat-class is what settles both whether a specific claim may undercut it and whether
`checks/asymmetry-problem` refuses. Reading that class off whichever handle the index
happened to yield first would key an *admission* on arrival order — handles are allocated
in assertion order — so `strongest-per-tuple` takes the maximum over the class lattice,
and breaks the ties that leaves on the context **name**. Both are functions of content alone.

**A `genl` edge between two types can flip an exception stated over a predicate neither
type appears in.** `ArgPreservingProver` sits in the level-6 stack that `exceptWhen` and
`unknown` evaluate through, and it answers by walking the *arguments'* reach — so
`(genl chihuahua dog)` changes whether `(largerThan chihuahua maine_coon)` holds, and
with it whether a rule excepted on `largerThan` fires. The re-check index is keyed on the
exception's own predicate and its supertypes, which cannot see that: without an
argument-side trigger the firings that predate the edge keep a conclusion the firings
after it correctly drop, and which you get depends on when the edge arrived.

`special/recheck-preserving-along` closes it. Whenever the extent of a relation `R` moves
— a fact on it, or a `genl` / `genlContext` edge — every rule whose exception mentions a
predicate declared `(argPreserving P n R)` is queued for re-evaluation at the next
`settle`. Queued as `:all` rather than with the moved sentence as a narrowing trigger,
because that sentence is about `R` and the exception is about `P`, so it could not narrow
the right firings anyway. The declarations are read off the functor roots rather than
through `matches-visible` — a trigger has to be conservative in the direction the answer
is, and a declaration this edge cannot see still qualifies a rule in a context that can.
Over-queueing costs a level-6 query at the next settle; under-queueing is a wrong belief.

**And the licence moves too, with no extent moving at all.** Three sentences decide
whether this prover finds anything, and none of them is on `P` or on `R`:
`(argPreserving P n R)` is the declaration itself, `(transitive R)` is what
`usable-relation?` reads at *use*, and `(asymmetric P)` is what gives a converse the
standing to deny a claim — without it the specific `(typicallyLargerThan maine_coon
chihuahua)` is inert and undercuts nothing. Each is read by `special/recheck-declaration`,
which takes the subject predicate off argument 1 and queues on its `genls` closure;
`(transitive R)` takes a second posting through `recheck-preserving-along`, since it
licenses the inheritance for every `P` declared along `R` and names none of them.
[exceptions.md](exceptions.md) has the general shape, of which this is one of three
instances.

The whole path is gated on some rule carrying an `exceptWhen` at all, and then on the
declaration functors having a non-empty extent, so a KB using one feature and not the
other pays a set-cardinality read.

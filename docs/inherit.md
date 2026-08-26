# Argument-position preservation

- **Covers:** how `transitiveInArg` / `transitiveInArgInverse` license carrying a stated claim
  about one argument across a transitive relation, how a specific claim undercuts
  rather than defeats a general one, and what is reported when it may not undercut one.
- **Not here:** matching a unary type antecedent against a subtype's stored fact —
  automatic, undeclared → [taxonomy.md](taxonomy.md); `arg` / `genlArg` minted as a
  justified fact from a type declaration → [argtypes.md](argtypes.md).
- **Assumes:** `genl`, transitive predicates, defeat-class, justification →
  [glossary.md](glossary.md).

`(largerThan dog cat)` says something about two *kinds*. Whether it also says something
about `golden_retriever` and `maine_coon` is not decidable from the sentence — it
depends on whether the relation distributes over the kinds' subkinds. Some relations do:
`disjoint` is closed under `genl`, and subtypes of disjoint types are disjoint. Some
emphatically do not: `chihuahua` is a kind of dog, `maine_coon` a kind of cat, and the
maine coon is bigger.

So it is **declared**, per predicate, per argument position:

```clojure
(transitiveInArg        P n R)   ; a stored (P … W …) licenses (P … A …) when (R A W)
(transitiveInArgInverse P n R)   ; …licenses it when (R W A)
```

`R` is any **transitive** relation — `genl` and `genlCx` through their cached
closures, or a predicate declared `(transitive R)` walked over the stored facts. With
`R` = `genl`, `transitiveInArg` is downward inheritance and `transitiveInArgInverse` is
upward. With `R` = `genlCx` the preserved argument **names a context**, and the
same two directions read the lattice: a claim about a wide context reaches every
context below it — a decree stated of a whole world holds in each of its scenarios —
and the inverse form carries a claim about a narrow context up to the ones above it.

Naming the relation is what keeps this from being a `genl` special case. An argument can
be preserved along `partOf` just as readily:

```clojure
(transitive partOf)
(partOf Engine Car)  (partOf Piston Engine)
(transitiveInArg needsMaintenance 1 partOf)
(needsMaintenance Car)
;; => (needsMaintenance Piston)   two hops, no types involved
```

The inverse form exists so the other direction never requires declaring an inverse
predicate that has no other purpose. Both are ordinary stored sentexes read through
`matches-visible`, exactly as `arg` and `genlArg` are — context-scoped and
belief-following, with no cache of their own. Several declarations may name **one**
position; their reaches union, since each independently licenses the claim.

A declaration is read for the goal's **own** predicate. It no more descends to a
sub-predicate than `transitive` or `symmetric` does: distribution over subkinds is a
claim about the relation that has it, and `muchLargerThan` may fail to distribute
where `largerThan` distributes. The sub-predicate's *facts* still serve the
super-predicate's goals — the claim reach fans through `matches-visible` like every
read — so the asymmetry is the semantics: facts travel up the predicate hierarchy,
licences do not travel down it.

## Four predicates ship with one

`largerThan` and `partType` are in `resources/kb/upper/CxAbstract.txt`, `capabilityType`
and `hasCapability` in `resources/kb/upper/CxLife.txt`. The first two are worth comparing
because they are declared **differently on purpose**:

```clojure
(transitiveInArg largerThan 1 genl)   (transitiveInArg largerThan 2 genl)
(transitiveInArg partType   1 genl)
```

`largerThan` preserves on both positions, so `(largerThan mammal insect)` in
`CxSize` answers `(largerThan dog ant)` with nothing stored about dogs or ants.
`partType` preserves on the **first only**: a kind of bird has whatever parts birds have,
so `(partType bird wing)` answers `(partType penguin wing)` — but birds having wings says
nothing about which *kinds of wing* they have, so position 2 preserves nothing. Each
position is a separate claim about the relation, and this is what that looks like when
somebody has actually made both decisions.

The capability pair is where the **inverse** form ships, and one predicate carries both
directions at once:

```clojure
(transitiveInArg        capabilityType 1 genl)   (transitiveInArgInverse capabilityType 2 genl)
(transitiveInArgInverse hasCapability  2 genl)
```

Position 1 of `capabilityType` carries a claim about a kind *down* to its subkinds — a
kind of bird flies with nothing written about it — while position 2 of both predicates
carries it *up* the capability hierarchy: flying is a kind of travelling, so whatever
flies travels.

The size claims are also where the sharp edge shows. Preservation runs downward, so
`(largerThan mammal mouse)` reaches every pair below it and lands on `(largerThan mouse
mouse)` — a kind reported larger than itself, which is not what `largerThan` is for.
`(largerThan mammal mouse)` is therefore not a fact this ontology can hold, however true
it sounds; every pair in `CxSize` is between kinds that are not `genl`-related, and that
is a requirement rather than a coincidence.

The requirement is the modeller's, and the engine does not enforce it: `(asymmetric P)`
convicts against a believed **opposing** claim, and a self tuple has none, so nothing is
refused and `contradictions` stays empty. Asymmetry does not give you irreflexivity here
([taxonomy.md](taxonomy.md)), which is exactly why the pairs have to be chosen rather
than checked.

## The transitivity has to have been declared

The reach is walked to a **fixpoint**, so naming a relation nobody said composes would
manufacture transitivity for it — two hops of `begat` licensing a claim only one hop was
ever evidence for. `assert` refuses the declaration:

```clojure
(transitiveInArg cursed 1 begat)
;; => throws :not-well-formed
;;    "begat is not transitive, and transitiveInArg walks the relation it names to a
;;     fixpoint — declare (transitive begat) before the preservation, or name one of
;;     genl / genlCx"
```

The refusal lives in `wff` rather than in `(arg transitiveInArg 3 transitive)`
because `arg` is **open-world**: an argument with no type cannot violate it, so the
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
context declares is not a licence this one holds. `genlCx` is the stated
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
CxCore and **deliberately inert**: it records the pairing for a reader and the
engine infers nothing from it, because the quantifier reading is exactly the thing
nothing here fixes.

**It cannot state a pair whose instance half is mixed**, and the shipped ontology holds
one. `(arg typeToInstancePred 2 instanceRelationPredicate)` requires the second
argument to be marked, and a marked predicate takes one argument-check family for *every*
position — `arg` throughout for an instance relation, `genlArg` throughout for a type
one. A predicate relating one individual to a *kind* satisfies neither and is left
unmarked, which `relationKind`'s own comment says of `result` and
`functionCorrespondingPredicate`. `hasCapability` is the third: one animal, one capability
kind. So `capabilityType`/`hasCapability` are named as a pair in their comments and not by
the predicate that exists to name pairs — declaring the mark to satisfy it would trade an
argument check that convicts for a link nothing reads. `partType`/`partOf` is the pair the
link does state, both halves relating individuals to individuals.

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
(transitiveInArg largerThan 1 genl)  (transitiveInArg largerThan 2 genl)

(largerThan dog cat)                        {:strength :monotonic}
(largerThan maine_coon chihuahua)           ; => throws :asymmetric
;   "largerThan cannot hold both ways, and (largerThan dog cat) is known true
;    (which reaches (largerThan chihuahua maine_coon) by argument preservation)"
```

```clojure
(asymmetric typicallyLargerThan)
(transitiveInArg typicallyLargerThan 1 genl)  (transitiveInArg typicallyLargerThan 2 genl)

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

## A contrary claim against a known-true one is a contradiction, and is reported

`(asymmetric P)` is what gives a converse the standing to deny a claim, so the paragraph
above is about predicates that carry the mark. The plain case needs no mark at all: a
stored `(not (P a b))` denies an inherited `(P a b)` outright, and `undercut?` is what
decides whether anything follows from that. A `:default` general claim yields — it is
undercut, does not fire for that tuple, and there is no pair. A `:monotonic` one is not
undercut, which is exactly the case its docstring calls **a contradiction to report
rather than a refinement to defer to**.

`settle/preserving-nogoods` forms that pair. It cannot form it the way every other
rebuttal is formed, because the `:opposed` set holds bodies stored in *both* polarities
and here the body is stored in one — the other side is a claim with no handle, read out
of somebody else's tuple. So the nogood's members are the stored claim **and everything
the reading rests on**:

- the general claim actually stated — `(carriesLoad hauler_kind Bone1)`;
- the declaration licensing the move — `(transitiveInArg carriesLoad 1 genl)`;
- the relation edges the reach travelled — `(genl cart_kind hauler_kind)`;
- and, for a fact-relation, the `(transitive R)` `usable-relation?` reads at use; for a
  mirrored reading, the `(symmetric …)` behind the mirror.

The same list `support-for` hands a justification, and for the same reason: those
sentexes are what the claim *is*, so a set that must not hold in full is that set and not
a pair inside it. The report carries `:kind :inherited` and an `:inherited` map naming the
claim nobody wrote, the handle it was read off and the handles it travelled — enough for
`why` to explain a report about a sentence the KB does not store
([nmtms.md](nmtms.md) has the entry shape).

**The belief consequence falls straight out of that, and no rule is invented for it.**
`decide-nogood` defeats the strictly-weakest member of any nogood, and this one is
weighed the same way, so the answer is the strength ordering the rest of the engine
already runs on:

| the reading | the stored contrary claim | what happens |
|---|---|---|
| `:default` general claim | any | undercut — no pair, nothing reported |
| every member known-true | `:default` | the stored claim is the unique weakest and is **defeated**: the general claim reaches the subkind and the nearer default does not stop it |
| a `:default` declaration or edge in it | `:default` | the floor is shared — a represented dilemma in `(contradictions kb)`, believed on both sides |
| every member known-true | `:monotonic` | an irreducible clash in `(conflicts kb)` |

The middle two rows are one rule read twice, and the rule is the one a firing's strength
already follows: **a reading is capped by its weakest link.** A `:monotonic` claim carried
by a `:default` declaration draws a `:default` conclusion through the forward door (below),
and it wins no argument a `:default` claim would lose through this one either. So a KB
whose taxonomy edges and declarations are ordinary defaults — which the shipped ontology's
are — gets the dilemma: what the engine has no grounds to choose between is *which* of the
declaration, the edge and the stored claim to give up, and choosing would be inventing an
ordering. A KB that states the reading as known-true gets the defeat, and the general
claim then answers `ask?` at the subkind.

Nothing about this is a second defeat axis. Specificity still decides who may undercut
whom, and defeat class still decides everything else; what changed is that a pair the
engine could not name now has a name.

**The pair is judged from the stored claim's own context**, which is the vantage the
inherited claim exists in at all: a claim reaches the contexts that can see it and no
others. So a general claim stated in a context the stored one cannot see denies nothing,
and two contexts neither of which sees the other pair nothing — the reading the `:refuse`
constraint policy takes for a definitional clash split across a visibility edge
([nmtms.md](nmtms.md), "Who asks the pair's question").

**The diagonal is excluded**, as it is for `support-for`: `witness-terms` is reflexive, so
the claim stated at the very tuple the stored negation is about comes back through the
reach too — and that pair is an ordinary `P` beside an ordinary `(not P)`, which
`negation-nogoods` already forms. Reporting it here as well would report one pair twice.

## `(asymmetric P)`

Predicate metadata beside `transitive` / `symmetric` / `reflexive` / `functional`:
`(P a b)` and `(P b a)` cannot both hold. It does two things — and refusing `(P a a)` is
not among them, because the check needs a believed opposing claim and a self tuple has
none ([taxonomy.md](taxonomy.md)).

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

The mark is read for the sentence's predicate **and every super-predicate of it**
(`tax/props-over`), because `(fatherOf a b)` beside `(parentOf b a)` is two `parentOf`
tuples one way round each, and `(asymmetric parentOf)` denies exactly that. The converse
is then probed at the marked predicate — `(parentOf b a)`, whose match fans down over
`parentOf`'s specs and so finds the claim under either spelling — where probing
`(fatherOf b a)` would miss one written generally. This is the **constraint** direction
and it is the opposite of the one below: a mark that convicts descends, a mark that
licenses does not.

## Reading it back

`TransitiveInArgProver` answers a **ground** goal; an open argument is left to the fact
and rule provers, in the shape `different` and the NAF operators already use.
Enumerating one would mean walking the inverse reach of every stored witness, which is a
much larger question than the one a closed goal asks. `cost :compute`, `completeness
60` — it augments facts and rules rather than replacing them, since a preserved
predicate is still an ordinary predicate whose claims can be stored and derived
directly.

`vaelii.impl.inherit/verdict` is the whole semantics in one function: `:for`,
`:against`, `:ambiguous`, or nil when the predicate declares no preserved position.

Being answered at all is not the same as being *reached*. `TransitiveInArgProver` sits in
a registry where a prover claiming `completeness 100` runs alone, and a computed answer
— a taxonomy closure, an arithmetic comparison, a constraint network — cannot contain a
claim nobody stored. So `provers/sole-prover` asks `provers/shadowing-channels` before
letting any claimant run alone, and a declared preserved position puts `:preserving` in
that set, which sends the goal down the union path where this prover is consulted.
Without it, declaring `(transitiveInArg partOfRegion 1 genl)` beside a registered `:rcc8`
reasoner leaves the declaration inert and `query-plan` listing a prover that never runs.

That read is on the hot path, and it is gated twice over. `positions` is asked by
`TransitiveInArgProver.applicable?` *and* by `shadowing-channels`, so it runs for every
goal's functor in the KB, and each real read is two `matches-visible` calls. So
`declared-about?` answers first: a cardinality read on the declaration functors' roots,
false for nearly every KB there is, and only then an intersection with the argument
root at position 1 — where a declaration's predicate sits — which is exact in the
negative direction whatever anyone believes. Ungated, **one** declaration anywhere made
a `genl` goal cost roughly 3× what it costs in a KB with none (~15 µs → ~40 µs), a tax
every query paid for a feature almost none of them use. Gated, the two cases are ~16 µs
and ~21 µs, and the difference is the declared predicate's own read.

## Forward chaining on a claim nobody stored

A forward rule's antecedents are matched against stored facts, and an inherited claim is
not one. So the two doors into the same knowledge answered differently: `ask` reached
`(largerThan chihuahua maine_coon)` through the prover above, while the fixpoint fired
`(implies (largerThan ?x ?y) (outweighs ?x ?y))` on the claims that were written and on
nothing else, and `sentexes-matching` read that back. The engine treats a
forward/backward disagreement as a defect elsewhere — `provers/exception-holds?` is one
shared function precisely so an exception cannot block a rule one way and not the other
— and three further things followed from the conclusion never being derived: `why` could
not explain an answer `ask` was confident about, retraction did not reach it, and it
could not be an antecedent of anything.

Support is what closes it, exactly as it does for a relation a constraint network
entails ([qcn.md](qcn.md)). An inherited claim has no handle, but it was **read from**
things that do:

- the **claim that was stated** — `(largerThan dog cat)`;
- the **declaration** licensing the move — `(transitiveInArg largerThan 1 genl)`, one per
  position that actually moved;
- the **relation edges** the reach travelled — `(genl chihuahua dog)`, `(genl maine_coon
  cat)`, one shortest path per position;
- and, for a fact-relation, the `(transitive R)` that `usable-relation?` reads at use,
  since withdrawing it withdraws the reach with no fact having moved.

`inherit/support-for` answers a ground goal with that list and
`inherit/solve-with-support` hands it to `chain/join-antecedent`, which contributes the
handles as antecedents of the firing. So the conclusion is withdrawn when any of them
goes, `why` names the actual reasons, and the conclusion is placed only where all of
them can be seen — the contract an ordinarily matched antecedent has.

```clojure
(transitiveInArg largerThan 1 genl)  (transitiveInArg largerThan 2 genl)
(largerThan dog cat)
(implies (largerThan ?x ?y) (outweighs ?x ?y))

(v/ask? kb '(outweighs chihuahua maine_coon) C)              ; => true
(v/sentexes-matching kb '(outweighs chihuahua maine_coon) C) ; => the derived sentex
```

**A closed antecedent asks one question; an open one enumerates.** A rule whose other
antecedents bind the variables first reaches the preserved literal ground, and it is the
same question `ask` asks. A literal still open — the example above, where the rule has
one antecedent and nothing has bound it — runs the reach the other way: every believed
claim of the predicate, the tuples that claim licenses, and then the full semantics
asked per tuple. So a tuple is *found* by the reach and *admitted* by `surviving`, and a
forward antecedent can no more join on an undercut or disputed claim than `ask` can
answer one. That enumeration is the walk this file declines to make for an open *goal*
(above), and the forward join is the caller for which it is the right one: a conclusion
has to be drawn per tuple whether or not anybody asked.

**Union, not replacement.** The ordinary matcher still runs, so nothing that fired
before stops firing, and duplicate justifications from the two routes are set-deduped by
the TMS. The **diagonal** is dropped from the inherited path: `witness-terms` is
reflexive, so a claim stated at the very tuple it is asked about comes back through the
reach too, and it already carries the ordinary matcher's justification — a second one
naming the same claim plus a declaration and no edge would rest on nothing the first did
not.

Five more things follow, and each needed its own wiring.

**The trigger index cannot connect any of it.** A rule is fired by a datum whose
predicate keys it, and `(genl chihuahua dog)` licenses a `largerThan` antecedent with
neither of its terms appearing anywhere near `largerThan`. Nor is a claim on the
predicate itself enough on its own: `(largerThan dog cat)` unifies with the antecedent at
the one tuple it is *stated* at, and the tuples it licenses are reached by joining rather
than by matching. So such a datum **re-joins in full** every forward rule carrying an
antecedent on a preserved predicate whose licensed set it moved, and those rules leave
the trigger set so the work is done once (`inherit/rejoin-rules`,
`chain/rejoin-in-full`). A `(symmetric P)` declaration takes the same route for a
different reader — it moves what the *matcher* answers rather than what a prover does,
and the facts it now pairs have already arrived (`chain/symmetric-rejoin-rules`). The
sentences that move a preserved predicate are the declaration itself, a
claim on the predicate, a fact on the relation — a `genl` or `genlCx` edge included
— `(transitive R)`, and `(asymmetric P)`.

**A defeat inside arbitration moves the same joins with no sentence arriving at all.**
Belief flips where the solver clears a dilemma, nothing is stored or removed, and so
nothing queues the re-join an arrival would. `settle`'s `preserved-rejoins-for` reads the
rules each defeated sentence licensed and re-chains them like any blanket mark, so a
firing whose named witness went OUT either re-derives through a route that witness did not
travel or is withdrawn by its own re-check. The closures are refreshed at the same point
(`refresh-after-defeat`, the mirror of the revival refresh `settle*` opens with, scoped by
`jtms/touched` the same way) — otherwise the rest of the settle walks a closure still
holding the defeated edge, and the next defeat round's nogoods read belief as it was.

**A mirrored antecedent licenses the forward door too, and the firing says so.** A claim
whose stored orientation is not the tuple it was read at came through the symmetric
mirror, and that reading rests on a `(symmetric …)` declaration exactly as a fact-relation
reach rests on `(transitive R)` — so the justification names it, and retracting the
symmetry withdraws what only the mirror licensed. The matcher mirrors each fanned literal
on *its own* declaration, so the one named is the stored sentence's functor's, which is
the goal predicate's only where the two coincide; a symmetry declared on a sub-predicate
therefore moves every preserved super it feeds.

**A more specific contrary claim withdraws a conclusion with nothing retracted.**
`(typicallyLargerThan maine_coon chihuahua)` undercuts the inherited
`(typicallyLargerThan chihuahua maine_coon)`, and the general claim is not defeated: it
simply does not fire for that pair. Every antecedent of the firing is still stored and
believed, so the justification cannot express the withdrawal. The firing is **blocked**
the way an `exceptWhen`-excepted one is (`chain/inheritance-withdrawn?`, queued by
`special/recheck-preserving-firings`), which means the existing sweep collects the
conclusion and the existing revival machinery brings it back when the specific claim
goes. The check is asked only of an antecedent the KB does not state at the bound tuple:
a stored claim is withdrawn by its own handle going, and asking `verdict` about one would
block an ordinary firing over a pair the KB happens to hold in both polarities.

**Placement follows the reasons.** The claim, the declarations and the edges are
antecedents, so `maximal-common-descendant-contexts` sees their contexts alongside the
rule's, and the conclusion descends to the context that can see the reach rather than
sitting where the claim alone lives. A firing whose edges are stated in incomparable
contexts has no common descendant and is recorded as `:no-placement`, like any other
completed firing that lands nowhere ([contexts.md](contexts.md)).

Two things are deliberately left, and both are shared with the qualitative side. Support
names **a** witness rather than every witness — the path is a shortest one, and the
declaration named is one of however many license the same move — so a claim reachable two
ways carries one justification and the second route is re-derived after a retraction
rather than recorded in advance. And a firing's **strength** is capped by its weakest
antecedent as always, which now includes the declaration: a `:monotonic` claim declared
preserved by a `:default` declaration draws a `:default` conclusion, where the backward
prover answers `ask` without weighing either.

**What it costs, and who pays.** Nothing here runs until a KB declares a preservation
*and* a forward rule carries an antecedent on the declared predicate. The first gate is
the O(1) cardinality read on the declaration functors' roots that the query path already
uses, so a KB that declares none pays two set-count reads per datum and stops — the
difference is not measurable against a 4,000-fact load. A KB that declares one but writes
no rule over it reads the declarations themselves per datum and then probes the
antecedent index for nothing: the starter, which declares `largerThan` and `partType` and
carries no rule over either, loads **a couple of percent** slower for it (~760 ms against
~740 ms with the trigger stubbed out).

Where both gates pass, the cost is the one the feature is: a conclusion per licensed
tuple, so the product of the reaches at the preserved positions, per claim — and each
candidate tuple is admitted by a full `surviving` read before it fires. That is paid on
the assert path rather than per query, which is the trade a materialized conclusion
always is: `ask` pays the reach per question and stores nothing, forward chaining pays it
once and leaves a sentex a later rule can join on.

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

The multiplier the memo removes is the one `undercut?` introduces: it compares every claim
against every other, so a reach walked per comparison is quadratic in the claims and a
reach walked per question is linear in them. Both readings are gated —
`inherit_test/the-reach-walk-is-linear-in-the-claims-and-not-quadratic` counts
`matches-visible` calls at three sizes and holds the second difference to a doubling
rather than a quadrupling, and `lein perf`'s `inherit-reach-memo` prices 8× the claims at
under 12× per ask, against the ~51× a lost memo reads. The comparing stays quadratic
either way; only the walking moves.

It is a *thread binding*, so the layers under it — `claims`, `surviving`,
`solve-with-support` — realize their seqs before returning. A seq handed back
unrealized is realized with the binding popped, and both multipliers come back with the
answers identical, which is why nothing but a cost measurement can see it
(`laziness_test`).

`TransitiveInArgProver`'s `est-bindings` is **1**, and that is the answer count rather
than the cost — a closed goal has at most the one empty solution. `cost :compute` is
where the work shows.


## Four things that follow from reading claims out of belief

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
and breaks the ties that leaves on the context **name** and then on what the claim
**says**. All three are functions of content alone, and the last of them is printed
through `nm/print-key`: the matcher is type-aware and fans a goal over its
sub-predicates, so one tuple routinely carries two sentences in one context at one class,
and a key an ambient `*print-length*` collapsed would put the admission straight back on
the order the retrieval answered in.

**A `genl` edge between two types can flip an exception stated over a predicate neither
type appears in.** `TransitiveInArgProver` sits in the level-6 stack that `exceptWhen` and
`unknown` evaluate through, and it answers by walking the *arguments'* reach — so
`(genl chihuahua dog)` changes whether `(largerThan chihuahua maine_coon)` holds, and
with it whether a rule excepted on `largerThan` fires. The re-check index is keyed on the
exception's own predicate and its supertypes, which cannot see that: without an
argument-side trigger the firings that predate the edge keep a conclusion the firings
after it correctly drop, and which you get depends on when the edge arrived.

`special/recheck-preserving-along` closes it. Whenever the extent of a relation `R` moves
— a fact on it, or a `genl` / `genlCx` edge — every rule whose exception mentions a
predicate declared `(transitiveInArg P n R)` is queued for re-evaluation at the next
`settle`. Queued as `:all` rather than with the moved sentence as a narrowing trigger,
because that sentence is about `R` and the exception is about `P`, so it could not narrow
the right firings anyway. The declarations are read off the functor roots rather than
through `matches-visible` — a trigger has to be conservative in the direction the answer
is, and a declaration this edge cannot see still qualifies a rule in a context that can.
Over-queueing costs a level-6 query at the next settle; under-queueing is a wrong belief.

**And the licence moves too, with no extent moving at all.** Three sentences decide
whether this prover finds anything, and none of them is on `P` or on `R`:
`(transitiveInArg P n R)` is the declaration itself, `(transitive R)` is what
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

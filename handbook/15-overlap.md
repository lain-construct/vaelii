# 15. Overlap

- **Covers:** stating that two types overlap with `orthogonal`, and stating many overlaps
  at once with `typeOrthogonal` and `orthogonalMetatypes`; why an overlap is not inherited
  along `genl`; what counts as a witness; when `siblingDisjointException` is the right form.
- **Not here:** the identity criteria that decide whether two kinds can share a member →
  [ch. 12](12-identity.md); separations → [ch. 13](13-disjointness.md),
  [ch. 14](14-covers.md); pairs nobody has decided → [ch. 16](16-unknowns.md).
- **Assumes:** [ch. 12](12-identity.md) (**what ends a member**),
  [ch. 13](13-disjointness.md).

Two types stand in one of four relations: one subsumes the other, they are disjoint, they
overlap without either subsuming the other, or nobody knows. The KB states the first two
with `genl` and the separations. This chapter is about the third, which `core.txt` lists
beside the other two in `(termsRelated genl disjoint orthogonal)`.

## orthogonal

**Practice.** When two types are known to share an instance and neither subsumes the
other, state `(orthogonal A B)`. Put a `;;` note beside it naming a member of both and what
ends that member under each kind. State `(orthogonal A B)` also to bank a separation
weighed and declined ([ch. 2](02-representation.md#bank-the-decision)); it needs no
witness, and the note names one when one is known.

**Example.** `abstract.txt` states that electronic devices and machines cut across each
other, and attaches the three cases as a comment sentex:

```clojure
(set/monotonic (orthogonal electronic_device machine))
(comment (orthogonal electronic_device machine) "A fan-cooled desktop computer is both, a wind-up clock is a machine but not electronic, and a single-board computer is electronic but not a machine.")
```

`CxSocial.txt` states two overlaps of `dwelling` and names what ends each witness:

```clojure
(orthogonal dwelling building)
(orthogonal dwelling vehicle)
```

The note above them reads "A detached house is a dwelling and a building, and a motorhome
a dwelling and a vehicle. Demolition ends the house as both, and scrapping ends the
motorhome as both."

**Why.**

- *Logical.* `(orthogonal A B)` states three things together: `A` and `B` are not
  disjoint, `A` is not a `genl` of `B`, and `B` is not a `genl` of `A`. The declaration
  does not assert that any particular term is a member of both, and it exempts the pair
  from no separation.
- *Engine.* `orthogonal` is symmetric, so the two spellings of a pair are one sentex. It is
  forced-monotonic, derives nothing and fills no taxonomy cache. A separation the reader
  sees over the pair or over a supertype of each, a `genl` edge between the two, or one
  type named twice makes the declaration a one-member hard clash: `conflicts` lists it
  with the separating declarations under `:grounds`, every member stays believed, and
  `subsumption-status` reads the pair `:inconsistent`.
- *Engine.* `disjointness-audit` reads a declared pair as `:orthogonal` with `:witness
  :declared`, never as `:unknown`. Without the declaration, the pair reads `:orthogonal`
  only when the audit finds a shared instance by a facts-only query or a shared subtype.
- *Maintenance.* Left unstated, a settled overlap reads `:unknown` beside the pairs that
  are open questions. `oe-defenses.md` puts the effect in one sentence: `orthogonal`
  records the settled overlap, so the audit's unknowns are the real open questions.

**Why not the other ways.** A `disjoint` over an overlapping pair is false and turns every
real member of both into a defeated membership. Silence leaves the pair `:unknown`. A
stated overlap records a decision and lets the audit report only what is undecided.

**Audit.** Every `orthogonal` between kinds names a witness when one is known and says
what ends it under each kind (**what ends a member**, [ch. 12](12-identity.md)); one that
banks a declined separation with no witness says so in its note. Run `kb-integrity` and read
`:orthogonal-over-separation`: each finding is an overlap declaration that a stated
separation divides, named by handle, sentence and context on both sides, so the author
drops whichever is wrong.

## An overlap is not inherited

**Practice.** State each overlapping pair the KB means. Do not expect an `orthogonal`
between two types to reach their subtypes or supertypes.

**Example.** `abstract.txt` says why it writes the pairs one by one: "An orthogonal is not
inherited along genl, so each overlapping pair is stated or derived." Below `made`, it
states the overlaps it means:

```clojure
(orthogonal made vertebrate)
(orthogonal made invertebrate)
(orthogonal made solid)
```

`core.txt` banks the decision that the relation preserves nothing along `genl`, at either
position, in either direction:

```clojure
(not (transitiveInArgInverse orthogonal 1 genl))
(not (transitiveInArgInverse orthogonal 2 genl))
(not (transitiveInArg orthogonal 1 genl))
(not (transitiveInArg orthogonal 2 genl))
```

The comment above them gives the reason: "a subtype of one side may be disjoint from the
other, and a supertype of one side may subsume the other."

**Why.**

- *Logical.* Two overlapping types can have subtypes that share no instance. `made` and
  `vertebrate` overlap in a cloned sheep, and a subtype of `made` such as `machine` shares
  no instance with `vertebrate`. Upward, a supertype of one side can subsume the other, and
  `orthogonal` denies subsumption.
- *Engine.* The engine reads no preservation for `orthogonal`, and the four stated
  denials make the decision visible to the next author (**bank the decision**,
  [ch. 2](02-representation.md)).
- *Maintenance.* Each stated pair is a decision someone made about two named kinds. An
  inherited overlap would be a decision about kinds nobody looked at.

**Why not the other ways.** A rule that carried an overlap down `genl` would conclude
overlaps between kinds that share no instance, and each one would then clash with the
separation that is true of them.

**Audit.** For each overlap the change relies on, confirm the KB states it for the pair
itself or derives it through `typeOrthogonal` or `orthogonalMetatypes`. A pair that reads
`:unknown` in `disjointness-audit` has neither.

## typeOrthogonal

**Practice.** When every member of a classifier metatype overlaps one type, state
`(typeOrthogonal Classifier Type)` once instead of one `orthogonal` per member. Declare the
classifier `forced_monotonic_predicate`.

**Example.** `abstract.txt` states that both origins, `made` and `natural`, overlap each
of seven kinds:

```clojure
(forced_monotonic_predicate origin_type)
(typeOrthogonal origin_type organism)
(typeOrthogonal origin_type body_part)
(typeOrthogonal origin_type plant)
```

The comment above the block gives a witness on each side: "A cloned sheep is a made
organism and a wild sheep a natural one. A lab-grown bladder is a made body part and a
heart a natural one." Beside `(typeOrthogonal origin_type plant)` it gives "A bonsai or a
grafted apple tree is a made plant".

**Why.**

- *Logical.* `(typeOrthogonal M T)` means that every instance of `M` is orthogonal to `T`.
- *Engine.* `core.txt` reads the declaration with a generator that writes one rule per
  fact, concluding `(orthogonal T x)` from `(M x)`. The rule concludes a forced-monotonic
  literal, so a firing supports something only when its membership antecedent is
  forced-monotonic as well. `core.txt`'s `implementationNote` on `typeOrthogonal` says a
  firing from a membership that is not forced-monotonic supports nothing and is reported
  as a `:forced-conclusion` violation, and that is why the classifier carries
  `forced_monotonic_predicate`. `abstract.txt` says the same beside the mark: each
  membership is definitional, so `origin_type` is forced-monotonic.
- *Maintenance.* A third origin added to `origin_type` overlaps all seven kinds with one
  membership.

**Why not the other ways.** Fourteen `orthogonal` sentences state the same seven decisions
twice, once per origin, and a third origin needs seven more.

**Audit.** For each `typeOrthogonal`, confirm the classifier is declared
`forced_monotonic_predicate`, and name a member of the type on each side of the
classifier.

## orthogonalMetatypes

**Practice.** When every member of one metatype overlaps every member of another, state
`(orthogonalMetatypes M1 M2)`.

**Example.** `core.txt` crosses the spatial division of `thing` with the temporal one:

```clojure
(spatiality_type spatial)
(spatiality_type aspatial)
(temporality_type temporal)
(temporality_type atemporal)
(orthogonalMetatypes spatiality_type temporality_type)
```

The `comment` on `orthogonalMetatypes` gives the reading: each of `spatial` and `aspatial`
overlaps each of `temporal` and `atemporal` without either side subsuming the other, and
two members of one metatype are not made orthogonal.

**Why.**

- *Engine.* `core.txt` states a generator per pair of positions, each writing one strict
  rule over two memberships. As with `typeOrthogonal`, a firing is believed only where both
  classifiers are forced-monotonic, and `core.txt` declares `spatiality_type` and
  `temporality_type` `forced_monotonic_predicate`. The rules are stated for two and for
  three metatypes, so a fact naming four or more concludes nothing; the
  `implementationNote` on `orthogonalMetatypes` records that absence.
- *Maintenance.* The two partitions of `thing` by space and by time are independent axes,
  and one sentence records that.

**Why not the other ways.** Four `orthogonal` sentences over the members state the cross
product by hand. A fact over four metatypes stores and concludes nothing, so state such a
cross as several facts of two or three metatypes each.

**Audit.** For each `orthogonalMetatypes`, count its metatypes; four or more derive
nothing.

## siblingDisjointException

**Practice.** Use `(siblingDisjointException A B)` only when a separation *mark* — a
`sibling_disjoint` parent, a shared `disjoint_metatype`, or a `partition` or `separating`
declaration naming both — separates a pair that does overlap. Prefer a narrower mark when
the overlap shows the mark is wrong.

**Example.** The case the relation exists for is a Braille reading, which is both a
reading event and a touch perception under a mark that separates the two kinds as
siblings. The shipped ontology has neither type and states no exception.

**Why.**

- *Logical.* `core.txt` states `(genl siblingDisjointException orthogonal)`, so an
  exception entails the orthogonal of its pair.
- *Engine.* The exception exempts its one pair from the marks and leaves each type
  separated from everything else. It is read at the reader: a context that sees the
  exception reads the pair apart, and a context above it or beside it reads the pair
  separated. A stated `disjoint` is no mark: a `disjoint` over the pair or over a
  supertype of each separates it whatever exception is stated, and the exception then
  clashes through the orthogonal it entails.
- *Maintenance.* An exception silently undoes a separation the mark states. `kb-integrity`'s
  `:orthogonal-over-separation` category exists because `disjoint?` reads the exempted
  pair apart and `conflicts` has nothing to report.

**Why not the other ways.** A plain `orthogonal` beside a mark that separates the pair is a
hard clash, because `orthogonal` exempts nothing. Retracting the mark gives up the
separation of every other pair it covers.

**Audit.** Every `siblingDisjointException` appears in `kb-integrity`'s
`:orthogonal-over-separation` findings with the mark it lifts. Confirm the mark is meant,
and name the witness the exception rests on.

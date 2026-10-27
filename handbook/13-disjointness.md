# 13. Disjointness

- **Covers:** what a separation between two types says and what the engine does with
  one; why a missing `genl` is fixed before a `disjoint` is written; why a separation is
  stated at the highest level at which it is true; how to choose among `disjoint`,
  `disjoint_metatype` and `sibling_disjoint`.
- **Not here:** declarations that say the parts exhaust a whole (`covering`, `partition`,
  `separating`) → [ch. 14](14-covers.md); stating that two types overlap →
  [ch. 15](15-overlap.md); the pairs nobody has decided, and removing a separation →
  [ch. 16](16-unknowns.md); the strength a separation is written at →
  [ch. 24](24-strength.md).
- **Assumes:** [ch. 4](04-economy.md) (**strongest form**, **state it once**),
  [ch. 10](10-parent.md) (**tightest parent**), [ch. 12](12-identity.md) (**what ends a
  member**).

A separation says that two types share no instance. The KB uses separations for three
things: to catch a term filed under two incompatible kinds, to answer a denial that no
sentence states, and to tell the disjointness audit which type pairs are settled. Each
section below is one decision an author makes before writing a separation.

## What a separation commits the KB to

**Practice.** Write a separation only for two types that share no instance in any context
that sees the declaration. Choose the pair from the kind each type names, not from the
examples at hand.

**Example.** `abstract.txt` separates animals from the made things a person lives in,
wears or sits on:

```clojure
(set/monotonic (disjoint animal building))
(set/monotonic (disjoint animal clothing))
(set/monotonic (disjoint animal furniture))
```

**Why.**

- *Logical.* `(disjoint A B)` entails, for every term `x`, that `(A x)` and `(B x)` are not
  both true. A separation is closed under `genl`: every subtype of `A` is disjoint from
  every subtype of `B`. The declaration says nothing about any particular term until a
  membership arrives.
- *Engine.* `assert` stores a membership that clashes with a separation, and the next
  settle places the two memberships as a nogood. The verdict reads the members' strengths:
  a unique weakest member loses and is defeated at the nogood's vantage; two `:default`
  members tie, stay believed and are reported by `contradictions` as a dilemma; two
  `:monotonic` members are a hard clash `conflicts` reports. `try-assert` refuses the
  second membership instead of storing it (`:definitional-clash`). A separation also
  answers a denial nobody stated: with `(dog Rex)` believed and `dog` separated from
  `building`, `query` answers `(not (building Rex))` and `argue` of `(building Rex)`
  answers `:false`. The denial climbs only `genl` edges held at `:monotonic`, because a
  `:default` edge does not contrapose.
- *Engine.* `disjoint` is in the forced-monotonic set. A `disjoint` is never the loser of a
  nogood and leaves belief only by retraction, so the separation an author writes is the
  separation the KB keeps until someone retracts it.
- *Maintenance.* A false separation costs more as the KB grows. Every term that really is
  both kinds becomes a nogood, and the settle defeats whichever membership is weaker. The
  defeated membership is a true fact the KB no longer believes.

*In development:* `disjoint` as a forced-monotonic predicate is in development
([ch. 24](24-strength.md#the-forced-monotonic-set)).

**Why not the other ways.** Leaving a true separation unstated gives up the clash check
and the denial for every term of the two kinds, and the disjointness audit reports the
pair `:unknown`. Writing a separation the author is unsure of turns each real overlap into
a defeated membership. When the pair might share an instance, the question belongs to
**what ends a member** ([ch. 12](12-identity.md)) and to `orthogonal`
([ch. 15](15-overlap.md)).

**Audit.** For each new separation, name one term that would be a member of each side and
say why no such term can be both. Run `disjointness-audit` from `CxWell` and read the new
pair's `:status`; a status of `:inconsistent` means the pair is also genl-related or
declared `orthogonal`.

## classify before you constrain
*Classify before you constrain*

**Practice.** Before writing a `disjoint`, walk both types up their `genl` chains. When a
true `genl` edge is missing and adding it would make the separation follow from one
already stated, add the edge and do not write the `disjoint`.

**Example.** `CxSocial.txt` places `dwelling` under `container` and states two separations
of its own:

```clojure
(genl dwelling container)
(disjoint dwelling clothing)
(disjoint dwelling furniture)
```

`abstract.txt` already separates `container` from three kinds:

```clojure
(set/monotonic (disjoint container organism))
(set/monotonic (disjoint container person))
(set/monotonic (disjoint container substance))
```

The comment above `dwelling` in `CxSocial.txt` says that container's disjoints carry it
clear of organism, substance and person. The one `genl` edge separates `dwelling` from
those three kinds, and from every kind below them, with no `disjoint` naming `dwelling`.
The two `disjoint` sentences beside it name the separations that no supertype of
`dwelling` carries.

**Why.**

- *Logical.* `(genl X P)` with `(disjoint P Y)` entails `(disjoint X Y)`. The `genl` edge is
  the stronger claim: it entails the separation and also every other fact true of `P`'s
  members.
- *Engine.* The separation check walks each type's supertypes, cut to the types that some
  separation names, so a separation stated on `container` is found from `dwelling` with no
  sentence about `dwelling`. Every argument constraint, rule and inherited claim on
  `container` reaches `dwelling` through the same edge. A hand-written `(disjoint dwelling
  organism)` beside the edge adds no separation, and `kb-integrity`'s
  `:derivable-stated-edge` category reports such a sentence with `:separated-by` naming
  the declaration that already separates the pair.
- *Maintenance.* One `genl` keeps doing the work as the KB grows: a separation added to
  `container` later reaches `dwelling` without an edit. The edge also records the reason
  for the separation. A reader who asks why a dwelling is no organism finds the answer in
  the type's placement, where a bare `disjoint` gives no reason.

**Why not the other ways.** A hand-written `disjoint` for a pair the classification would
separate is a second source for one fact (**state it once**). When the classification
changes, the stated pair stays behind and asserts a separation nobody chose. The missing
`genl` also costs everything else the parent carries: the argument types, the rules and
the separations stated on the parent never reach the type. A `disjoint` written in place
of the edge treats the symptom and leaves the gap.

**Audit.** For every `disjoint`, `arg` or `genlArg` in the change, walk both terms up with
`direct-genls` and `genls`. Run `kb-integrity` with `:categories #{:derivable-stated-edge}`
over the change. Each finding is a stated separation another declaration already gives;
drop it, or mark the exception of **state it once** that applies
([ch. 26](26-file-layout.md)).

## strongest form
*State knowledge in its strongest form*

**Practice.** State a separation at the highest level at which it is true. When `(disjoint
A B)` holds and `A′` is a subtype of `A`, do not also state `(disjoint A′ B)`. Before
writing a separation between two narrow types, try it one level up on each side.

**Example.** `abstract.txt` separates the whole of `mechanism` from organisms and from
stuff, and the comment beside the two sentences names the kinds they reach:

```clojure
(set/monotonic (disjoint mechanism organism))
(set/monotonic (disjoint mechanism substance))
```

The comment reads "Stated once of mechanism, each reaches machine, electronic_device and
every kind below them." The same file states `(set/monotonic (disjoint biological
substance))` once of `biological`, and the comment beside it says the separation reaches
both parts of `biological` and every kind below them.

**Why.**

- *Logical.* `(disjoint A B)` entails `(disjoint A′ B)` for every subtype `A′` of `A`. The
  weaker sentence stays derivable, so stating the stronger one loses nothing.
- *Engine.* The engine reads one declaration per separation and holds no sentence per
  separated pair. Retracting the declaration releases every pair below it at once.
- *Maintenance.* A kind added below `mechanism` is separated from `organism` the moment its
  `genl` edge arrives. A separation stated at the leaves reaches only the leaves written
  so far, and each new kind needs a new line that someone has to remember.

**Why not the other ways.** A separation stated lower than its true level needs one
sentence per pair of subtypes, misses every subtype added later, and repeats itself:
`kb-integrity`'s `:derivable-stated-edge` reports each lower copy. A separation stated
higher than its true level separates a pair that shares an instance. `abstract.txt`
states `(orthogonal food body_part)` for that reason: a leg of lamb is food and a body
part, so a separation of `food` from `body_part`, or from any supertype of `body_part`,
would make every such membership a nogood. The highest *true* level is the target, and
each step up needs its own check for a shared instance.

**Audit.** For every line, ask whether a more specific true fact entails it, and for every
`disjoint`, ask whether the pair one level up on either side is still disjoint. Read the
parent pairs with `subsumption-status` from the vantage the separation is stated for. A
parent pair reading `:orthogonal` stops the climb on that side.

## Choosing the separation form

**Practice.** Use `disjoint` for one pair. Use `disjoint_metatype` when a family of types
is pairwise disjoint by the same criterion and each member is classified into the family
by a membership. Use `sibling_disjoint` when every type placed below a parent is to be
separated from every other one that is not its own `genl` or spec. When the separated types
also exhaust a whole, use a cover ([ch. 14](14-covers.md)).

**Example.** `abstract.txt` separates the states of matter through one metatype:

```clojure
(set/monotonic (disjoint_metatype stuff_type_by_state_of_matter))
(stuff_type_by_state_of_matter gas)
(stuff_type_by_state_of_matter liquid)
(stuff_type_by_state_of_matter plasma)
(stuff_type_by_state_of_matter solid)
```

`organism.txt` separates every two species with `(set/monotonic (disjoint_metatype
folk_species))`, and its header comment says that `folk_species` separates every two
species, so no organism is a cat and a dog.

**Why.**

- *Logical.* A disjoint metatype says that any two of its members share no instance. Four
  members carry six pairs, and the five vertebrate classes `organism.txt` separates
  through `vertebrate_class` carry ten.
- *Engine.* The members of a disjoint metatype are recorded and consulted when the
  separation check runs. No `(disjoint …)` sentex is written per pair. Retracting the
  metatype mark releases every pair, and retracting one membership releases that
  member's pairs and leaves the rest separated. A membership stated before or after the
  mark produces the same separation. `sibling_disjoint` records only the mark on the
  parent and reads the parent's spec closure, so a type added below the parent later is
  separated from its siblings once its `genl` edge is believed.
- *Engine.* A metatype membership is an ordinary fact. A separation through a member
  answers a denial only when the membership holds at `:monotonic`, as the `folk_species`
  memberships in `organism.txt` do.
- *Maintenance.* A new state of matter needs one membership, and the separation from the
  other four follows. With `disjoint` per pair, the same addition needs four new sentences.

**Why not the other ways.** A list of `disjoint` sentences over a family states one
criterion many times, and a member added later is separated from only the members someone
remembered to pair it with. `sibling_disjoint` on a parent whose specs are not all
separated by one criterion separates two specs that share an instance; the mark says
nothing about which specs it was meant for.

**Audit.** For each family of three or more types separated pair by pair, ask whether one
criterion separates all of them. If it does, replace the pairs with a disjoint metatype and
its memberships, and confirm with `disjointness-audit` that the count of `:disjoint` pairs
did not fall.

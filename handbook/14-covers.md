# 14. Covers and partitions

- **Covers:** the three part-list declarations `covering`, `separating` and `partition`,
  the higher-order `partitionedByType`, when a set of `disjoint` sentences is a partition
  in disguise, and what the engine concludes from a cover.
- **Not here:** a single separated pair and the metatype forms → [ch. 13](13-disjointness.md);
  overlapping types → [ch. 15](15-overlap.md); a stated `not` and negation as failure →
  [ch. 32](32-negation.md).
- **Assumes:** [ch. 4](04-economy.md) (**strongest form**, **state it once**),
  [ch. 13](13-disjointness.md).

A whole and a named list of parts support two independent claims. The parts can exhaust
the whole, so every member of the whole is a member of some part. The parts can be
pairwise disjoint, so no member of the whole is in two parts. Three spellings make the
claims:

| | the parts exhaust the whole | no two parts share an instance |
|---|---|---|
| `(covering W A B …)` | yes | no claim |
| `(separating W A B …)` | no claim | yes |
| `(partition W A B …)` | yes | yes |

All three take a whole followed by two or more distinct parts, and the part list is
unordered: `(commutativeInArgAndRest covering 2)` makes a list written in another order
the same sentex.

## partition over disjoint
*Can `disjoint` be a `partition`?*

**Practice.** For every `(disjoint A B)`, look for a type `C` whose members are exactly
the members of `A` and `B`, together with any other pairwise-disjoint siblings. When the
parts cover `C`, state `(partition C A B …)` and drop the `disjoint` sentences the
partition implies.

**Example.** `organism.txt` divides `animal` by backbone, and the comment above the
sentence names both claims:

```clojure
(set/monotonic (partition animal vertebrate invertebrate))
```

The comment reads "Every animal has a backbone or lacks one. The partition installs both
genl edges to animal." `abstract.txt` divides `tangible` by origin the same way, and its
comment ends "A tangible denied made is concluded natural.":

```clojure
(partition tangible made natural)
```

**Why.**

- *Logical.* `(partition C A B)` entails `(disjoint A B)`, `(genl A C)`, `(genl B C)` and
  the coverage claim that every `C` is an `A` or a `B`. The `disjoint` alone entails none
  of the other three. The partition is the stronger form (**strongest form**).
- *Engine.* The coverage half licenses a conclusion. With `(partition tangible made
  natural)`, a believed `(tangible X)` and a believed `(not (made X))` prove `(natural
  X)`. `CoveringProver` answers that goal with one bounded subquery per premise and no
  enumeration of a part's extent. Denying every part of a cover for a member of the whole
  is a contradiction of kind `:cover`, stored and placed as a nogood in every arrival
  order. A denial of a supertype of a part denies the part, and a separation's denial
  rules a part out as a stated denial does.
- *Engine.* The separation half is recorded the way a disjoint metatype's members are: no
  `(disjoint …)` sentex is written per pair, and retracting the partition releases every
  pair at once.
- *Maintenance.* The partition states the two `genl` edges, so the file holds one sentence
  where the weaker form needs three. A reader who asks what an animal can be gets the
  answer from one line.

**Why not the other ways.** A `disjoint` between two parts of a covered whole states half
of what is true, so the KB cannot conclude the remaining part from a denied one. A
`covering` beside a `separating` over the same part list is a partition logically, and
`core.txt`'s comment on `partition` notes that no rule concludes a `partition` from the
two. The KB answers `(covering W A B)` and `(separating W A B)` from a stated `(partition
W A B)`, through `partition`'s two `genl` edges, but not the converse.

**Audit.** Run `kb-integrity` with `:categories #{:disjoint-could-be-partition}`. A
finding with `:basis :covering` names a cover whose parts the separations already divide,
and the suggested partition is then entailed. A finding with `:basis :sole-specs` names a
parent whose only direct specs are the pair, and coverage is then a guess the author
confirms by asking whether the parent has a member in neither part. The finding never
suggests a parent a visible `partition` already divides into the pair.

## Covering, separating or partition

**Practice.** Decide the two claims one at a time. Ask whether every member of the whole
belongs to some part; ask whether any member belongs to two. Write `partition` when both
hold, `covering` when only the first does, and `separating` when only the second does.

**Example.** `organism.txt` separates animals from plants without claiming that every
organism is one of the two:

```clojure
(set/monotonic (separating organism animal plant))
```

A mushroom is an organism and neither an animal nor a plant, so a partition of `organism`
into the two would be false. The comment on `plant_class` in the same file records the
same decision for the folk classes of plant: "Not a partition of plant, since a fern or a
moss is none of the three."

**Why.**

- *Logical.* `separating` claims the separation and nothing about coverage, so an
  instance of the whole that belongs to no part violates nothing. `covering` claims the
  coverage and lets two parts overlap.
- *Engine.* Only a declaration that claims coverage, `covering` or `partition`, reaches
  `CoveringProver` and the `:cover` refutation. A `separating` declaration proves no
  membership and no set of denials falsifies it. A bare `covering` records no separation,
  so `disjoint?` answers false for two of its parts.
- *Engine.* Each of the three installs a `genl` edge from each part to the whole,
  supported by the declaring sentex and carrying its context. The edges therefore leave
  with the declaration when it is retracted.

**Why not the other ways.** A `partition` over a whole that has members outside the parts
makes the coverage inference conclude a false membership. A `partition` over parts that
overlap places a nogood on every member of two parts. `separating` and `covering` exist so
an author states exactly the claim that is true and no more.

**Audit.** For each new part list, name a member of the whole that is in no part, or
state that none exists; name a member that is in two parts, or state that none exists. The
two answers pick the spelling.

## A cover states the edges it rests on

**Practice.** Do not write `(genl Part Whole)` beside a cover that names the part. Where a
file states the edge anyway, a `;;` note says which exception of **state it once** applies.

**Example.** The header of `organism.txt` says that `(separating organism animal plant)`
states both `genl` edges and the separation, so no `(genl plant organism)` or `(disjoint
animal plant)` sentence is written beside it. The same comment notes that `core.txt` also
stores `(genl animal organism)` as a sentence.

**Why.**

- *Engine.* Every reader that asks which edges a sentex put into the `genl` closure reads
  one edge per part for a cover, so a rule on the whole fires on a fact about a part with
  no edge stated by hand. A cover asserted before its parts carry any other fact settles to
  the state a cover asserted after them does.
- *Maintenance.* A separately stated edge outlives the cover. When the cover is retracted
  or narrowed, the stated edge stays and asserts a placement nobody chose.

**Why not the other ways.** `wff` refuses a cover that states nothing or cannot hold:
fewer than two parts, a repeated part, an individual in any position, a part equal to the
whole, and a part the closure already places above the whole. Each is refused as
`:not-well-formed`. A part disjoint from its whole is stored, and the settle reports the
cover and the `disjoint` together as a hard clash.

**Audit.** Run `kb-integrity` with `:categories #{:derivable-stated-edge}`. A stated
`genl` that a cover also installs is reported with `:also-stated-by` naming the cover.

## partitionedByType

**Practice.** When the parts of a partition are exactly the members of a classifier
metatype, state `(partitionedByType Whole Classifier)` and the classifier's memberships.
Write the plain `partition` beside it, and mark that sentence as the implementation
exception of **state it once**.

**Example.** `abstract.txt` classifies tangibles by origin:

```clojure
(metatype origin_type)
(forced_monotonic_predicate origin_type)
(origin_type made)
(origin_type natural)
(partitionedByType tangible origin_type)
```

`(partition tangible made natural)` stands in the same file. `core.txt` divides `thing`
by spatiality the same way, with `(partitionedByType thing spatiality_type)` beside
`(set/monotonic (partition thing spatial aspatial))`.

**Why.**

- *Logical.* `(partitionedByType W M)` says each member of `M` is a subtype of `W`, no two
  members share an instance, and every instance of `W` is an instance of some member. The
  classifier names the criterion, so a reader sees why the parts divide the whole.
- *Engine.* `core.txt` reads the declaration with two rules. A generator places each
  member of the classifier under the whole, and skips a `thing` whole, since every type is
  under `thing` already. A forward rule concludes `(disjoint_metatype Classifier)`, so the
  separation is the metatype's recorded clique. No rule draws the coverage half;
  `core.txt`'s `implementationNote` on `partitionedByType` says so, and says that a
  partition stated beside each fact carries it. That note is the reason the plain
  `partition` stays.
- *Maintenance.* The classifier gives the criterion a name that other declarations can
  use. `abstract.txt` states seven `typeOrthogonal` facts over `origin_type`
  ([ch. 15](15-overlap.md)), each of which reaches both `made` and `natural`.

**Why not the other ways.** A bare `partition` states the division without naming its
criterion, and a classifier with no `partitionedByType` states the criterion without the
division. A `partitionedByType` alone, with no plain `partition` beside it, loses the
coverage inference while no rule draws it.

**Audit.** For each `partitionedByType`, confirm a plain `partition` over the same whole
and the classifier's members is stated beside it, with a `;;` note naming the
implementation exception.

## The coverage a type inherits

**Practice.** When a type under a covered whole is disjoint from every part but one, state
its `genl` edge to the remaining part.

**Example.** `kb-integrity`'s `:implicit-genl` category finds such a type. With `(partition
thing tangible intangible)` and `(partition thing temporal atemporal)` stated, and
`tangible` below `temporal` through `core.txt`'s `(genl tangible spatiotemporal)`, a type
placed under `atemporal` is separated from `tangible` through the second partition, so
each of its members is `intangible`.

**Why.**

- *Logical.* The coverage argument holds of a type as of an individual: every instance of
  the type is an instance of the whole, none is in the excluded parts, so all are in the
  remaining part.
- *Engine.* The `genl` closure does not derive the edge, and nothing on the write path
  applies the cover to a type. Without the stated edge, the type's members miss every rule
  and argument constraint on the remaining part.

**Why not the other ways.** A rule concluding the remaining part for each member reaches
the individuals the rule fires on and leaves the type outside the remaining part in the
hierarchy, where the disjointness audit and every subsumption read look.

**Audit.** Run `kb-integrity` with the new types as candidates. Each `:implicit-genl`
finding names the type, the edge to state, the cover that forces it, and for each other
part the declarations that separate the type from it.

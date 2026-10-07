# Changelog

Notable changes to `vaelii`, newest first. Versions follow
[semantic versioning](https://semver.org/spec/v2.0.0.html); pre-1.0, a **Breaking**
entry raises the minor. What each class means, and why a **Refusal** is patch-eligible,
is [CONTRIBUTING.md §3](CONTRIBUTING.md).

**Releases before 0.23.0 are summarized rather than reproduced.** Each one
keeps its title, its class census and every `*Breaks:*` token, so an upgrade across
several releases is still a grep for the name you call. The full entry prose for a
released version is in this file's git history, at the tag of the release that shipped
it — `git show v0.16.0:CHANGELOG.md`.

## Unreleased

### Breaking

- **`transitiveInArg` and `transitiveInArgInverse` swap names, so `transitiveInArg` takes
  the direction of Cyc's `transitiveViaArg`.** `(transitiveInArg P n R)` now carries a
  stored `(P … W …)` along `R`'s arrow: `(R W A)` gives `(P … A …)`, which with `genl`
  is upward, to a supertype. `(transitiveInArgInverse P n R)` carries it against the
  arrow: `(R A W)` gives `(P … A …)`, which with `genl` is downward, to a subtype. Before
  this change each name carried the other direction. The argument order stays `(P n R)`
  (Cyc writes `(P R n)`). The engine implements the same two walks it did; only the
  functor naming each walk changed, and every declaration the shipped KB and the test
  suite state was rewritten to the other name, so each one still licenses what it did:
  `(transitiveInArg largerThan 1 genl)` is now `(transitiveInArgInverse largerThan 1
  genl)`. [inherit.md](docs/inherit.md), [from-cyc.md](docs/from-cyc.md).

  *Class:* **Breaking** (a stored declaration under either name now licenses the
  opposite direction).
  *Migration:* swap every `transitiveInArg` and `transitiveInArgInverse` in your KB: the
  names now carry the directions Cyc's `transitiveViaArg` / `transitiveViaArgInverse`
  do.
  *Breaks:* `transitiveInArg`, `transitiveInArgInverse`

- **`siblingDisjointException` is retired; `orthogonal` is the exemption.** A stated
  `(orthogonal a b)` exempts the pair from a separation a `sibling_disjoint` parent or a
  `disjoint_metatype` would otherwise force, pair-local and read at the reader, as
  `(siblingDisjointException a b)` did, and from every other form of disjointness too: a
  `partition` or `separating` roster naming both (a partition keeps its coverage half) and
  an explicit `(disjoint a b)`, which an `orthogonal` of the pair now overrides wherever
  it is seen. The exemption is read against the separated pair of supertypes, so it lifts
  what that separation reached below them. The declaration also says neither type
  subsumes the other, so a `genl` edge between them, `(orthogonal a a)`, or an
  `orthogonal` over two subtypes of a pair that stays separated is a clash of the
  declaration; `(siblingDisjointException a a)` was refused as not well-formed. CxCore no longer
  declares `siblingDisjointException`, `special/entries` no longer interprets it, and a
  stored one is an ordinary fact that exempts nothing.
  [taxonomy.md](docs/taxonomy.md#disjointness).

  *Class:* **Breaking** (a predicate retired, and an explicit `disjoint` is overridden by
  an `orthogonal` of the same pair, so `subsumption-status` of a pair stating both moves
  from `:disjoint` to `:orthogonal`).
  *Migration:* `(siblingDisjointException a b)` → `(orthogonal a b)`; a KB that states
  both `(disjoint a b)` and `(orthogonal a b)` reads the pair apart, so drop whichever is
  wrong.
  *Breaks:* `siblingDisjointException`, `disjoint?`, `subsumption-status`

- **`subsumption-statuses` reads `:disjoint` from its vantage.** `disjoint?` is read at
  `context` (default `CxUniverse`), the vantage the declared `orthogonal` is read from, so
  a pair separated in `CxUniverse` and declared `orthogonal` in a context below it reads
  `:disjoint` at `CxUniverse` and `:orthogonal` below, and a `disjoint` stated only in a
  context the vantage does not see no longer counts.
  [taxonomy.md](docs/taxonomy.md#auditing-the-hierarchy-for-missing-disjointness).

  *Class:* **Breaking** (a pair separated only in a context below the vantage reads
  `:unknown` at the vantage).
  *Migration:* pass the context that states the separation as `context`.
  *Breaks:* `subsumption-statuses`, `subsumption-status`, `disjointness-audit`

- **CxCore states the upper ontology's axes orthogonal.** The three partitions of
  `thing` cut it by location in some space, by location in time and by mass, and a part
  of one overlaps a part of another without either subsuming it. CxCore now says so:
  `(orthogonal spatial temporal)`, `(orthogonal aspatial atemporal)`,
  `(orthogonal spatial atemporal)`, `(orthogonal aspatial temporal)`,
  `(orthogonal intangible spatial)`, `(orthogonal intangible temporal)` and
  `(orthogonal intangible spatiotemporal)`, each `set/monotonic` beside the partitions
  and each with a witness (a rock, the line y=x, a fluent, a region of space). Each pair
  now reads `:orthogonal` from `subsumption-status` without a shared instance, and
  leaves `disjointness-audit`'s `:unknown` candidates. No stated separation divides any
  of them, so the load adds no conflict and no contradiction.
  [taxonomy.md](docs/taxonomy.md#disjointness). *Class:* **Additive**.

- **`transitiveInArgInverse` is forced monotonic, as `transitiveInArg` is.** CxCore
  declares `(forced_monotonic_predicate transitiveInArgInverse)` and the engine's roster
  holds it on every KB beside `transitiveInArg`, under `:unforced-relation-mark`: a
  declaration written at `:default` reads back `:monotonic`, a denial of one is stored and
  held OUT (`why-not` answers `:inert`), a rule concludes one only from roster
  antecedents, and retracting the roster declaration is refused.
  [nmtms.md](docs/nmtms.md#the-forced-monotonic-roster).

  *Class:* **Breaking** (a denial of a `transitiveInArgInverse` is no longer believed, and
  a `:default` one is no longer defeasible).
  *Migration:* retract a `transitiveInArgInverse` declaration instead of denying it.
  *Breaks:* `transitiveInArgInverse`

### Additions

- **`time` is a moment or a stretch of time as such, and `time_interval` is the
  stretch.** A date is no cause: the year 2000 broke nothing, two-digit years did, at the
  rollover. CxAbstract declares `time`, a time as in "at that time", with
  `(genl time temporal)`, `(genl time aspatial)` and `(genl time acausal)`, and
  `(partition time time_point time_interval)`, so a moment and a stretch are each
  temporal, aspatial and acausal and never each other; `(disjoint time situation)` keeps
  a time apart from what happens in it. CxUniverse states
  `(termsRelated time_interval Duration)`, since `Duration` is CxMeasure's.
  `(genl time_point temporal)` is removed, since the partition derives it.
  `YearFn`, `MonthFn` and `DayFn` declare `(result … time_interval)` where they declared
  `temporal`, so a calendar term is admitted where an argument wants `acausal` or
  `aspatial`, as is a `StartFn` moment. CxTime declares `DatetimeFn`, the ISO-string
  spelling of a calendar interval, a `unary_function` with `(arg DatetimeFn 1 string)`
  and `(result DatetimeFn time_interval)`. `ontology_test` pins the edges, the
  disjointness and the calendar readings.
  [time.md](docs/time.md)

  *Class:* **Additive** (shipped ontology content, which takes no Breaking label however
  far it moves an answer).
  *Migration:* a KB that read `(result YearFn temporal)`, `(result MonthFn temporal)` or
  `(result DayFn temporal)` as stated reads `time_interval` instead; `temporal` still
  derives through `time`. A KB that relied on `(genl time_point temporal)` being stated
  reads it from `genl?`.

- **`kb-integrity` runs a bounded, read-only integrity sweep in a context.** Over a finite
  set of ground candidate terms it reports the definition clashes a candidate meets (a
  passing `defnSufficient` beside a failing own `defnNecessary`), and it reports every
  visible `predAllSpecified` / `predSpecifiedAll` declaration that `all-specified-violations`
  reports. A clean sweep answers `{:status :audited :candidate-count n}`, a sweep with
  findings `:status :gap` with only the non-empty categories, and a sweep that runs out of
  `:max-work`, `:max-ms` or `:max-results` `:status :truncated` with its `:reason` and the
  findings kept. `:categories` names the passes to run. The sweep stores nothing and
  files no violation. [integrity.md](docs/integrity.md).

  *Class:* **Additive**.

- **`kb-integrity` reports a predicate `genl` edge that widens a declared argument type.**
  The sweep adds the sparse category `:genl-arg-widening`, one
  `{:spec P :genl Q :arg n :spec-type T :genl-type U}` per type `P` declares at a position
  that no type `Q`'s constraint demands there subsumes. The pass reads the visible `arg`
  declarations, not the candidate terms.
  [integrity.md](docs/integrity.md#what-a-widening-finding-means).

  *Class:* **Additive**.

- **The daemon serves `kb-integrity` as the `:kb-integrity` op.** A request with no option
  map receives the daemon's three ceilings (`:max-work` 10,000, `:max-results` 1,000 and
  the query clock), and a bound over a ceiling is refused `:over-ceiling`. `vaelii.client`
  gains `kb-integrity`. [operations.md](docs/operations.md).

  *Class:* **Additive**.

- **`relation` is divided into `function` and `truth_valued_relation`,
  `truth_valued_relation` into `logical_constant` and `predicate`, and `logical_constant`
  into `quantifier` and `logical_connective`; `and`, `or`, `not` and `implies` are logical
  connectives.** CxCore states `(partition relation function truth_valued_relation)`,
  `(partition truth_valued_relation logical_constant predicate)` and
  `(partition logical_constant quantifier logical_connective)`, after Cyc's
  `TruthFunction`, so a predicate, a quantifier and a logical connective reach `relation`
  through `truth_valued_relation`, and each is disjoint from the others and from
  `function`. `truth_valued_relation` is named apart from logic's truth function, a
  connective whose value is fixed by its arguments' truth values, which a predicate and a
  quantifier are not. `(unary_predicate not)` and `(binary_predicate implies)` are
  replaced by `(logical_connective not)` and `(logical_connective implies)`, and the
  connectives' arities are stated with the relation-wide vocabulary: `(unary not)`,
  `(binary implies)`, `(variable_arity and)` and `(variable_arity or)`. An arity reader
  (`kb/relation-arity`, the `checks` arity arm) reads 1 for `not` and 2 for `implies` as
  before, and `arity_vocabulary_test`'s every-relation-has-exactly-one-arity-policy holds
  over all four. No shipped term is a `quantifier` yet. CxCore no longer states
  `(genl function relation)`, `(genl predicate relation)` or `(disjoint function
  predicate)`: the partitions entail all three, the disjointness descending to `predicate`
  from `(disjoint function truth_valued_relation)`, so each is derived, and the rule-entry
  refusal of `(implies (result ?f ?t) (genl ?f ?t))` reads the derived disjointness as it
  read the stated one. `ontology_test` pins the three
  partitions, the connectives' typing, and that the three entailed facts derive and are
  not stated; the four new types are classified inert in the vocabulary roster.

  *Class:* **Additive** (shipped ontology content, which takes no Breaking label however
  far it moves an answer).
  *Migration:* a query that found `not` among the `unary_predicate`s or `predicate`s, or
  `implies` among the `binary_predicate`s, asks `logical_connective` instead, or `unary` /
  `binary` for the arity; a KB that states `(predicate not)` or a connective's membership
  in any predicate type now contradicts the partition. A query for `(genl function
  relation)`, `(genl predicate relation)` or `(disjoint function predicate)` answers as
  before; code that unasserts one of them, or reads it as a stated sentence (a dump, a
  diff, a justification walked to its stated leaves), finds it derived from the
  partitions instead, and retracts it by retracting the partition.
  *Breaks:* `(unary_predicate not)`, `(binary_predicate implies)`,
  `(genl function relation)`, `(genl predicate relation)`, `(disjoint function predicate)`

- **The upper ontology divides `thing` by location in space, by time and by mass:
  `spatial` is a location in any space, `spatiotemporal` is a location in space and
  time, `physical_object` is renamed `tangible` and `abstract` is renamed
  `nowhere_never`.** The old `spatial`, which meant a location in the world, is renamed
  `spatiotemporal`, and `spatial` now names the broader collection of things with a
  location in some space, mathematical spaces included — the line y=x, a square of an
  abstract chessboard, a point — and `spatiotemporal` is defined as the intersection of
  `spatial` and `temporal`. Every CxSpace argument is declared at the broader `spatial`,
  since none of the four calculi needs time, so RCC-8, direction and distance relate
  regions of the Cartesian plane as readily as fields; the context keeps two spaces apart.
  `(partition thing spatial aspatial)`, `(partition thing temporal atemporal)` and
  `(partition thing tangible intangible)` state the three divisions, separation and
  coverage both, so a thing denied one part is concluded the other. `tangible` is
  something with mass and keeps `physical_object`'s edge to `spatiotemporal`;
  `intangible` is something with no mass, and `(disjoint intangible spatial)` is dropped
  so that a region can be spatiotemporal and intangible at once. `nowhere_never` is in
  no space and at no time — an expression, a language — defined as the intersection of
  `aspatial` and `atemporal`; what has no location in space, or none in time, has no
  mass, so `aspatial` and `atemporal` are both below `intangible`. `attribute`,
  `capability`, `fluent`, `organization` and `relation_type` are below `aspatial`, and
  CxCore places `context` and `language` below `nowhere_never`, so each stays disjoint
  from `spatial` and `spatiotemporal` in every context that sees the kind's placement.
  Every stated `genl` or `disjoint` that a partition, an intersection, a `genl` chain, a
  `disjoint_metatype` or another disjointness already derives in the same context is
  removed — forty-two sentences across CxCore, CxAbstract and CxUniverse, which now
  states no axiom of its own. `ontology_test` pins the divisions and every removal, and
  `spatial`, `spatiotemporal`, `tangible` and `nowhere_never` are classified inert in the
  vocabulary roster.
  [space.md](docs/space.md), [glossary.md](docs/glossary.md)

  *Class:* **Additive** (shipped ontology content, which takes no Breaking label however
  far it moves an answer).
  *Migration:* a KB that wrote `physical_object` renames to `tangible`; the old spelling
  stores clean but attaches to nothing in the taxonomy, so its instance reaches neither
  `tangible` nor `thing`. A KB that wrote `spatial` for "located in the world" renames to
  `spatiotemporal`; the old spelling still stores, and now places the thing in the
  broader collection, where nothing concludes it has a location in the world. A KB that
  wrote `abstract` renames to `nowhere_never`; the old spelling stores clean but attaches
  to nothing in the taxonomy. A KB that relied on `(disjoint organization animal)` or
  another removed sentence being stated, rather than derived, reads it from `disjoint?`
  or `genl?` instead.
  *Breaks:* `physical_object`, `spatial`, `abstract`

- **`living_thing` is renamed `organism`.** The type names something alive in its own
  right — born, growing, reproducing, and dying by default — and every shipped use is
  renamed: the `alive` and `mortal` defaults, the argument declarations of `alive`,
  `dead` and `mortal`, the `animal` and `plant` edges, the vocabulary roster, the
  browser examples and the docs. The default-alive and default-death rules are
  unchanged. No `rewriteOf` alias is shipped, as none was for `physical_object`.

  *Class:* **Additive** (shipped ontology content, which takes no Breaking label however
  far it moves an answer).
  *Migration:* a KB that wrote `living_thing` renames to `organism`; the old spelling
  stores clean but attaches to nothing in the taxonomy, so no default reaches what it
  types.
  *Breaks:* `living_thing`

- **Kinship and age relate organisms, not only animals.** A plant or a bacterium is born
  and has a parent as an animal does, so `parentOf`, `childOf`, `siblingOf`, `ancestorOf`,
  `grandparentOf`, `birthYearOf` and `olderThan` declare `organism` where they declared
  `animal`, and the kinship and age rules read on from a tree's parent as from a dog's.
  `fatherOf`, `motherOf`, `FatherFn` and `MotherFn` stay `animal`, as do the behaviour
  predicates (`asleep`, `awake`, `breathes_air`, `eats`, `preysOn`, `warm_blooded`).
  `common_sense_test` stores a parent and two birth years between two trees and derives
  the rest, with neither tree taken for an animal.

  *Class:* **Additive** (shipped ontology content, which takes no Breaking label however
  far it moves an answer).
  *Migration:* a KB that relied on a kinship or age fact refusing a plant, or on its
  arguments being animals, states that narrower type of its own.

- **`biological` is an organism or a part of one: `organism` and `body_part` are
  separated under it, and `food` and `body_part` are orthogonal.** `biological` is a
  tangible that is an organism or part of one, held in CxCore beside the other skeleton
  collections so both CxCore's `organism` and CxAbstract's `body_part` extend it.
  `(separating biological organism body_part)` places `body_part` under `biological`,
  with no edge stated beside it, and keeps an organism and a part it grew apart without
  claiming the two exhaust `biological`. The stated
  `(genl organism tangible)` and `(genl body_part tangible)` are removed, since the
  route through `biological` derives both. The monotonic `(disjoint food body_part)` is
  replaced by `(orthogonal food body_part)` — a leg of lamb or a chicken wing is both —
  so an instance of both is no longer a clash. `(disjoint biological substance)` is stated
  monotonic in CxAbstract in place of `(disjoint organism substance)` and
  `(disjoint substance body_part)`, which it derives, so a thing both biological and a
  substance is a clash. `ontology_test` pins the separation, the derived edges and
  disjointness, and the shared instance, and `biological` is classified inert in the
  vocabulary roster.
  [contexts.md](docs/contexts.md)

  *Class:* **Additive** (shipped ontology content, which takes no Breaking label however
  far it moves an answer).
  *Migration:* a KB that relied on `food` and `body_part` clashing has no stated
  replacement below CxAbstract, since an `orthogonal` overrides a `disjoint` of the pair
  wherever both are seen; it types the clash it needs on narrower kinds of its own. A
  KB that relied on `(disjoint organism substance)` or `(disjoint substance body_part)`
  being stated, rather than derived, reads it from `disjoint?` instead. A
  KB that relied on `(genl organism tangible)` or `(genl body_part tangible)` being
  stated, rather than derived, reads it from `genl?` instead.

- **An organism can be an artifact: `(disjoint organism artifact)` is replaced by
  `(orthogonal biological artifact)`.** An artifact is anything intentionally made, so
  an engineered bacterium or an organ grown in a lab is biological and an artifact at
  once. The monotonic disjointness is removed from CxAbstract and the orthogonal stated
  there, so an organism or a body part that is also an artifact is no longer a clash,
  and neither is a kind below either — an `animal` that is a `tool`. `organism` and
  `body_part` stay disjoint from `substance`. `ontology_test` asserts an organism and
  a body part as artifacts and finds no clash.

  *Class:* **Additive** (shipped ontology content, which takes no Breaking label however
  far it moves an answer).
  *Migration:* a KB that needs an organism kept apart from an artifact states the
  separation over narrower kinds of its own, such as `(disjoint animal tool)`; a
  `disjoint` of `biological` and `artifact` themselves is overridden wherever the
  shipped `orthogonal` is seen.
  *Breaks:* `(disjoint organism artifact)`

- **CxCore partitions `function` and `unary_predicate` and defines
  `equivalence_relation` as an intersection.** `(partition function reifiable_function
  unreifiable_function)` separates the two minting marks, which nothing separated
  before, and installs their edges to `function`. `(partition unary_predicate
  fixed_order_type variable_order_type)` separates the two order kinds and installs
  their edges to `unary_predicate`, so a metatype is never of variable order.
  `(intersection equivalence_relation reflexive symmetric transitive)` concludes
  `(equivalence_relation P)` of a predicate carrying all three marks and places
  `equivalence_relation` below each of them, so its stated edge to `binary_predicate` is
  removed; the three forward rules that materialize the marks stay. `ontology_test`
  pins each division, the coverage half of `(partition relation function
  truth_valued_relation)`, and the five removed sentences.

  *Class:* **Additive** (shipped ontology content, which takes no Breaking label however
  far it moves an answer).
  *Migration:* a KB that declared one function both `reifiable_function` and
  `unreifiable_function` now reads a clash; drop the wrong mark.

- **A situation is static or an event.** CxUniverse states `(partition situation
  static_situation event)`, which adds coverage to the separation CxAbstract states, so
  a situation denied being an event is concluded a `static_situation`. `ontology_test`
  pins the coverage.

  *Class:* **Additive** (shipped ontology content, which takes no Breaking label however
  far it moves an answer).
  *Migration:* none.

- **The organisms carry a folk taxonomy: `vertebrate` and `invertebrate`, three class
  metatypes under `folk_biological_class`, and `folk_species`.** CxUniverse states
  `(partition animal vertebrate invertebrate)` and places the five vertebrate classes
  and `insect` and `arachnid` below the two parts. `invertebrate_class` and
  `plant_class` are `disjoint_metatype`s beside the shipped `vertebrate_class`, and
  `(separating folk_biological_class vertebrate_class invertebrate_class plant_class)`
  keeps the three apart. `folk_species` is a `disjoint_metatype` over the 27 shipped
  species, so no organism is of two species, and is disjoint from
  `folk_biological_class`. Both new metatypes are below `type`, since each member is a
  first-order type. The disjointness audit's unknown pairs among the types below
  `organism` fall from 514 to 280, and the 248 among the kinds fall to 0: `grass` is a
  `plant_class` beside `tree` and `flower`. Each of the 280 pairs one of the seven
  biology properties placed under `organism` and `animal` (`alive`, `asleep`, …) with
  another type. `ontology_test` pins the separations, the coverage half and that no
  pair of kinds below `organism` is left unknown.

  *Class:* **Additive** (shipped ontology content, which takes no Breaking label however
  far it moves an answer).
  *Migration:* a KB that stated one organism of two shipped species, or an insect that is
  a mammal, now reads a clash.

- **`folk_species` is on the forced-monotonic roster.** CxUniverse declares
  `(forced_monotonic_predicate folk_species)`: a species membership is definitional, so
  it is held `:monotonic` whatever strength it was written at and a denial of one is held
  OUT, and a rule concluding a roster literal such as `orthogonal` from
  `(folk_species ?s)` alone is a roster rule rather than a `:forced-conclusion`.
  [nmtms.md](docs/nmtms.md#the-forced-monotonic-roster).

  *Class:* **Additive** (shipped ontology content, which takes no Breaking label however
  far it moves an answer).
  *Migration:* none; a denial of a shipped species membership no longer moves belief.

- **Fifteen shipped unary predicates gain a `genl` path to `thing`.** The `kb-integrity`
  `:not-under-thing` sweep reported each from CxWell. In CxCore,
  `abducible_predicate`, `closed_extent_predicate`, `decontextualized_predicate`,
  `forced_decontextualized_predicate` and `target_following_predicate` are placed under
  `predicate`, as `modal_predicate` already was; `sibling_disjoint` under
  `unary_predicate`, since what it marks is a type. In CxTime, `functional_at_instant` is placed under `function`. CxUniverse states
  `(genl initially fluent)`: `initially` is CxTime's and `fluent` is CxAbstract's, and
  CxUniverse is the context that sees both. CxUniverse also places the seven
  biology properties under the kind each is said of: `alive`, `dead` and `mortal` under
  `organism`; `asleep`, `awake`, `breathes_air` and `warm_blooded` under `animal`.
  `ontology_test` runs the sweep over those fifteen and finds none. The sweep also
  reports `not`, which is left unplaced: a `genl` edge from a connective to `formula`
  would make it a subtype of the formulas it builds, so its typing is punted to the
  use/mention batch.

  *Class:* **Additive** (shipped ontology content, which takes no Breaking label however
  far it moves an answer).

- **`subsumption-statuses` reads a shared subtype that is not separated from itself as
  `:orthogonal`.** A pair neither subsuming the other nor disjoint, with a type below both
  for which `disjoint?` of the type with itself is false, reads `:orthogonal` with no
  shared instance stated. A type below two separated types is empty and is no witness, so
  a pair whose only shared subtypes are empty stays `:unknown`. `disjointness-audit` marks
  each `:orthogonal` entry with `:witness` (`:declared`, `:shared-instance` or
  `:shared-spec`) and, for the last two, `:via`, the instance or the subtype found. On the
  starter KB, 18 of 13861 pairs move from `:unknown` to `:orthogonal`, among them
  `spatial` and `temporal` through `spatiotemporal`, and `injection` and `surjection`
  through `bijection`.
  [taxonomy.md](docs/taxonomy.md#auditing-the-hierarchy-for-missing-disjointness).

  *Class:* **Additive** (an `:unknown` pair gains a status, and audit entries gain two
  keys).

### Fixes: answers

- **`query {:proof? true}` and `argue` return a proof when a rewrite's residual repeats
  a conjunct the goal already holds.** Where the repeat folded onto a literal left of the
  rewritten one they threw `IndexOutOfBoundsException`; where it folded onto one right of
  it the proof showed a derived literal as a `:leaf`. A proof's leaves are now exactly the
  answering node's literals. [inference.md](docs/inference.md#the-two-side-by-side).

  *Class:* **Fix**.

### Fixes: clashes and order independence

- **A symmetric fact's argument-type mints rest on the same declaration however it was
  spelled.** A fact asserted or derived after its `arg` / `genlArg` / `interArg`
  declarations drew its mints over the arguments as written, while a declaration
  arriving after the fact, and a text export reloading it, drew them over the spelling
  the store keeps. For a `(symmetric P)` fact written against that sorted order, such as
  `(orthogonal spatial atemporal)` under `(genlArg orthogonal 1 thing)` and
  `(genlArg orthogonal 2 thing)`, the minted `(genl spatial thing)` rested on the
  position-1 declaration in one order and the position-2 one in the other, so authored
  and content order stored different justifications. The entailment now reads the
  stored spelling on every path, so every order stores the same justifications.
  [argtypes.md](docs/argtypes.md).

  *Class:* **Fix**.

- **A stated `genl` route that makes a minted edge redundant re-joins the rule firings
  the mint carried.** The settle withdraws a `genl` mint a stated route has made
  redundant by sweeping it, and every rule firing that named the mint as its witness was
  deleted with it. Where the firing's conclusion stood on another firing, nothing drew
  it again over the surviving route, so the store kept whichever firings the arrival
  order had drawn, and a later full join — a re-join after a context-hierarchy change,
  or `forward-chain` — drew the rest at fresh justifications. The settle now re-joins
  the facts and rules each withdrawn edge carried, as it does for an edge that lost
  belief, so the two arrival orders store the same justifications.
  [nmtms.md](docs/nmtms.md).

  *Class:* **Fix**.

- **`orthogonal` declares that two types may overlap and neither subsumes the other.**
  `(orthogonal A B)` states that something could be an instance of both and that neither
  is a `genl` of the other; it does not say that anything is, and says nothing about
  things that are instances of neither. CxCore
  declares it a symmetric binary `type_relation_predicate`, so `(orthogonal B A)` is the
  same sentex. It derives nothing and mints no shared instance.
  [taxonomy.md](docs/taxonomy.md#disjointness). *Class:* **Additive**.

- **`subsumption-statuses` reads a stated `orthogonal` as `:orthogonal`.** A pair
  declared `(orthogonal a b)` in either spelling, visible from the vantage `context`,
  reads `:orthogonal` with no shared instance, so `disjointness-audit` no longer counts it
  among its `:unknown` pairs. A declared pair that is also `genl`-related, or separated
  through two supertypes the declaration does not exempt, carries both statuses, and
  `subsumption-status` reports it `:inconsistent`; a `disjoint` over the declared pair
  itself is exempted, so that pair reads `:orthogonal`.
  [taxonomy.md](docs/taxonomy.md#auditing-the-hierarchy-for-missing-disjointness).
  *Class:* **Additive**.

- **`disjointness-audit` sweeps types, not the relations a predicate `genl` edge names.**
  `genl` also specializes one relation by another, as in `(genl performedBy doneBy)`,
  and the audit swept every node of the `genl` closure, so each such relation entered
  the sweep as a type and every pair it was in read `:unknown`. A node whose arity is two
  or more, read from `(arity P n)` or an exact-arity class as the arity check reads it,
  or that is declared `variable_arity`, is now left out, and `:types` counts the nodes
  swept.
  [taxonomy.md](docs/taxonomy.md#auditing-the-hierarchy-for-missing-disjointness).
  *Class:* **Fix**.

- **An `orthogonal` over a `genl`-related or still-separated pair is a clash of the
  declaration.** Wherever a reader reads a `genl` edge between the two, the two are one
  type, or the pair is still disjoint through a separation of two supertypes the
  declaration does not exempt, the declaration is
  a one-member nogood, `:kind :orthogonal`, in every arrival order. Nothing is refused:
  `orthogonal` is on the forced-monotonic roster beside `disjoint`, so the declaration,
  at whatever strength it was written, is a hard clash `conflicts` lists, with the
  separating declarations under `:grounds`, and its retraction from the roster is refused
  with `:unforced-definitional-declaration`.
  [nmtms.md](docs/nmtms.md#declarations-over-related-types). *Class:* **Additive**.

- **`kb-integrity` reports a candidate type with no `genl` path to `thing`.** Every type
  is a specialization of `thing`, but nothing on the write path reports a
  `unary_predicate` that reaches `thing` by no `genl` edge. The sweep adds a fourth
  sparse category, `:not-under-thing`, with one `{:term X}` per candidate term the audit
  context sees declared `unary_predicate` and that has no `genl` path to `thing` visible
  from that context, in print order. `thing` itself is never a finding, and a candidate
  that is not a ground symbol is skipped. The caller's candidate set bounds the pass, so
  it enumerates no types. Findings count against `:max-results` after the
  `:genl-arg-widening` category and are kept on truncation.
  [integrity.md](docs/integrity.md#what-a-not-under-thing-finding-means).

  *Class:* **Additive**.

- **`kb-integrity` suggests a `genl` edge a cover forces but the closure misses.** A
  cover places individuals, not types: a type under the whole that is disjoint from every
  part but one has all its instances in that part, yet `(genl X P)` is neither stated nor
  derived. The sweep adds a fifth sparse category, `:implicit-genl`, with one
  `{:term X :genl P :cover [...] :disjoint-from [{:part Q :grounds [...]} ...]}` per
  candidate type and visible `covering` or `partition` over one of its supertypes or over
  `thing` that leaves exactly one part `disjoint?` does not exclude, when `genl?` does not
  already hold. `:grounds` names the believed declarations each separation rests on. A
  part or the whole itself is never a finding, and the sweep asserts nothing. The
  caller's candidate set bounds the pass. Findings count against `:max-results` after the
  `:not-under-thing` category and are kept on truncation.
  [integrity.md](docs/integrity.md#what-an-implicit-genl-finding-means).

  *Class:* **Additive**.

- **`kb-integrity` reports an `orthogonal` that lifts a stated separation.** An
  `(orthogonal a b)` exempts the pair from every separation, so `disjoint?` reads it
  apart and nothing shows the conflict when the separation was meant: one `orthogonal`
  silently undoes a `partition` of `thing`. The sweep adds a sixth sparse category,
  `:orthogonal-over-separation`, with one
  `{:orthogonal {:handle :sentence :context} :separated-by [{:handle :sentence :context} ...]}`
  per visible, believed `orthogonal` whose pair, or a supertype of each, an explicit
  `disjoint`, a `partition` or `separating` roster, a `sibling_disjoint` parent or a
  `disjoint_metatype` separates, read with no exemption applied. Both sides are named by
  handle so the author can drop whichever is wrong. The pass reads one census of
  visible `orthogonal` declarations, not the candidate set. Findings count against
  `:max-results` after the `:implicit-genl` category and are kept on truncation.
  [integrity.md](docs/integrity.md#what-an-orthogonal-over-separation-finding-means).

  *Class:* **Additive**.

### Internal

- **The `orthogonal` comments and taxonomy.md name every separation the declaration
  exempts.** The flat-cache comment and `tax/exemption`'s docstring named the clique marks
  alone. [taxonomy.md](docs/taxonomy.md#disjointness).

  *Class:* **Internal**.

- **taxonomy.md documents the three partitions of `thing`, and the glossary defines
  `intangible`.** The glossary entries for `aspatial`, `atemporal`, `tangible` and
  `nowhere_never` link the section. `nm/advice`'s documented multi-word example is
  `(isa Muffet WarmBlooded)`, a type the shipped ontology declares, and contexts.md lists
  the head's ontology collections without a count.
  [taxonomy.md](docs/taxonomy.md#the-three-partitions-of-thing)

  *Class:* **Internal**.

- **`full_kb_test`'s write probes borrow no type from a relation's membership.** A
  function's name is spelled as an individual's, so the probe skips a sampled `(T x)`
  whose `x` is a `relation` in its context.

  *Class:* **Internal**.

- **`ontology_test` fails a loaded membership in a type no other sentence names.** The
  test reads every premise membership in the starter and the test-world, and names a
  type that no `genl` edge, argument declaration or comment names.

  *Class:* **Internal**.

- **`vaelii.impl.violations/*report-sink*` collects the diagnostics a read files.** Bound
  to an atom, it receives the violations an evaluation would add to the ledger;
  `kb-integrity` binds it, so the ledger does not move during a sweep. The
  `kb-integrity` docstring states its contract, and `docs/integrity.md` drops two
  sentences that gave a rationale where a mechanism belongs.
  [integrity.md](docs/integrity.md#what-a-definition-finding-means).

  *Class:* **Internal**.

- **A daemon `:kb-integrity` call that sends only the candidate set is refused
  `:bad-args`.** The daemon no longer pads it to a call that reads its option map as the
  context. [operations.md](docs/operations.md).

  *Class:* **Internal**.

- **A `kb-integrity` sweep that spends no more than `:max-work` finishes.** A sweep that
  completed within its work budget no longer reports `:truncated` with `:reason
  :max-work`. [integrity.md](docs/integrity.md#the-call).

  *Class:* **Internal**.

- **`kb-integrity` takes `:categories`, and checks its candidate set before any pass.**
  A set of category keys runs those passes alone, so a caller reaches a candidate pass
  the census passes would spend the work budget ahead of. A candidate set that is not a
  set of ground terms is refused with `:op kb-integrity` whichever passes run.
  [integrity.md](docs/integrity.md#the-call).

  *Class:* **Internal**.

- **`kb-integrity`'s specified pass reads the declarations in content order.** A sweep cut
  short by `:max-results`, `:max-work` or `:max-ms` keeps the same declarations in every
  arrival order. The sweep's deadline tests move a hooked clock instead of sleeping.
  [integrity.md](docs/integrity.md#the-call).

  *Class:* **Internal**.

- **`kb-integrity`'s work meter is part of `vaelii.impl.budget`, and a read outside a
  sweep takes no meter wrapper.** Outside a sweep, prover dispatch returns each answer
  stream and callback result unwrapped. A sweep's `:max-ms` reaches the
  argument-preservation prover's claim walk, and a `nil` bound reads as no bound.
  [integrity.md](docs/integrity.md#the-call).

  *Class:* **Internal**.

## 0.23.0 — 2026-10-02 — "no definitional clash is refused, each reader decides a clash from its own view, and the definitional vocabulary is held known-true"

### Breaking

- **A forced-monotonic predicate is held `:monotonic` when belief is computed, a denial
  of one is held OUT, and a firing concluding one from a non-roster ground supports
  nothing; every write is stored as written.** `(forced_monotonic_predicate P)` puts `P`
  on the roster, and `(forced_monotonic_between_predicates F)` puts every `(F …)` whose
  arguments are all spelled as predicates on it. The engine holds `genlCx`, the relation
  marks, the definitional declarations, the arity bindings, `except` and the equality
  relations with the first, and `genl` with the second, on every KB whether or not it
  loads CxCore; CxCore declares these and `injection`, `surjection` and `bijection`, and
  `has-prop?` and `props` answer the roster from any context. A `:default` write of one stays
  `:default` in its record and reads back `:monotonic` from `defeat-class`. `(not S)`
  for a roster literal `S` is stored as a premise, never believed, and `why-not` answers
  `:inert` for it; a denial of an equation instance no longer blocks its rewrite. A rule
  concluding a roster literal is stored, and its firing supports its conclusion only
  when every antecedent is a roster literal and the rule has no `unknown`, `exceptWhen`
  or `set/defaultRule`; any other firing is stored, supports nothing and is reported as
  a `:forced-conclusion` violation. A declaration is a switch: asserting or retracting
  one recomputes belief over what its predicate reaches, so a KB that retracted it
  believes what a KB that never held it believes. Retracting a declaration CxCore makes
  is refused with `:uncleared-forcing`, except those of `injection`, `surjection` and
  `bijection`. No rule concludes `(arity P n)` from an exact-arity class: `describe`'s
  `:arity` and `admitsArgnum` read the class, and a query of `(arity P n)` answers the
  declared arity alone. A reasoning image stamps the declared roster and is declined
  under another one. [nmtms.md](docs/nmtms.md#the-forced-monotonic-roster).

  *Class:* **Breaking** (a roster write reads back `:monotonic`, a denial of one is not
  believed, a rule's roster conclusion from a non-roster ground is not believed, a class
  no longer derives an arity sentence, and an uncleared declaration's retraction is
  refused).
  *Migration:* retract a roster sentence instead of denying it; state a defeasible
  separation or identity with a `:default` rule concluding a denial of a membership, or
  with a predicate that does not merge; read an arity through `describe` or assert
  `(arity P n)`. A store written before keeps each premise at the class it was
  stored at, and a denial it held inert takes the `:default` premise mark on its next
  recover; `forward-chain` places a firing it dropped under a declaration it no longer
  holds.
  *Breaks:* `defeat-class`, `why-not`, `violations`, `describe`, `retract!`, `edit!`, `has-prop?`, `props`, `forced_monotonic_predicate`, `forced_monotonic_between_predicates`, `relationTypeByArity`

- **No definitional clash is refused, and the `:constraints` option and
  `VAELII_ARBITRATE_CONSTRAINTS` are gone.** `assert` stores a sentence that completes a
  `disjoint`, `functional`, cover, `asymmetric` or `anti_transitive` clash with stored
  content, whatever the members' classes, and the settle decides it: the unique weakest
  member loses, a `:default` tie is listed by `contradictions`, and a clash of
  `:monotonic` members stands in `conflicts` with every member believed. The same holds
  for a fact whose argument-declaration mint clashes. A `(disjoint a b)` over
  `genl`-related types and a cover naming a part disjoint from its whole are stored, and
  `check` no longer reports a clash that names its members. Opening a KB with
  `:constraints`, or with `VAELII_ARBITRATE_CONSTRAINTS` set, is refused with
  `:unknown-option`, and a reasoning image written before is declined once and rebuilt.
  [nmtms.md](docs/nmtms.md#1-order-independence).

  *Class:* **Breaking** (`assert` stores what it refused, and an option and a switch are
  refused).
  *Migration:* drop `:constraints` from `open-kb` and `fork` options and unset
  `VAELII_ARBITRATE_CONSTRAINTS`. Where a caller caught a `:disjoint`, `:functional`,
  `:cover`, `:asymmetric` or `:anti-transitive` refusal, read `(conflicts kb)` for a clash
  of `:monotonic` members and `(contradictions kb)` for a `:default` tie, and retract the
  member the application rejects.
  *Breaks:* `open-kb`, `fork`, `assert`, `check`, `:constraints`,
  `VAELII_ARBITRATE_CONSTRAINTS`, `:disjoint`, `:functional`, `:cover`, `:asymmetric`,
  `:anti-transitive`

- **A firing of a rule with an `unknown` antecedent or an `exceptWhen` confers
  `:default`.** A `:monotonic` rule guarded by `(unknown S)` or `exceptWhen` over
  `:monotonic` facts concludes a `:default` sentence, which ties a `:default` member of a
  nogood as a dilemma instead of defeating it. An `exceptWhen` stated after the rule
  fired lowers the conclusions already derived, and retracting it restores them.
  [nmtms.md](docs/nmtms.md#strength-propagates-from-the-antecedents).

  *Class:* **Breaking** (`defeat-class` of a guarded conclusion reads `:default`, and a
  clash it was the monotonic winner of is a dilemma in `contradictions`).
  *Migration:* none for a `set/defaultRule`. State a conclusion that must stay
  `:monotonic` with a rule that has no `unknown` antecedent and no `exceptWhen`.
  *Breaks:* `defeat-class`, `contradictions`, `supporting-justifications`, `exceptWhen`,
  `unknown`

- **An `irreflexive` self tuple and an `anti_symmetric` converse no merge reconciles are
  stored, and each reader decides them.** `assert` no longer refuses `(P a a)` under a
  visible `(irreflexive P)`, or `(P 2 1)` beside `(P 1 2)` under `(anti_symmetric P)`.
  The tuple is stored, and each context that reads the mark decides the nogood when it
  reads: a `:default` self tuple, or the `:default` member of a converse whose other
  member is `:monotonic`, is not believed there, and a sentence resting only on it is
  withdrawn with it. Two `:default` members are listed by `contradictions`, and a
  `:monotonic` self tuple or pair by `conflicts`. The mark and the tuple give one reading
  in either order, and a late mark files no `:irreflexive`, `:anti-symmetric` or
  `:unarbitrable-reach-truncated` violation. `preview` names a tuple a mark in its batch
  takes out. `lein perf` gains `irreflexive-mark-arrival` and `decided-warm-read`.
  [nmtms.md](docs/nmtms.md#nogoods-decided-at-the-reader).

  *Class:* **Breaking** (`assert` stores what it refused, `believed?` answers false for a
  stored tuple a reader decides against, and two refusal types and three violation kinds
  are gone).
  *Migration:* where a caller caught an `:irreflexive` or `:anti-symmetric` refusal, read
  `(conflicts kb)` for a known-true tuple and `(believed? kb h context)` for a `:default`
  one, and retract the tuple the application rejects. Stop reading `:irreflexive`,
  `:anti-symmetric` and `:unarbitrable-reach-truncated` entries from `violations`.
  *Breaks:* `assert`, `check`, `believed?`, `conflicts`, `contradictions`, `violations`,
  `preview`, `:irreflexive`, `:anti-symmetric`, `:unarbitrable-reach-truncated`

- **Each reader below a vantage decides a clash from its own view, and belief no longer
  depends on how many passes a settle runs.** A context below a nogood's vantage which also
  sees a denial, an edge or an `except` dissolving the clash believes the member the
  vantage took OUT, and a context that sees two vantages reads the classes it sees itself:
  a tie there is a dilemma it believes both members of, whatever either vantage decided.
  This holds for a clash inside one context as for one across several: the network holds
  no defeat, so a rule over the loser fires and its conclusion is stored and
  withdrawn wherever the loser is, and `belief-status` answers `:in? true` with
  `:withdrawn? true` for the loser. A write that makes a settle run a second pass leaves
  every reading as it was. An inherited clash is decided the same way, at each reader, in
  one context as across several. [nmtms.md](docs/nmtms.md#a-defeat-is-scoped-to-its-vantage).

  *Class:* **Breaking** (`ask?`, `believed?` and `contradictions` at a context below a
  vantage answer from that context's view; `belief-status`' `:in?` is true for a loser;
  a conclusion over a loser is stored, withdrawn).
  *Migration:* none; a caller that relied on a vantage's verdict below it states the
  winning member where that reader sees it, and reads a loser's belief through
  `believed?` or `in?` rather than `belief-status`' `:in?`.
  *Breaks:* `ask?`, `believed?`, `belief-status`, `contradictions`, `argue`

- **A tuple of a length its predicate's arity binding breaks is stored, and each reader
  decides it; the arity bindings are forced monotonic.** `(arity P n)`, the nine
  exact-arity class memberships (`unary`, `binary_predicate`, `ternary_function`, …),
  `variable_arity` with its two specializations, and `arityMin` are on the
  forced-monotonic roster, so a `:default` write of one reads back `:monotonic` and a
  denial of one is inert. `assert` no longer refuses a tuple whose length breaks the
  binding its predicate, or a predicate above it, carries: the tuple is stored, a
  `:default` one is not believed at a context that sees the binding, and a `:monotonic`
  one stands in `conflicts` with the binding under `:grounds`. A membership binds by its
  own functor, so `(transitive P)` binds no length of `P`. A `genl` edge, or an arity
  declaration, relating two predicates whose own bindings differ is stored, and the two
  bindings are a hard clash in `conflicts` (`:arity-descension`). A late binding files no
  `:arity`, `:arity-truncated` or `:arity-report-truncated` violation, and a firing's
  wrong-length conclusion is stored rather than dropped. `lein perf` gains
  `arity-binding-arrival`. [taxonomy.md](docs/taxonomy.md#arity).

  *Class:* **Breaking** (an arity binding reads back `:monotonic`, `assert` stores what it
  refused with `:arity`, `believed?` answers false for a stored tuple a reader decides
  against, and a refusal type and three violation kinds are gone).
  *Migration:* where a caller caught an `:arity` refusal, read `(conflicts kb)` for a
  known-true tuple and `(believed? kb h context)` for a `:default` one, and retract the
  tuple the application rejects. Retract an arity binding instead of denying it. State a
  length with a roster spelling rather than through a membership whose type sits under an
  exact-arity class. Stop reading `:arity`, `:arity-truncated` and
  `:arity-report-truncated` entries from `violations`.
  *Breaks:* `assert`, `check`, `believed?`, `conflicts`, `defeat-class`, `violations`,
  `:arity`, `:arity-truncated`, `:arity-report-truncated`, `binary_predicate`,
  `variable_arity`, `arityMin`

- **A `functional`, `functionalInArg` or `anti_symmetric` collision of two symbols merges
  only when both facts are `:monotonic`.** `(motherOf Kid Ann)` known-true beside a
  `:default` `(motherOf Kid Bea)` under `(functional motherOf)` derives no
  `(equals Ann Bea)`: the collision is a nogood, `(motherOf Kid Bea)` is not believed, and
  Ann and Bea stay distinct. Two `:default` facts are a dilemma listed by
  `contradictions`, with both believed. Two `:monotonic` facts merge as before, in every
  arrival order, and re-asserting the `:default` fact `:monotonic` merges them. An
  `anti_symmetric` converse through two predicates below the mark is decided the same
  way. [equality.md](docs/equality.md#functional-infers-equality-instead-of-throwing).

  *Class:* **Breaking** (`same-class?`, `ask?` of `equals` and the rewriting of a goal no
  longer follow a merge a `:default` fact licensed, and `believed?` answers false for the
  `:default` loser).
  *Migration:* assert the facts a merge should follow from `{:strength :monotonic}`, or
  state the identity with `equals`, which is stored `:monotonic`. A defeasible identity
  is written with a predicate that does not merge.
  *Breaks:* `same-class?`, `ask?`, `believed?`, `contradictions`, `functional`,
  `functionalInArg`, `anti_symmetric`, `injection`, `surjection`, `bijection`

- **A read that names no context answers belief at the handle's own context.** `in?` and
  `believed` answer false for a handle a nogood its own context decides takes OUT, and for
  one resting only on such a loser, where they answered the network's label. `types-of`
  and `isa?` with no context read each membership that way, the unscoped `genl` and
  `genlCx` closures and flat caches leave out a supporter withdrawn at its own context, so
  `genl?`, `disjoint?` and `inverse-of` with no context skip it, and `why-not` answers
  `:defeated` for such a loser. An unscoped read never believes what no context believes.
  [nmtms.md](docs/nmtms.md#a-read-with-no-reader).

  *Class:* **Breaking** (`in?`, `believed`, `why-not` and the unscoped taxonomy reads
  answer false for an `irreflexive`, `anti_symmetric`, arity or other reader-decided loser
  at its own context, where they answered true).
  *Migration:* read the network label through `belief-status`' `:in?`.
  *Breaks:* `in?`, `believed`, `why-not`, `types-of`, `isa?`, `genl?`, `disjoint?`

- **The justification network records no defeat, and a reasoning image written before is
  declined once and rebuilt.** A contradiction is decided at each reader and never in the
  network, so the network keeps support labels alone: the defeated set and the second,
  groundability fixpoint are gone from both network representations, and a
  `:disk-snapshot` image no longer carries them. An image an earlier build wrote is
  declined at open, the KB recovers in full, and the next close writes an image of the new
  layout. [storage.md](docs/storage.md#the-reasoning-image).

  *Class:* **Breaking** (a `:disk-snapshot` image of an earlier build is recovered in full
  once, at its first open).
  *Migration:* none; the first open after the upgrade recovers the store and writes a new
  image.
  *Breaks:* `:disk-snapshot`

- **A merge restates every member of a clash, and a decontextualization lift copies a
  clashing fact.** With `(disjoint dog cat)`, `(dog Bea)`, `(cat Bea)` and `(equals Ann
  Bea)`, the twin restated second was dropped and reported in `violations`, so which
  member kept the displaced spelling `Bea` depended on the arrival order. Each twin is now
  stored and supersedes its original, a member whose network label is OUT when the merge
  arrives is restated too, and the clash at `Ann` is decided at each reader and reported in
  `contradictions` or `conflicts`. A lift into CxUniverse from a context that does not see
  it stores a copy that clashes there in the same way. Only an inadmissible twin or copy
  (an argument conviction, a malformed form) is dropped and filed.
  [equality.md](docs/equality.md#interactions).

  *Class:* **Breaking** (`violations` no longer files a `:disjoint`, `:functional`,
  `:asymmetric` or `:anti-transitive` entry for a merge's twin or a lift's copy, and its
  table drops the last three kinds).
  *Migration:* read `(contradictions kb)` for a `:default` tie and `(conflicts kb)` for a
  clash of `:monotonic` members, where a caller read the twin's entry in `violations`.
  *Breaks:* `violations`, `:functional`, `:asymmetric`, `:anti-transitive`

- **A `siblingDisjointException` exempts its pair only at the contexts that see it.** With
  `(sibling_disjoint col)`, `(genl ta col)`, `(genl tb col)`, `(ta X)` and `(tb X)` in CxU
  and `(siblingDisjointException ta tb)` in CxE below CxU, CxU reads the two memberships
  as a nogood and CxE reads none: `disjoint?` at CxU answers true, a `:default` tie is
  listed by `contradictions` with vantage CxU, and a `:default` member beside a
  `:monotonic` one is not believed at CxU and is believed at CxE. An exception was read
  over the whole KB, so it released the pair at every context. A read with no context
  sees every exception. `exposed-clashes` names a pair a context reads separated below
  or beside the exception.
  [taxonomy.md](docs/taxonomy.md#disjointness).

  *Class:* **Breaking** (belief, `disjoint?`, `contradictions` and `exposed-clashes` at a
  context that does not see the exception).
  *Migration:* state an exception that must hold for a context in that context or in
  one it sees, such as CxUniverse.
  *Breaks:* `siblingDisjointException`, `disjoint?`, `contradictions`, `exposed-clashes`

### Refusals

- **A durable fork remounted over a base that has grown since is refused
  `:fork-base-overlap`.** A fork keys its records and its excepts' targets by handle, and
  mints them above the base's handles at the time. Remounted over a base that has since
  grown (a newer starter, more files loaded at startup), the fork's record at each handle
  the base now also held won every read: the base's sentence there answered `unknown`
  through the fork, `argue` returned the fork's justification for it, and an except naming
  a handle the fork had retracted hid the base sentence that took that handle (#99). A
  fork that had only retracted inherited premises hid the grown base's sentences too,
  under any key it had emptied, and so did a reindexed fork; over a base rebuilt in another
  order, a tombstone hid whichever sentence took the handle. Each mount now records the
  base's watermark in the fork's bookkeeping, and the next mount refuses when the base
  holds a record at or above it and the fork has written anything. A fork pins a digest
  of each base record it tombstones, overrides or releases, and a mount over a base
  holding another record at a pinned handle is refused. A fork mounted before this
  release is checked on its first mount by comparing its own records with the base's at
  the handles both hold. The refusal names the `:handles` at issue and leaves the fork's
  directory unlocked. [overlay.md](docs/overlay.md#the-merge-model--record-half).

  *Class:* **Refusal** (a remount over a grown base answered base sentences with the
  fork's records, with no error).
  *Migration:* mount the fork over the base it was taken against, read its premises, and
  re-assert them by content in a fresh fork over the new base, re-pointing each except
  at the new handle of its target.

  *Breaks:* `fork`, `open-kb`

- **An `exceptWhen` exception whose quantifier rebinds a rule variable is refused
  `:quantifier-not-local`, and one written with a query operator is held to
  stratification.** `(exceptWhen (thereExists ?b (sick ?b)) (implies (bird ?b) (flies
  ?b)))` was stored with the rule's binding substituted for the binder, so the
  quantifier ranged over a constant. And an exception whose conjunct is an `unknown`, a
  `thereExists` or an aggregate drew its negative edge to the operator rather than to the
  predicates it reads, so a cycle through negation it closed was accepted when its rule
  arrived after the rule it cycled with, and refused in the other order; it is now
  refused `:not-stratified` in both. `check` predicts both.
  [exceptions.md](docs/exceptions.md#the-exception-is-a-query-not-a-literal).

  *Class:* **Refusal** (a rebound binder answered over a constant, and an unstratified
  exception was stored, with no error).
  *Migration:* rename the binder apart from the rule's variables; break the cycle by
  guarding the rule with an antecedent, or write the exception over a predicate off the
  cycle.
  *Breaks:* `assert`, `check`

### Additions

- **`conflicts` lists a `disjoint` over `genl`-related types, and a cover naming a part
  a `disjoint` separates from its whole.** With `(genl dogw animalw)` and `(disjoint dogw
  animalw)`, `conflicts` lists a hard clash whose one member is the declaration; with
  `(covering animalw dogw catw)` and the same `disjoint`, it also lists one of the cover and
  the `disjoint`. Every arrival order reports the same, and no belief moves.
  [nmtms.md](docs/nmtms.md#declarations-over-related-types).

  *Class:* **Additive**.

- **A `conflicts` and `contradictions` report names the declarations its clash is
  convicted through.** Each report carries `:grounds`, `[{:handle :sentence :context}
  ...]` in content order: the `disjoint`, metatype, `sibling_disjoint`, cover or relation
  mark declarations a vantage of the report sees, and no `genl` edge. A rebuttal and an
  `:inherited` clash carry `[]`. The list is the same in every arrival order, and
  retracting every ground dissolves the clash.
  [nmtms.md](docs/nmtms.md#a-clash-is-reported-never-stored). *Class:* **Additive**.

### Fixes: answers

- **`(cautiously S)` answers alike with and without an ASP backend for a conclusion
  derived from one side of a dilemma.** With a backend, a conclusion that is not a
  dilemma member fell back to base belief, which holds both sides, so in a Nixon diamond
  with `pacifist ⇒ opposesWar` `(cautiously (opposesWar Nixon))` answered true; it now
  reads the solve-free bracket, as a build without a backend does, and answers false.
  [labeling.md](docs/labeling.md).

  *Class:* **Fix**.

- **`(bravely S)` and `(cautiously S)` answer alike with and without an ASP backend for a
  member of dilemmas whose members derive from one another.** With three defaults where
  `b` rebuts both `a` and `c` and each rebuts `b`, a backend answered `(cautiously a)`
  false and `(bravely b)` true, because the `Program` it solves holds no derivation
  between members and so misses that defeating `b` also drops the `¬a` and `¬c` it
  derives. A backend now classifies only a member of a cluster the solve-free bracket
  does not enumerate, and only when no member of that cluster derives from another.
  [labeling.md](docs/labeling.md).

  *Class:* **Fix**.

- **`do/labeling` commits an optimal resolution of dilemmas whose members derive from
  one another, with or without an ASP backend.** On the same three defaults it gave up
  `a`, `b` and `c` and kept their three denials, where defeating `b` alone resolves both
  dilemmas; its classification called all six members `:supportable`. It now commits one
  of the solve-free bracket's resolutions, chosen by content, keeps `a`, `c` and `¬b`,
  and returns and records the bracket's classification, which `label/classify` reads
  back. A cluster past the bracket's caps is still labeled by a solve.
  [labeling.md](docs/labeling.md).

  *Class:* **Fix**.

- **An `exceptWhen` exception may carry a `thereExists`.** `(exceptWhen (thereExists ?c
  (and (childOf ?b ?c) (sick ?c))) (implies (bird ?b) (flies ?b)))` was refused
  `:exception-not-closed`, the closure check counting the binder `?c` as a variable the
  antecedents owed. It now counts free variables, so the exception blocks for a `?b`
  with one child that is sick. Binders are numbered when the exception is stored, so two
  exceptions that differ only in a binder's name are one meta-sentex.
  [exceptions.md](docs/exceptions.md#the-exception-is-a-query-not-a-literal).

  *Class:* **Fix**.

### Fixes: clashes and order independence

- **A revived `genl` edge merges and decides what the same edge arriving merges and
  decides.** An edge whose void firing a roster declaration released merged nothing below
  it for a `functional` or `anti_symmetric` mark, and an edge revived under an
  `anti_symmetric` mark left a converse pair stored while it was OUT undecided, so its
  `:default` member stayed believed where the order with the edge arriving last takes it
  OUT. [equality.md](docs/equality.md#functional-infers-equality-instead-of-throwing).

  *Class:* **Fix**.

- **A `functional`, `functionalInArg` or `anti_symmetric` mark that a void firing
  concludes merges nothing until a roster declaration releases the firing.** Its arrival
  stored an equality OUT over the facts already stored and merged the partition, so
  `equiv-class` answered a merge `ask?` denied, and under `anti_symmetric` the release left
  both converse facts believed under the displaced spelling, with no restatement, where the
  order with a fact stored after the mark restates them.
  [equality.md](docs/equality.md#functional-infers-equality-instead-of-throwing).

  *Class:* **Fix**.

- **A rule firing held void installs its conclusion in no taxonomy cache, so the KB
  agrees with its own `recover`.** A firing that concludes an equality, a `genl` edge
  between predicates, a `genlCx` edge, a `disjoint`, an arity binding or a relation mark
  from an antecedent off the forced-monotonic roster is stored and not believed, and it
  still merged the two terms, joined the edge or marked the predicate until a restart.
  [taxonomy.md](docs/taxonomy.md#what-a-rule-may-conclude-and-what-it-reaches).

  *Class:* **Fix**.

- **An equality that becomes believed after its firing was held void restates the facts
  its merge displaces.** Released by a roster declaration, or joined by a valid firing of
  the same conclusion, it merged the two terms and restated nothing, so the KB believed
  the retired spellings where the order with the valid firing first believes their
  restatements. [equality.md](docs/equality.md#what-a-merge-does).

  *Class:* **Fix**.

- **The settle after a `genl` edge mints every link of a chain of `genlArg` declarations
  in which each declaration waits on the type the one before it mints.** The settle
  released one link per pass, so a chain of more than 15 links stopped at the 16-pass
  bound, and a read before the next settle missed the remaining edges.
  [exceptions.md](docs/exceptions.md#a-refused-firing-is-remembered-as-bindings).

  *Class:* **Fix**.

- **A context whose election retires the KB's own representative reads a fact stated
  under it in every arrival order.** With `(sameAs Pa Qb)`, `(rewriteOf Qb Pa)` and `(dog
  Qb)`, a context that sees the `sameAs` and not the `rewriteOf` (stated in a sibling,
  reached by a late `genlCx` edge, or excepted there) elects `Pa`, and read `(dog ?x)` as
  nothing in the orders where the fact was stored before the sentence that hid the
  `rewriteOf` from it. [equality.md](docs/equality.md#scope-context-and-re-election).

  *Class:* **Fix**.

- **A reader that withdraws an equality supporter no longer reports a disjointness clash
  between memberships whose spelling it then retires.** In a KB that leaves the equality
  relations off the forced-monotonic roster, a reader that defeats the `rewriteOf` making
  `Qb` the head of `{Pa Qb}` elects `Pa`, and still read `(dog Qb)` and `(cat Qb)` as a
  hard clash. [nmtms.md](docs/nmtms.md#a-defeat-is-scoped-to-its-vantage).

  *Class:* **Fix**.

- **A reader's arity binding is read over the live `genl` edges after the inherited-clash
  discovery reads its own view in the same settle.** The discovery's view of the
  taxonomy and the live taxonomy can each move one `genl` edge to the same generation, and
  a reader after the view read the bound predicates above a functor through the view's
  edge. [nmtms.md](docs/nmtms.md#nogoods-decided-at-the-reader).

  *Class:* **Fix**.

- **A stored tuple is not believed beside the converse a known-true claim reaches by
  argument preservation under an `asymmetric` mark.** With `(asymmetric touchesX)`,
  `(genl nudgesX touchesX)`, `(transitiveInArg nudgesX 1 genl)`, `(genl chix dogx)`, a
  `:monotonic` `(nudgesX dogx Fido)` and a `:default` `(nudgesX Fido chix)`, every arrival
  order believed `(nudgesX Fido chix)`; the mark on `nudgesX` itself did the same when
  one argument position is preserved. The pair is now an `:inherited` nogood, and the
  default loses. [inherit.md](docs/inherit.md#a-contrary-claim-against-a-known-true-one-is-a-contradiction-and-is-reported).

  *Class:* **Fix**.

- **A guarded firing a blocker's defeated support releases fires in every arrival order.**
  With `(exceptWhen (penguin ?x) (bird ?x) => (flies ?x))`, `(antarctic ?x) => (penguin
  ?x)`, `(bird Opus)`, a `:default` `(antarctic Opus)` and a `:monotonic` `(not (antarctic
  Opus))` in one context, 24 of the 120 arrival orders left `(flies Opus)` unbelieved.
  [nmtms.md](docs/nmtms.md#a-read-with-no-reader).

  *Class:* **Fix**.

- **A context below a guarded rule's placement asks the rule's `unknown` or `exceptWhen`
  again.** With `(pp ?x) & (unknown (qq ?x)) => (rr ?x)` and `(pp Zed)` in CxA, and
  `(qq Zed)` in CxB, which sees CxA, CxB believed `(rr Zed)`; it now reads the firing as
  withdrawn, with what rests on it, and CxA keeps it. An `exceptWhen` query holding at the
  reader does the same. [naf.md](docs/naf.md#evaluated-in-the-placement-context-not-the-join).

  *Class:* **Fix**.

- **The change feed reports a firing an `exceptWhen` rule makes as it arrives.** With
  `(bird Opus)` stored, asserting `(exceptWhen (penguin ?x) (set/forwardRule (implies
  (bird ?x) (flies ?x))))` delivered an event naming the rule and not `(flies Opus)`.
  [feed.md](docs/feed.md#one-settle-is-one-event).

  *Class:* **Fix**.

- **`preview`, `edit-with-consequences!` and the change feed report a belief a reader's
  verdict releases in every arrival order.** With `(cat Rex)` in CxA, `(dog Rex)`
  `:monotonic` in CxB, `(disjoint dog cat)` in CxD and a rule `(cat ?x) => (meows ?x)` in
  CxJ, which sees all three, CxJ takes `(meows Rex)` OUT; when the rule arrived last,
  retracting `(dog Rex)` or the declaration revived `(meows Rex)` at CxJ and no report
  named it. Each event now equals the difference in belief at each sentence's own
  context. [nmtms.md](docs/nmtms.md#the-published-window).

  *Class:* **Fix**.

- **A length bound on a cover's whole binds its parts in every arrival order.** With
  `(arity W 1)`, `(covering W P Q)` and a tuple `(P X Y)`, the tuple stayed believed when
  the cover arrived after it; each order now withdraws it, as an asserted `(genl P W)`
  does. [taxonomy.md](docs/taxonomy.md#arity).

  *Class:* **Fix**.

- **A `disjoint` or cover clash is found from the term its memberships name and decided
  by each reader that sees it, in every arrival order, and the `:arbitration-truncated`
  notice is no longer filed.** A `genlCx` edge that brings a separation into view at a
  common descendant of the two memberships' contexts decides the pair there when it
  arrives last, as it did when it arrived first; with `(a Pip)` in CxA, `(b Pip)` in CxB,
  `(disjoint a b)` in CxDecl, and CxZ seeing CxA and CxB through one parent and CxDecl
  through `(genlCx CxH CxDecl)`, the edge arriving last left both memberships believed at
  CxZ. A denial of a supertype of a cover's part rules the part out whichever of the
  cover, the membership and the denials arrives last. A declaration arriving over any
  number of memberships decides every clash it makes in its own settle and reads none of
  the memberships of terms holding one side; beside 8,192 memberships of each type it
  separates, a `disjoint` arriving and read through takes 0.85 ms against 15.6 ms.
  [nmtms.md](docs/nmtms.md#nogoods-decided-at-the-reader).

  *Class:* **Fix**.

- **A rule guarded by `unknown` or `exceptWhen` fires once a context below a clash's
  members takes the datum its guard reads OUT, in every arrival order.** With `(happy
  Zed)` in CxA, a monotonic `(not (happy Zed))` in CxD, and in CxB, which sees both, the
  rule `(pp ?x) & (unknown (happy ?x)) => (rr ?x)` and `(pp Zed)`, the denial arriving
  last left `(rr Zed)` underived at CxB. [naf.md](docs/naf.md).

  *Class:* **Fix**.

- **A separation declared below two memberships stored in one context decides them where
  it is seen, in every arrival order.** With `(a Ind)` and a monotonic `(b Ind)` in CxA
  and `(disjoint a b)` in CxB below it, CxB believed both memberships.
  [nmtms.md](docs/nmtms.md#a-defeat-is-scoped-to-its-vantage).

  *Class:* **Fix**.

- **A rule guarded by `unknown` or `exceptWhen` fires once a clash across two functors
  defeats the datum its guard reads, in every arrival order.** Beside `(disjoint happy
  sad)` and a monotonic `(sad Zed)`, the rule `(pp ?x) & (unknown (happy ?x)) => (rr
  ?x)` left `(rr Zed)` underived when `(sad Zed)` arrived after `(happy Zed)` and the
  rule; a `:default` dilemma over `(happy Zed)` resolved by a later monotonic derivation
  did the same. [naf.md](docs/naf.md).

  *Class:* **Fix**.

- **A `covering`, `separating` or `partition` declaration brings the facts already stored
  under its parts into a rule on the whole, in every arrival order.** With `(a ?x) =>
  (z ?x)` and `(c Kit)` stored, `(covering a b c)` arriving last left `(z Kit)` underived,
  as it did a rule joining over the `genl` closure. Retracting a cover while an asserted
  `(genl c a)` still reaches the whole re-derives what the cover's edge licensed, and a
  mint the cover made redundant is withheld and released as under a stated edge.
  [taxonomy.md](docs/taxonomy.md#a-cover-states-the-specialization-it-rests-on).

  *Class:* **Fix**.

- **A `functional`, `functionalInArg` or `anti_symmetric` merge follows its members'
  classes, in every arrival order.** With `(functional motherOf)`, a monotonic
  `(motherOf Kid Ann)`, a default `(motherOf Kid Bea)` and a monotonic rule
  `(birthMotherOf ?x ?y) => (motherOf ?x ?y)`, a monotonic `(birthMotherOf Kid Bea)`
  arriving last left Ann and Bea unmerged and unreported, and retracting it after the
  merge left them merged on a default member. A reader that had decided an
  `anti_symmetric` pair while it merged kept its `:default` converse believed after the
  member's class dropped. [equality.md](docs/equality.md#functional-infers-equality-instead-of-throwing).

  *Class:* **Fix**.

- **An inherited clash a context below the denial's own reads over a known-true route is
  decided there, in every arrival order.** With `(transitiveInArg heavierThan 1 genl)`, a
  default `(genl cart hauler)`, a default `(not (heavierThan cart Bone1))` and a
  monotonic `(heavierThan hauler Bone1)` in CxUniverse, and a monotonic `(genl cart
  vehicle)` and `(heavierThan vehicle Bone1)` in CxLeft below it, CxLeft believed the
  denial: CxUniverse's dilemma hid CxLeft's reading.
  [inherit.md](docs/inherit.md#a-contrary-claim-against-a-known-true-one-is-a-contradiction-and-is-reported).

  *Class:* **Fix**.

- **A `functional`, `functionalInArg`, `asymmetric` or `anti_transitive` nogood whose
  members sit in contexts neither of which sees the other is decided by each reader that
  sees them all, whatever the marked position.** A `(functionalInArg P 2)` pair of
  ternary tuples split across two contexts was never paired, since only a mark on the
  last position was asked about there. A self tuple stated in two contexts under an
  `asymmetric` mark is one sentence and forms no pair.
  [nmtms.md](docs/nmtms.md#nogoods-decided-at-the-reader).

  *Class:* **Fix**.

- **A sentence superseded by the write that stores it is not reported as leaving
  belief.** A tuple whose arrival merges its own arguments, such as the second of two
  `:monotonic` `functional` fillers, was never believed, and the change feed, `preview` and
  `edit-with-consequences!` listed it among the handles the write took out of belief.
  [feed.md](docs/feed.md#the-event-is-a-region-diff).

  *Class:* **Fix**.

- **A spelling superseded before a write and not believed after it is not reported as
  leaving belief.** A retraction that un-merges two terms gives a displaced spelling back,
  and one the reader then decides OUT, or one a standing merge keeps superseded, was
  listed among the handles the write took out of belief by the change feed, `preview`
  and `edit-with-consequences!`.
  [nmtms.md](docs/nmtms.md#the-published-window).

  *Class:* **Fix**.

### Fixes: performance

- **A `genl` edge puts the facts below it back on the chaining agenda only when a rule
  reads a term at or above its upper end.** The edge sent every believed fact of its
  lower end's spec subtree to forward chaining on every write, whether or not any rule
  could newly match one, so an edge under a type above most of the vocabulary chained
  most of the store. Over 1,024 facts below the edge and a rule elsewhere, a `genl`
  assert costs 0.25 ms where it cost 7.5 ms. [taxonomy.md](docs/taxonomy.md#what-a-batch-of-edges-costs-the-passes-that-read-it).

  *Class:* **Fix**.

- **A `genl` edge reads the facts below it for a merge only when a `functional`,
  `functionalInArg` or `anti_symmetric` mark stands at or above its upper end.** The edge
  handed every stored fact of its lower end's spec subtree to the merge derivations
  whenever any such mark was declared anywhere, and the antisymmetric arm offered each
  fact to every candidate family, so an exact-arity membership recomputed its predicate's
  arity candidates; on a large store, an edge under a type above most of the vocabulary
  did not finish in 45 minutes. An edge whose upper end has no length bound at or above it recomputes no arity
  candidate. Over 1,024 memberships below the edge, an unchained `genl` assert costs
  0.28 ms where it cost 10.0 ms. [taxonomy.md](docs/taxonomy.md#what-a-batch-of-edges-costs-the-passes-that-read-it).

  *Class:* **Fix**.

- **A `genl` edge's stratification check walks once, from the rules the edge reaches.**
  The check walked the rule graph once from every stored rule carrying a negative edge,
  so its cost grew with those rules times the graph each reached, and a cycle through
  negation already stored (the import path can write one) refused every `genl` edge. It
  now walks once, from the edge, and finds only cycles through the edge; a `genlCx` edge
  is not walked. Beside 128 excepted rules the edge does not reach, a `genl` assert costs
  0.86 ms where it cost 9.2 ms.
  [exceptions.md](docs/exceptions.md#a-taxonomy-edge-closes-a-cycle-too).

  *Class:* **Fix**.

- **The stratification walk reads the upward closure of each rule's consequent, not the
  spec closures of what each rule reads.** A `genl` edge's check and a rule's check fanned
  every predicate a reached rule reads over its whole spec closure, with a rule-index read
  per spec, so a walk into a large rule component reading broad types ran for minutes. The
  walk now runs against the graph's edges, from a rule to the readers of each predicate
  at or above its consequent, and costs the rules it reaches. Over a chain of eight rules
  whose types have 64 specs each, a `genl` edge's check reads at 1.15x its cost at 4 specs,
  where it read 3.96x. [exceptions.md](docs/exceptions.md#the-search).

  *Class:* **Fix**.

- **A reader's later rounds decide only the nogoods their region reaches.** Every round of
  a reader's withdrawal read the belief and class of each member of every nogood and
  decided it again, though a nogood with no member in the round's region keeps the
  verdict it had in the round before. Beside 20,000 `:default` dilemma pairs and 200
  decided self tuples, a reader's first withdrawal decides 20,200 nogoods where it decided
  40,200, and costs 111 ms where it cost 153 ms. [nmtms.md](docs/nmtms.md#a-defeat-is-scoped-to-its-vantage).

  *Class:* **Fix**.

- **A reader reads an arity candidate's binding once per shape, and no tuple of a shape
  the binding holds.** A tuple is a candidate when some length bound above its functor
  differs from its own, and every reader read the record of every candidate tuple and
  asked its functor's binding per tuple, though a functor's own binding holds the tuples
  of its own length. A functor binding nothing now stops reading the bindings above it at
  the second length it sees. Beside 6,400 such tuples and 200 decided self tuples, a
  reader's first withdrawal costs 1.0 ms where it cost 4.9 ms; on a store holding 1.1M
  candidate tuples of 8,003 shapes, a reader's first withdrawal costs 31 to 36 s where
  it cost 90 to 101 s. [nmtms.md](docs/nmtms.md#nogoods-decided-at-the-reader).

  *Class:* **Fix**.

- **A reader re-reading its definitional nogoods asks each member's violations once, and
  re-reads them only in a round that withdraws another ground.** Each nogood re-asked
  its members' violations, so a term holding `p` pairwise separated types cost `p`
  violation reads per nogood, and every later round re-asked every nogood whether or not
  it withdrew a ground. A `recover` whose first discovery reader decides the 1,128
  nogoods of one term holding 48 such types costs 0.17 ms per nogood where it cost
  1.16 ms. [nmtms.md](docs/nmtms.md#a-defeat-is-scoped-to-its-vantage).

  *Class:* **Fix**.

- **A KB opened from its reasoning image compares the membership candidates'
  separation stamp by identity after its first read.** The image holds the stamp and the
  taxonomy's declaration rosters as two equal copies, and every scoped read compared them
  entry by entry. With 1,600 `disjoint` declarations, a thousand reads cost 1.7 ms where
  they cost 165 ms. [nmtms.md](docs/nmtms.md#how-a-settle-finds-the-clashes).

  *Class:* **Fix**.

- **A discovery that reads a detached taxonomy syncs the nogood candidate index once, not
  once per question.** Where a verdict withdraws a taxonomy declaration at its own
  context, the inherited-clash discovery reads a taxonomy copy holding it, and the copy
  and the live taxonomy re-synced one shared candidate index in turn. A `recover` over 400
  preserved claims and 400 terms a withdrawn `disjoint` separates costs 0.15 ms per claim
  where it cost 5.6 ms. [nmtms.md](docs/nmtms.md#the-runtime-view).

  *Class:* **Fix**.

- **`recover`'s inherited-clash discovery asks the preserved predicates' stored claims and
  reads no record of any other sentex.** Its region is the whole store, and it read the
  record of every handle in it to find the claims of a preserved predicate. [nmtms.md](docs/nmtms.md#the-inherited-clash-memo).

  *Class:* **Fix**.

- **A discovery pass reads a preserved predicate's stored extent once, not once per
  claim it asks.** Each question about a stored claim filtered the predicate's whole
  extent, so a pass over n claims cost n² row tests. A `recover` over
  2,000 claims each under 60 shared types costs 0.15 ms per claim where it cost 10.6 ms.
  [inherit.md](docs/inherit.md#what-one-question-costs).

  *Class:* **Fix**.

- **A discovery question walks a goal term's `genl` reach to a bound and tests membership
  past it, never building the term's closure.** Each question built the supertype
  closure of every argument term of every stored claim of a preserving predicate,
  through a closure cache that could not hold them. A reach, scoped or unscoped, is now
  walked up to 1,024 terms; past that a membership is a memoized `genl?` walk, a term
  asked twice reads its reach whole once, and a pass holds those reaches in a weighted
  LRU and the edges each walk filters in a neighbour cache, both dropped when the
  question or pass ends. The claim set is unchanged.
  [inherit.md](docs/inherit.md#what-one-question-costs).

  *Class:* **Fix**.

- **A lift sweep over stored facts asks once per stating context whether it sees
  CxUniverse.** The sweep a `decontextualized_predicate` declaration arriving last runs,
  and the one `recover` runs, asked `sees?` per fact. Where an `except` targets a
  `genlCx` edge, each `sees?` reads the visibility of every edge supporter on its path.
  With 2,000 facts stated under a 64-context chain, the `recover` sweep costs 0.6 ms per
  hundred facts, where it cost 13.5 ms.
  [contexts.md](docs/contexts.md#why-cxuniverse-and-not-a-target-the-declaration-names).

  *Class:* **Fix**.

- **A settle whose region holds a deleted record asks the inherited-clash discovery only
  what that deletion moved.** A retracted fact, or a firing a guard block swept, left a
  handle with no record in the region, and the discovery then asked every stored claim it
  carried an entry for again; after a `recover` that is every claim of a preserved
  predicate. The removal now records the departing sentence for the discovery to read. A
  `retract!` of an unrelated fact beside 512 carried entries costs 0.67 ms, where it cost
  111 ms; the clashes found are unchanged.
  [nmtms.md](docs/nmtms.md#the-inherited-clash-memo).

  *Class:* **Fix**.

- **The settle after a `genl` or `genlCx` edge moves re-asks the declarations waiting on
  an unmintable type from one walk of `thing`'s subtypes.** It walked up from each
  waiting declaration's type, which costs the type's whole ancestor set when the answer
  is no, and sorted every waiting entry on each pass before comparing a stamp, so the
  first settle after any taxonomy edge paid one ancestor walk per waiting declaration.
  [exceptions.md](docs/exceptions.md#a-refused-firing-is-remembered-as-bindings).

  *Class:* **Fix**.

- **`recover` re-notes the declarations waiting on an unmintable type from one walk of
  `thing`'s subtypes.** It asked each stored `arg`, `genlArg` and `interArg` declaration
  whether its type reaches `thing` by walking up from that type, which costs the type's
  whole ancestor set when the answer is no. The declarations noted are the same.
  [exceptions.md](docs/exceptions.md#a-refused-firing-is-remembered-as-bindings).

  *Class:* **Fix**.

- **A reader's withdrawal computed during a settle stays cached after it.** Each point of
  a settle that reconciles the withdrawal cache checked every entry against the settle's
  whole touched window, so an entry a pass computed after a write reached the reader was
  dropped at the next reconcile for that same write, and the next read computed it again.
  The cache now marks the window when it reconciles (`jtms/touch-mark`) and checks what
  was recorded after the mark. A batch that stores a nogood a reader decides and runs two
  passes keeps the 11 entries its settle computed, where it dropped all 15 it computed;
  the first read after it at a context seeing 4,096 `except`s costs what it costs at 32.
  [nmtms.md](docs/nmtms.md#the-withdrawal-cache).

  *Class:* **Fix**.

- **A later pass of one settle asks the inherited-clash discovery only what the earlier
  passes moved.** Every pass read the settle's whole touched window, so a pass after the
  first asked again every claim of a preserved predicate the first pass had asked, and a
  `recover`, whose window is the store, asked every such claim once per pass. The
  discovery now marks the window when it asks (`jtms/touch-mark`) and reads what was
  recorded after that mark. A batch of 60 claims whose settle runs two passes asks 63
  questions, where it asked 124; the clashes found are unchanged.
  [nmtms.md](docs/nmtms.md#the-inherited-clash-memo).

  *Class:* **Fix**.

- **The durability tick's compaction probe reads no record index.** The record store
  answered each dead-ratio probe by walking every `.idx` in full under the kind lock;
  each kind now keeps its live frame bytes as a counter its writes maintain, so a probe
  reads that counter and the log's length. On a 500k-record store a probe takes 10 µs
  and reads no idx byte, where it took 19 ms and read 12 MB. The ratio, and so every
  compaction decision, is unchanged.
  [storage.md](docs/storage.md#the-on-disk-backend-disk).

  *Class:* **Fix**.

- **A reader reads a length binding above a functor without building the functor's
  closure.** Each reader deciding the arity family built the whole `genl` closure of
  every candidate functor that binds no length of its own; it now reads that closure cut
  to the predicates binding a length, shared by every reader of a settle, and checks
  reachability only when the reader misses a context stating a `genl` edge. Reading
  `conflicts` over 60 contexts holding memberships of a 300-type chain under a type
  bound to another length takes 135 ms against 300 ms.
  [nmtms.md](docs/nmtms.md#nogoods-decided-at-the-reader).

  *Class:* **Fix**.

- **An unrelated write beside decided nogoods reads none of them.** Each settle pass read
  every candidate of the reader-decided families to find where a firing could be lost,
  and every withdrawal-cache check compared the flat declaration caches entry by entry.
  Beside 800 negation pairs a reader decides, an unrelated assert takes 0.30 ms, as at
  100 pairs, where it took 0.80 ms; flipping one of 4,000 `disjoint` declarations costs
  what flipping one of 500 does.
  [nmtms.md](docs/nmtms.md#where-the-layer-stops).

  *Class:* **Fix**.

- **A retraction that releases a firing re-joins no other rule over its whole extent.**
  When the released firing placed a sentence an `exceptWhen` rule reads, the settle
  re-joined that rule over every fact it had matched in the same pass; beside 3,200 such
  facts the retraction takes 6.0 ms against 130 ms.
  [exceptions.md](docs/exceptions.md#re-chaining-what-was-released-not-what-was-touched).

  *Class:* **Fix**.

- **A write a reader decides reads again only the readers it reaches to publish what it
  moved.** A self tuple arriving under an `irreflexive` mark in a context of its own,
  beside n contexts each holding a consequence a reader withdraws, takes under 0.45 ms at
  n = 128 and at n = 1,024, where it took 16.6 ms at 64 and 224 ms at 256.
  [nmtms.md](docs/nmtms.md#the-published-window).

  *Class:* **Fix**.

- **A denial of a term that holds no membership reads none of the term's other
  denials.** Beside 2,000 stored denials of one term, one more takes 0.13 ms against
  1.47 ms. [nmtms.md](docs/nmtms.md#nogoods-decided-at-the-reader).

  *Class:* **Fix**.

- **A load in which every type binds its own length is linear in the bindings.** A length
  binding arriving above types that already hold that length reaches none of them, where
  it recomputed the arity candidates of every type below it. Loading 4,000 types in forty
  levels, each with `(arity t 1)`, takes 4.0 s against 53.8 s.
  [taxonomy.md](docs/taxonomy.md#arity).

  *Class:* **Fix**.

- **A tuple under a `functional`, `functionalInArg`, `asymmetric` or `anti_transitive`
  mark reads the stored tuples its own arguments name, and no extent of its predicate.**
  Beside 8,192 tuples under `(functionalInArg P 3)`, a tuple on a determinant of its own
  takes 0.20 ms against 3.23 ms. A mark arriving offers its predicate's stored tuples
  whole, so the `:partner-sweep-truncated` notice is no longer filed.
  [nmtms.md](docs/nmtms.md#nogoods-decided-at-the-reader).

  *Class:* **Fix**.

- **A pattern whose ground arguments lead reads the trie under them, not two argument
  roots.** `(scoreOf Team Year ?v)` read from a context walks the stored tuples extending
  `(scoreOf Team Year …)` where it intersected the postings of `Team` and `Year`, so the
  `functionalInArg` check at the last argument no longer grows with how widely both terms
  are used. Beside 32,768 tuples whose two leading terms each hold 1,638, a tuple on a
  determinant of its own takes 0.24 ms against 0.70 ms.
  [indexing.md](docs/indexing.md#retrieval-from-the-roots-resmatch-one).

  *Class:* **Fix**.

- **An assert beside negation pairs stored in two contexts no longer re-finds every pair
  on each settle.** A stored `(not B)` and a stored `B` in two contexts neither of which
  sees the other are decided by each reader that sees both, from an index kept where
  either is stored or removed.
  Beside 800 such pairs an unrelated assert takes 0.30 ms against 11.06 ms.
  [nmtms.md](docs/nmtms.md#nogoods-decided-at-the-reader).

  *Class:* **Fix**.

- **An assert beside rules holding many refused firings no longer reads every refusal on
  each settle pass.** A pass looked through every rule's refused firings for the lift,
  mint and argument-conviction entries it re-asks. Beside 32,000 `unknown` refusals an
  unrelated assert takes 0.18 ms against 9.0 ms.
  [exceptions.md](docs/exceptions.md#a-refused-firing-is-remembered-as-bindings).

  *Class:* **Fix**.

- **A settle that moves no equality premise reconciles no supersession, and the change
  feed and `edit-with-consequences!` name the spelling a merge displaces.** The spellings
  a merge displaces are reconciled where a sentence that moves them is stored or removed,
  and a settle reconciles them only after an `except` moved or an equality edge off the
  forced-monotonic roster moved in belief, so an unrelated assert beside standing
  `rewriteOf` merges no longer compares their preferences on each settle. The settle
  publishes each spelling a merge displaced since the last settle, so `(sameAs Pref Dep)`
  over a stored `(dog Pref)` reports `(dog Pref)` under `:believed-removed`, as `preview`
  does. [equality.md](docs/equality.md#what-a-merge-does).

  *Class:* **Fix**.

- **A separation question reads a type's supertypes cut to the separable ones, not its
  whole closure.** A disjointness frame, unscoped or read at a context or an ancestor
  set, read the whole supertype closure of each type it framed, so a sync over every
  type built one closure per type. It now reads only the supertypes declared disjoint,
  members of a disjoint metatype, sibling-disjoint parents and partition parts, held in
  the closure cache or the pass cache; only the sibling arm reads a whole chain. A `genl`
  component the reader sees whole is read as one unit.
  [taxonomy.md](docs/taxonomy.md#disjointness).

  *Class:* **Fix**.

- **A moved `genlCx` edge asks only the contexts holding a mint whether they see it.** The
  mints a moved `(genlCx sub super)` can make redundant were found by reading every
  context below `sub`, which filters each descendant by its own `sees?` walk while an
  `except` reaches a `genlCx` supporter. The contexts are now read off whichever side is
  fewer: the mint roster's contexts that see `sub`, or the contexts below it.

  *Class:* **Fix**.

### Fixes: errors and reporting

- **The `:closure-answers` row of `caches` reports the bound a binding of
  `*closure-answer-limit*` sets.** The row reported 100,000 members under a binding the
  store path enforced. [caches.md](docs/caches.md).

  *Class:* **Fix**.

- **`siblingOf`'s comment says the shared parent is biological (#98).** `siblingOf` is
  read off `parentOf`, whose comment already said so; the comment now also says that
  chosen or elective kinship is not this predicate. No rule, argument constraint or
  property moves.

  *Class:* **Fix**.

### Tooling, CI and benches

- **`lein perf --list` prints each check's name and claim and measures nothing.** The
  wrapper let `--list` past its worktree refusal and the harness refused it as an unknown
  flag; `--list` now runs anywhere and writes no log or ledger row.

  *Class:* **Fix** (developer tooling; no public function moves).

## 0.22.0 — 2026-09-29 — "prove answers what ask answers, a rule record names the engines that run it, and a clash is decided where its grounds come into view"

**57 entries** — 13 Breaking, 8 Refusal, 8 Additive, 28 Fix. `prove`, `ask` and `query`
answer the entailed goal where they answered the stored one, and a rule record holds
`:engines` and `:effect` in place of `:direction`, `:assumption` and `:constraint`. A
clash is decided where its grounds come into view, `violations` no longer files the
clashes the settle decides, and an argument-type mint gives way to a more specific
membership. An ASP solve stops at a conflict limit under a fixed seed, the LLM stack and
the taxonomy's scoped closure budget are gone, and a failed background rebuild ends
read-only. Malformed rules, an `except` naming no handle, a damaged log frame and unusable
server or browser input are refused; `set/solveRule`, the six named points of a temporal
thing, `rebuild-progress` and browser extensions are new.

*Breaks:* `prove`, `provable?`, `prove-within`, `resume`, `ask`, `query`, `query?`,
`query-status`, `search-tree`, `compare-tacticians`, `(:direction`, `(:assumption`,
`(:constraint`, `RuleSentex`, `violations`, `contradictions`, `assert`,
`:exposure-truncated`, `:not-defeasible`, `handle-of`, `sentexes-matching`, `why`,
`VAELII_PRUNE_SUBSUMED_MINTS`, `:disjoint`, `check`, `watch`, `VAELII_LLM_PROVIDER`,
`vaelii.llm.provider`, `VAELII_LLM_LIVE`, `VAELII_OLLAMA_HOST`, `VAELII_OLLAMA_MODEL`,
`VAELII_OLLAMA_GENERATION_MODEL`, `VAELII_OLLAMA_NUM_CTX`, `VAELII_OLLAMA_KEEP_ALIVE`,
`OLLAMA_HOST`, `ANTHROPIC_API_KEY`, `ANTHROPIC_AUTH_TOKEN`, `ANTHROPIC_BASE_URL`,
`/propose`, `:llm`, `vaelii.host.llm`, `with-model`, `:taxonomy-scoped-closures`,
`*scoped-memo-budget*`, `vaelii.memo.budget`, `open-kb`, `:recover? :background`,
`rebuild-progress`, `lein cli`, `resolve-by-majority`, `admin-principal`,
`register-agent`, `set-trust!`, `ask?`, `ask-within`, `VAELII_ASP_SOLVE_LIMIT`, `settle`,
`do/label`, `do/labeling`, `do/classify`, `import!`, `thereExists`, `forall`,
`set/assumptionRule`, `set/hardConstraint`, `set/softConstraint`, `edit!`, `close!`,
`ClosedChannelException`, `Stream Closed`, `:overlay`, `:space`, `:dir`, `:base-stores`,
`set-cache-limit`, `--dir`, `vaelii.serve/start`, `vaelii.web/start`, `/levels`,
`/inference`, `/network`, `/term`, `/find`, `/assert`, `/edit`, `/edit/preview`,
`/retract`, `/sentex/:id`, `/why/:id`, `/justification/:id`, `/demo`, `/reasoning`,
`/jobs/cancel`, `/kbs/load`, `/kbs/unload`, `/kbs/activate`, `/kbs/export`,
`/caches/scale`, `POST /op`, `unload!`

## 0.21.0 — 2026-09-23 — "a definitional clash is decided at the context that sees it whole, and a relation can state that its arguments commute"

**61 entries** — 5 Breaking, 3 Refusal, 12 Additive, 41 Fix. A definitional clash whose
halves sit in two contexts is weighed under `:refuse` at the context that sees both, as
`:arbitrate` already did, and leaves `violations`; under `:arbitrate` a refusal reads the
derivation behind a clash as well as the fact it opposes, and `refuses-assert?` takes the
asserting context. A firing over an inherited claim is placed by the route that places it
highest, a context that disbelieves a `genl` or `genlCx` edge stops reaching over it, and a
firing whose route was defeated is re-derived over any second route its reader reaches.
`IndexStore` gains `unary-sentexes-with-arg` behind index layout 3, `KvBackend` names no
index family, and `ArgColumns` is gone. `commutative`, `commutativeInArgs`,
`commutativeInArgAndRest`, `covering`, `separating`, `partition`, `interArgs` and
`interArgAndRest` join the vocabulary; `watch` refuses an `(and …)` conjunction, one CLI
argument is one form, and `lein cli export --format` takes `text` or nothing.

*Breaks:* `violations`, `contradictions`, `assert`, `:constraints :arbitrate`, `:disjoint`,
`:functional`, `genl`, `check`, `refuses-assert?`, `sentexes-matching`,
`sentexes-in-context`, `IndexStore`, `unary-sentexes-with-arg`, `ArgColumns`,
`arg-scoped-members`, `arg-scoped-intersect`, `watch`, `lein cli`, `read-arg`, `--format`

## 0.20.0 — 2026-09-17 — "a defeated fact stays believed outside the context that decided the clash, and the belief record is renamed Reasoning"

**42 entries** — 6 Breaking, 1 Refusal, 15 Additive, 20 Fix. A clash's defeated member is
disbelieved only at the vantage that sees the clash and below it, a conclusion follows its
reader so an `except` subtracts what rests on what it hides, `contradictions` takes a
reader, and `do/labeling` commits inside its context so two labelings stand side by side.
The record holding a KB's network, taxonomy and derived atoms is renamed `Reasoning`, its
durable image moves to `<dir>/reasoning/`, and seven extension-point protocols move to
held namespaces the development reloader never re-evaluates. A rule is refused an
`(ist Ctx S)` consequent; `open-kb` takes `:recover? :background`, `belief-status` reports
`:withdrawn?` and `:scoped-vantages`, and `lein cli upgrade` brings a store's images up to
the running build. `store-backend` names the backend a directory was written by, the
daemon, the CLI and the browser open a store under it, and only
`scripts/start-vaelii-dev.sh` turns hot reload on.

*Breaks:* `in?`, `believed?`, `except`, `sentexHandle`, `do/labeling`, `contradictions`,
`belief-image`, `:belief-image`, `belief_image`, `types.belief`, `map->Belief`,
`derived-state`, `belief-fingerprint`, `register-belief-image!`, `:belief-fp`, `Prover`,
`SupportingProver`, `Solver`, `SnapshotSink`, `SnapshotSource`, `KvBackend`, `kv-get`,
`:reload?`, `assert`, `assert-rule`, `check`

## 0.19.1 — 2026-09-14 — "five readers repaired after rules lost their sentence field, and the source digest re-parses only files that changed"

**3 entries** — 3 Fix, each a regression 0.19.0 shipped. Five readers that still asked a
rule record for the `sentence` slot 0.19.0 dropped — the NAT teardown, the index
fingerprint, the retired-spelling filter, the vantage supporter check and the QCN
refuted-pair read — take the `implies` form from `sentence-of` instead, so an index dump's
fingerprint over rules is again the digest earlier releases wrote. The source identity
memoizes each engine namespace's parse and re-reads only a file whose stat and digest
moved, taking a call from 1.1 s to 9 ms. The shipped `CxBiology` stores no
`(hasCapability ?x travelling)` record: the capability hierarchy answers it at retrieval,
where a forward rule had stored a second record and justification per flyer.

## 0.19.0 — 2026-09-13 — "stores reopen from a saved belief image instead of recomputing it, and records drop the fields that repeated their own sentence"

**23 entries** — 5 Breaking, 4 Refusal, 4 Additive, 9 Fix, 1 neither label. A
`:disk-snapshot` KB installs a stored belief image at open in place of a full `recover`,
keyed on the records fingerprint, the source identity and the policies, and declines to an
ordinary recover when any of the three moved. The sentex records stop restating what the
store already holds: a rule map carries no `:sentence` and a literal no `:polarity`, a
justification names its rule once as `:informant` and carries no `:out`, and `sentence-of`
reconstructs each form. `bravely` and `cautiously` classify a labeling's dilemmas with no
ASP backend, a `genlCx` cycle is refused at assert as a `genl` cycle already was, and three
write paths that stored a record no belief-filtered read could find now refuse. Seven hot
paths drop work that changes no answer, an operation log records a `:disk-snapshot` KB's
public writes behind a seal, and a settle-phase instrument splits a settle's wall clock
into four cost centres. The engine's `project.clj` names no `vaelii-foreign` coordinate,
so an engine release no longer forces a plugin release.

*Breaks:* `:refuse`, `violations`, `sentex`, `sentexes-matching`, `canonical-sentex`,
`:sentence`, `:polarity`, `bravely`, `cautiously`, `justification`,
`supporting-justifications`, `dependent-justifications`, `vaelii.belief.snapshot`,
`genlCx`, `assert-inert`, `cardAtMost`, `cardAtLeast`

## 0.18.1 — 2026-09-11 — "every entry point refuses an out-of-range value by name, and the upper ontology splits things into spatial and temporal"

**14 entries** — 2 Refusal, 4 Additive, 6 Fix. Every bounded entry point refuses a value
outside its domain by name, reading one shared domain table, and `assert-inert` refuses an
open sentence. The upper ontology divides `thing` by space and time, renames
`spatial_thing` and `temporal_thing` to `spatial` and `temporal`, and adds a `CxUniverse`
collector context. A process-wide cache profile scales every derived cache's bound, and a
memory-pressure guard the servers install shrinks the caches as the old generation fills
and grows them back as it drains. A reified NAT or context constant is named by the
SHA-256 of its expression, so the same expression reifies to the same constant across
processes, and the one-shot clingo solve injects its ground program through the backend
accessors rather than a temp file.

*Breaks:* `:counters?`, `:believed?`, `:max-cost`, `:max-depth`, `:max-term-growth`, `add-evaluatable`, `assert-inert`, `describe`, `why-not`, `spatial_thing`, `temporal_thing`

## 0.18.0 — 2026-09-09 — "argument-type declarations create the types they constrain, and rules forward-chain only when asked to"

**16 entries** — 3 Breaking, 1 Refusal, 9 Additive, 3 Fix. Assertive argument types become
the default reading: an `arg` / `genlArg` / `interArg` declaration mints the type it
constrains rather than only testing for it. A bare `implies` rule defaults to `:backward`
and materializes nothing, and `set/forwardRule` adds forward chaining to the backward use
rather than replacing it, so a rule forward-chains only where its author asks. The arity
vocabulary gains a runtime floor — a variable-arity application below its `arityMin` is
refused — and `admitsArgnum` answers a position query from the declared arity. New
declaration vocabulary types a whole variable-arity tail (`args`, `argsGenl`, `argAndRest`,
`argAndRestGenl`) and names an `intersection` kind that derives its taxonomy edges, and new
readers report the brave and cautious status of a labeling dilemma, a cardinality bound over
ASP choice heads, and the subsumption status of every type pair. A state-of-affairs and
causality cluster joins the upper ontology in CxAbstract.

*Breaks:* `VAELII_ASSERTIVE_ARG_TYPES`, `(implies` asserted bare, `set/forwardRule`,
`arityMin`, `(lessThan`, `(greaterThan`, `(termsRelated`, `(functionCorrespondingPredicate`,
`vaelii.impl.llm.protocol/Provider` (now `vaelii.host.llm.protocol/Provider`; the
entry was added after the release)

## 0.17.0 — 2026-09-06 — "arity becomes declared vocabulary on every relation, and declarations stop restating what they already imply"

**14 entries** — 1 Breaking, 4 Refusal, 4 Additive, 5 Fix. A declaration that restates
what the taxonomy already concludes turns that conclusion into a precondition, so the
arrival order of two assertions decides which facts a KB holds. Four entries retire such a
declaration — on `genl`, on fifteen unary marks, on six arity marks, and in the `predAll`
pair's third argument — and the arity vocabulary underneath is rebuilt so `relation` is
the common parent of `predicate` and `function` and every relation lands in exactly one
arity policy. `predAllSpecified` and `predSpecifiedAll` go binary and derive the filler
type from the predicate's own slot contract. Three composite function marks — `injection`,
`surjection` and `bijection` — arrive as one declaration each, a `genlCx` edge's merge
sweep stops growing with the KB, and a late `symmetric` declaration folds a mirrored pair
no earlier version could fold.

*Breaks:* `(predAllSpecified`, `(predSpecifiedAll`, `specified-violations`,
`all-specified-violations`, `(binary_predicate P)` beside `(variable_arity P)`,
`:arg-type`, `*assertive-arg-types?*`, `VAELII_ASSERTIVE_ARG_TYPES`,
`(genlArg genl 1 thing)`, `(arg symmetric 1 predicate)`, `(arg functional 1 predicate)`

## 0.16.0 — 2026-09-04 — "the predAll quantifier family, refusals that carry a type, and declarations that apply to facts already stored"

**18 entries** — 3 Breaking, 1 Refusal, 7 Additive, 7 Fix. The `predAll` quantifier
family lands in all eight cells. Three refusals stop answering with the wrong keyword:
an unpinned indeterminate term is not provably `different` from anything, a missing
adapter is not an unknown backend, and a wrong operand count is not an unknown option.
Declarations arriving after the facts now reach them — a `(symmetric P)` mark folds
records already stored, a computed `genlCx` edge runs the reconcilers a stated one runs,
and `quotedArg` is answered along the `genl` closure. Every refusal declares what its
`ex-data` carries, and a throw that drops a key fails the build.

*Breaks:* `(different`, `indeterminate_term`, `:unknown-backend`, `:sqlite`, `:pg`,
`:unknown-option`, `:not-stratified`

## 0.15.0 — 2026-09-01 — "definitions that compute their own answer, and two renames"

**7 entries** — 2 Breaking, 5 Additive. Definitional membership is answered at query
time rather than only by a forward rule. Two renames: the sentex polarity slot is
`:polarity`, and the `AtomicSentex` record is `LiteralSentex`. A unary predicate is
snake_case and `assert` enforces the spelling in both directions, which retired the
camelCase marks. CxCore names the expression kinds and gains a curation vocabulary.

*Breaks:* `unaryPredicate`, `reifiableFunction`, `abduciblePredicate`,
`closedExtentPredicate`, `disjointMetatype`, `siblingDisjoint`, `warmBlooded`, `:truth`

## 0.14.0 — 2026-08-29 — "the index image becomes a storage backend, and the heap it no longer needs"

**10 entries** — 1 Refusal, 1 Additive, 5 Fix. The mapped index image becomes a backend
of its own, `:disk-snapshot`, rather than a property of the disk store, and stops
carrying the argument roots into heap. The disk store's live-handle sets become
compressed bitmaps. The writer refreshes a drifted image mid-life and can be told not
to. A `functionalInArg` declaration arriving after the facts it convicts is reported
rather than silently late. Neither adapter shipped at this version; both stayed at
0.13.0.

*Breaks:* `vaelii.index.snapshot`, `:argument-family-ceiling`

## 0.13.0 — 2026-08-25 — "calendar time, joined queries, and entry points that refuse invalid input"

**95 entries** — 5 Breaking, 14 Refusal, 32 Additive, 22 Fix. The largest release:
calendar time, joined queries and a sweep through the entry points that refuse.
`CxChange` ships an event calculus, calendar constructors give a date its own endpoints
so it orders itself, and a metric constraint narrows an interval relation. `or` is
accepted in a rule antecedent, stored as one rule per alternative, and refused as a
goal. Every search entry point takes a bound and the daemon holds them to its ceiling.
Fourteen refusals close inputs whose acceptance stored junk, and the `:disk` and
`:pg-disk` pairings are renamed to say that both halves are out of core.

*Breaks:* `:disk`, `:pg-disk`, `VAELII_TEST_BACKEND=disk`, `edit!`,
`edit-with-consequences!`, `apply-proposal!`, `contexts`, `count-in-context`,
`contextDenotingFunction`, `lein cli load`, `prove`, `provable?`, `query`, `argue`,
`forward-chain`, `ask`, `ask?`, `query-plan`, `abduce`, `sentexes-matching`,
`handle-of`, `assert`, `load-text!`, `lein cli assert`, `unaryPredicate`,
`binaryPredicate`, `ternaryPredicate`, `/kbs`, `lein serve --listen <flag>`,
`vaelii.client/client`, `:timeout-ms`, `:token`, `dereference`, `resolve-by-locator`,
`set-trust!`, `trust-of`, `display-name-of`, `:reserved-family` (a dense index past its
`(predicate, position)` ceiling is `:argument-family-ceiling`), `do/label` over an
`assumptionRule` with a negated head (`:choice-head-not-positive`); these two entries
were added after the release

## 0.12.0 — 2026-08-23 — "query contexts, bulk loading, and types for literal values"

**99 entries** — 3 Breaking, 3 Refusal, 7 Additive, 5 Fix. Query contexts, bulk loading,
and a literal's type. `resultIsa` and `resultGenl` become `result` and `genlResult`; the
four function marks classify what they mark, and the reifiability criterion is written
down. A records read stays lazy, and a proof's witness is one of its bindings. Three
reads that could not answer the question stop answering empty. First release of the two
adapters, `com.vaelii/postgres` and `com.vaelii/sqlite`, each at this version.

*Breaks:* `resultIsa`, `resultGenl`, `reifiableFunction`, `unreifiableFunction`,
`quotingFunction`, `contextDenotingFunction`, `ist`, `:proof?`, `?ctx`,
`qualitative-network`, `possible-relations`, `:arg-type`, `:quoted-arg-type`, `result`,
`genlResult`, `:arg-genl`, `character_string`, `:pg-disk`, `:dir`,
`:stale-index-records`, `register-modal-predicate!`

## 0.11.0 — 2026-08-22 — "contradiction solving, arrival order, and the durable log"

**67 entries** — 2 Breaking, 4 Additive. Contradiction solving, arrival order, and the
durable log. `antiTransitive` convicts the chain it forbids rather than being declared
and deferred. Definitional collection relations tie membership to a defining condition,
and sibling disjointness lets a collection's specializations separate themselves, with
an escape hatch for a pair that must overlap. A computed predicate or function is
registered in one line.

## 0.10.0 — 2026-08-20 — "more than one agent over one knowledge base"

**9 entries** — 4 Additive. Koinii: several agents coordinate over one shared knowledge
base, with belief projection for what each agent holds true. A context can be a reified
function application whose `genlCx` edges compute themselves. Mention-opacity arrives —
a quoting function reads its argument by spelling — and `quotedArg` types an argument
against a syntactic type. The `argIsa`, `argGenl` and `interArgIsa` spellings become
`arg`, `genlArg` and `interArg`.

## 0.9.0 — 2026-08-17 — "the truth-maintenance network defaults to dense"

**15 entries** — 5 Breaking, 8 Additive. The dense truth-maintenance network becomes the
default and gives a concurrent reader a consistent view. Four relation properties are
enforced rather than documented. A subsumption rests on its strongest route rather than
its shortest. An algebraic property becomes one predicate instead of a mark and a twin,
which retired the `...Predicate` spellings.

*Breaks:* `defeat-class`

## 0.8.0 — 2026-08-14 — "predicates inherit down the hierarchy"

**50 entries** — 1 Breaking, 1 Additive. Predicates inherit down the hierarchy. A KB
whose declared hazards are unresolved refuses writes rather than accepting them
unchecked, and a derived record's teardown is refused where belief was never built.
`check` and `check-edit` answer for the entry point they mirror. Five refusals close
recovery paths that believed records the store did not hold.

*Breaks:* `:unrecovered-kb`, `write-hazards`, `note-hazards!`, `contradictions`,
`violations`, `:constraint-exposure`

## 0.7.0 — 2026-08-12 — "contexts get a single naming convention"

**2 entries.** Contexts get one spelling. A context name is `Cx`-prefixed rather than
`Context`-suffixed, and the context-transitivity predicate is `genlCx`.

## 0.6.0 — 2026-08-12 — "stored rules become first-class"

**22 entries** — 2 Breaking, 4 Refusal, 2 Additive. Stored rules become first-class: a
rule can conclude a rule, and a rule carries a handle, TMS support and retraction with
no rule-specific machinery. A capability claim about a kind is `capabilityType` and
about a member is `hasCapability`. A NAF guard written as a conjunction now guards, and
the strictest policy stops being the leakiest.

## 0.5.1 — 2026-08-11 — "faster writes, and more of the engine exposed to monitoring"

**15 entries.** Faster writes, more to watch. A settle pays for the region it moved
rather than for what the KB holds. The arbitrating half of a bounded pass says when its
budget stopped it. Four places where arrival order decided an answer are closed.

## 0.5.0 — 2026-08-07 — "operating the engine as a service"

**23 entries.** Operating the engine as a service. The daemon authenticates and refuses
to bind an address without a token. One space number names a KB's stores, `:space`,
replacing the separate record and index spellings. `context-size` becomes
`count-in-context`, `different` descends into compound arguments, and a name can carry a
sense and a lexeme.

*Breaks:* `:record-space`, `:index-space`, `docs/storage.md`

## 0.4.0 — 2026-08-05 — "correctness fixes against the invariants"

**33 entries.** Correctness fixes against the four invariants. A conjunctive query could
answer nothing while each of its conjuncts answered, and no longer does. `assert`
refuses a sentence that is not an s-expression, an `exceptWhen` query's literals are
held to the naming invariants, and an `edit!` batch key nothing reads is refused.

## 0.3.0 — 2026-08-04 — "a type on every refusal"

**29 entries.** A type on every refusal: every `ex-info` the engine throws carries a
`:type`, and the daemon's refusal keywords become plain. Both servers hold one
request-body ceiling, and the browser serializes its writes. An `ist` form must have
exactly three elements.

## 0.2.0 — 2026-08-03 — "the public API boundary is drawn"

**17 entries.** The public API boundary is drawn — six public namespaces, everything
else `vaelii.impl.*` and free to change. Every handle-taking function refuses a
non-handle. `close!` releases a durable KB's directory, an argument-constraint refusal
names its convicting declaration in content order, and the five sweeps start running in
CI.

## 0.1.0 — 2026-07-31 — "the first release"

The first public release.

## 2026-07-19 .. 2026-07-30 — the pre-release dailies

Twelve dated entries before versioning began, one per day of the initial build: the
whole stack on day one (2026-07-19), then order independence made an invariant, equality
and a sudoku solved, sound negation as failure, performance fixes and an operational
surface, denser storage measured first, OpenCyc in the engine's own format, reads scoped
to the asking context, aggregation over query results, the gate (lint, suite and
scaling), one entry point for backward chaining, and declarations that re-check what
they change (2026-07-30).

# Ontology defenses

- **Covers:** why a piece of the shipped ontology is shaped the way it is, and why the representation a reader would reach for instead is worse.
- **Not here:** the general rules every vocabulary change follows. Those are in [oe-principles.md](oe-principles.md), and an entry here cites a principle by its handle rather than restating it.
- **Assumes:** you have read the vocabulary the entry defends, in the KB file it names.

An entry names the alternative, says what the KB states instead, and gives the reason. A **Status** line says whether the form is on develop or ruled and not yet merged.

## Space, time and mass

### Mass and location are two axes, not one

**Alternative:** `intangible` means "has no mass", and everything without mass is one kind.

**Instead:** `thing` is partitioned three ways, each on its own axis: `(partition thing tangible intangible)` by mass, `(partition thing spatial aspatial)` by location in space, and `(partition thing temporal atemporal)` by location in time. `nowhere_never` names what is aspatial and atemporal.

**Why:** mass and location come apart. A region of space has a location and no mass. A line such as y=x is placed in a space and has no mass. A number has neither. With one axis, "massless" sweeps a region together with a number, and every rule about located things has to exclude the massless ones by hand. With three axes, each rule names the axis it is about, and the disjointness audit reads the pairs between axes as overlapping.

**Status:** on develop (CxCore).

### An event is temporal, and only some events are spatial

**Alternative:** `(genl event spatiotemporal)`: every event happens somewhere and somewhen.

**Instead:** `event` is temporal. A `spatial_event` spec holds the events that have a place. `(genl causal temporal)`: every cause is in time.

**Why:** some events have a time and no place. A contract expiring, a debt falling due and a term of office ending each happen at a time and nowhere in particular, and each can cause things. Requiring a place would either exclude them from `event` or force an invented location. The same reasoning stops `causal` at temporal: if a placeless event can cause, causation does not require a place.

**Status:** ruled; carried by #118, which waits on the engine fix for #150.

### `orthogonal` for axes that cut across each other

**Alternative:** relate cross-cutting types with `disjoint` or `separating`, or leave their relationship unstated.

**Instead:** `(orthogonal A B)` states that A and B overlap and neither subsumes the other, for example `made` and `biological`.

**Why:** the types on different axes are neither disjoint nor nested. A bred animal is made and biological. Left unstated, every such pair reads `:unknown` in the disjointness audit, which hides the pairs that are open questions among hundreds that are settled. Stating them disjoint would be false. `orthogonal` records the settled overlap, so the audit's unknowns are the real open questions.

**Status:** on develop (#104 declares `orthogonal`, #110 states the axes).

## Time and change

### No `rigid` term for users to learn

**Alternative:** a `rigid` type for predicates whose instances hold for as long as they exist, in the sense of the OntoClean literature.

**Instead:** predicates are partitioned by how they behave over time: `time_invariant_predicate`, `time_agnostic_predicate` and `time_varying_predicate`. The classes take the modal reading: a time-invariant predicate holds of its arguments at every time they exist, and a time-varying one fails for some arguments at some time they exist.

**Why:** the partition says the property in terms a reader already has, so nobody has to learn a term of art to use it. The modal reading beats the actual-time one because it licenses inference. Under the actual-time reading, a predicate that has never yet changed for any instance would count as time-invariant, and a single new fact would reclassify it. Under the modal reading, the class is a commitment about the predicate, and inheritance along `genl` can rely on it.

**Status:** ruled; not yet merged.

### No `possibly_time_varying_predicate`

**Alternative:** a class for predicates that may vary, mirroring `possibly_time_invariant_predicate`.

**Instead:** no such class.

**Why:** a predicate class is useful only if some property inherits through it. `possibly_time_invariant_predicate` carries time-invariance up `genl`, and `time_varying_predicate` carries variation down. A "possibly time-varying" predicate carries nothing in either direction: its genls may be invariant and its specs may be invariant. It would be a class nothing reads.

**Status:** ruled; not yet merged.

### `transitiveInArg` points the way Cyc's does

**Alternative:** keep vaelii's `transitiveInArg` and `transitiveInArgInverse` in the direction they first shipped with.

**Instead:** the two names are swapped so their direction matches Cyc's `transitiveViaArg`, and a test pins the direction each carries along `genl`.

**Why:** readers arrive from Cyc's documentation. A predicate whose name matches Cyc's and whose direction is opposite gets used backwards, and the result is a KB that derives the wrong memberships with no error. Apart from Cyc, the new direction is also the one most readers expect the name to mean. The swap is a breaking change, made while few KBs depend on the old direction.

**Status:** on develop (#131).

## Kinds and properties

### Abilities are event kinds, not a `capability` type

**Alternative:** a `capability` type whose instances are abilities (flying, swimming), related to their holders by `hasCapability`.

**Instead:** no `capability` type. The second argument of `hasCapability` and `capabilityType` is an event kind: flying and travelling are kinds of event.

**Why:** an ability is an ability to take part in a kind of event, and the event vocabulary already carries the structure abilities need. `(genl flying travelling)` makes "can fly implies can travel" fall out of the event hierarchy with no parallel ability hierarchy to keep in step, and travelling being a `causal_event` is stated once, for the events and the abilities together.

**Status:** on develop (#126).

### Biology properties have genls

**Alternative:** keep `alive`, `dead`, `mortal`, `asleep`, `awake`, `breathes_air` and `warm_blooded` free of genls, on the rule that a property is not a type.

**Instead:** each property takes the genl it is true of: `alive` and `dead` under `biological`, and the other five under `organism` or `animal`.

**Why:** only a living kind of thing can be alive, asleep or warm-blooded. Without a genl, nothing stops `(warm_blooded Rock1)`, and every pair of these properties with the kinds below `organism` reads `:unknown` in the audit. With the genl, a misapplied property is caught as a type clash. `alive` and `dead` go under `biological` rather than `organism`, so a dead leaf is not concluded to be an organism.

The objection behind the genl-free rule is that a property such as `alive` is not a kind: a thing can stop being alive and still exist, while it cannot stop being an organism. The time-invariance partition (see "No `rigid` term for users to learn") states that difference directly, as `(time_varying_predicate alive)`. With that difference stated on the predicate, the genl no longer blurs a property into a kind, and it can say what the property is true of.

**Status:** on develop (#127).

### Metal is solid by default, and mercury is the stated exception

**Alternative:** state that every metal is solid, or leave metal's state of matter unstated.

**Instead:** metal is a `solid` by default, and mercury is the stated exception.

**Why:** a monotonic "every metal is solid" is false, because mercury is liquid at room temperature. Leaving the state unstated gives up a conclusion that is right for almost every metal anyone will mention. A default states the common case, and the exception keeps the one known counterexample from contradicting it. The choice between a default and a list of the known solid metals turns on new cases: a newly discovered metal, a hypothesized one, or one in a fictional or counterfactual context should come out solid unless something says otherwise. A list would conclude nothing about any of them, so the default is the right form (**default or enumerate** in the principles).

**Status:** ruled; not yet merged.

## Logic

### `empty` and `nonempty` partition `unary_predicate`

**Alternative:** leave it implicit that a type below two disjoint types has no members.

**Instead:** `(partition unary_predicate empty nonempty)`, carried down and up `genl`. A type below two disjoint types is concluded `empty`, and the disjointness audit does not treat a shared subtype as evidence of overlap unless the subtype is known to be `nonempty`.

**Why:** `(disjoint c c)` holds exactly when c is empty, so an empty type is disjoint from everything, itself included. Left implicit, an empty shared subtype would be counted as an overlap witness and the audit would report two disjoint types as overlapping. Naming emptiness makes that case explicit, so the audit can ask for a witness that something is actually there.

**Status:** on develop (#119).

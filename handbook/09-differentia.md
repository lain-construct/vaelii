# 9. The differentia

- **Covers:** finding the property that separates a type's members from everything else
  under its parent; the refinement audit a proposed classifier passes; why a type is
  defined by what its members are and not by what they are for; and why discreteness makes
  a poor differentia.
- **Not here:** placing the type once its differentia is known → [ch. 10](10-parent.md);
  what ends a member of a kind → [ch. 12](12-identity.md); writing the differentia as a
  definition the engine applies → [ch. 31](31-definitions.md).
- **Assumes:** [ch. 1](01-true-and-useful.md), [ch. 7](07-comments.md),
  [ch. 8](08-kind-of-term.md).

A type is its parent plus a differentia: the property every member has and no other
member of the parent has. The comment states the differentia, the examples test it, and
where vaelii can express it the differentia is a rule. The three principles below find the
differentia, keep purpose out of it, and keep it stable under parts and slices.

## differentia from near-misses

*Find a type's differentia from its complement*

**genlPrinciple:** no OE calligraphy

**Practice.** List the members of the proposed type. Then list the near-misses: things
under the same parent that are not members. A property is the differentia only if every
member has it and no near-miss does. If no property survives, the type has no differentia
and the KB gains nothing by reifying it. The near-misses are often members of other kinds,
and each such kind is a type the new one needs a stated relation to.

**Example.** `formation` sits under `natural`. Its members are a rock, a crystal, a river, a
star and a dune. Its near-misses under `natural` are a wild sheep and a coral reef, which
are natural and grown. The surviving differentia is that the form came from physical
processes, neither grown nor made. The near-misses also name a kind the type must be
related to: they are `biological`, a type under `tangible` that crosses the origin division
(abstract.txt's note says an engineered bacterium is made and biological), and the KB
separates `formation` from it (abstract.txt):

```clojure
(comment formation "A natural tangible whose form came from physical processes, neither grown nor made.")
(genl formation natural)
(separating tangible formation biological)
```

`made`'s differentia, "a tangible shaped by an agent's action, or by something made", is
stated as two rules, one per half of the definition (abstract.txt, with the notes above
each rule):

```clojure
(set/forwardRule (implies (and (tangibleOutput ?e ?x) (performedBy ?e ?d)) (made ?x)))
(set/forwardRule (implies (and (tangibleOutput ?e ?x) (doneBy ?e ?d) (made ?d)) (made ?x)))
```

The notes record the cases each rule decides. Growth is never intentionally initiated, so
a calf is not made by its mother. A widget a factory machine pressed is made, though no
agent's action shaped it directly, and the second rule covers that case.

**Why.**

- **Logic.** A differentia is a condition relative to the parent. The near-misses share
  every property of the parent, so they are the cases that can falsify a candidate
  condition. Familiar members cannot, because a wrong condition usually holds of them too.
- **Engine.** A differentia stated as rules makes membership a conclusion: an output of an
  intentionally initiated event is concluded `made`, justified by the two facts it rests
  on. A near-miss named as a sibling becomes a separation, so a term stated both a
  `formation` and `biological` is placed as a nogood instead of stored as two compatible
  memberships.
- **Maintenance.** A type without a stated differentia gathers members by association, and
  each new case reopens the question of what the type means. A differentia with its
  near-misses settles new cases the same way for every reviewer.

**Why not the other ways.** Defining a type by a list of familiar members tests nothing,
because a list does not say what the next member must have. Defining it by a feature the
members happen to share, such as a typical size or a common use, admits near-misses that
share the feature and excludes members that lack it.

**Audit.** The change lists each new type's members and near-misses and states the
differentia that separates them, and records them as `positiveExampleComment` and
`negativeExampleComment` lines. Each near-miss that is a kind gets a stated separation or a
stated `orthogonal`.

### The refinement audit

Run these six steps before accepting a proposed classifier.

1. **State what membership means under the parent**, and not only a list of familiar
   members. Where a word has episodic, habitual or modal uses, fix the intended reading and
   the context. `hollow` fixes the episodic reading in its first words: "Has, at that time,
   an interior space".
2. **Give positive controls and close non-members under that parent**, with the reason each
   belongs or does not. Challenge the proposed differentia with cases that share its
   arity, its argument types or its variation over time, since those features need not
   capture its meaning.
3. **Separate essential meaning from accidental association.** A relation may be
   asserted, learned or changed in a happening without describing a happening itself. For
   a proposed happening classifier, contrast an occurrence with a held state, as core.txt's
   partition of `uninterrupted_situation` into `static_situation` ("a held state") and
   `event` ("whose state changes") does, and not merely a changing truth value with a fixed
   one.
4. **Ask what each classification lets the KB conclude or rule out** (**does it have
   rules?**, [ch. 1](01-true-and-useful.md)). Examples test a proposed definition, and a
   finite list does not establish that it is necessary or sufficient. Revise the
   definition when a real counterexample defeats it.
5. **State the defining facts or rules where possible** (**represent the definition**,
   [ch. 2](02-representation.md)). For two encodings, make their argument and role mapping
   and their context or temporal correspondence explicit. Do not substitute an unrelated
   existential witness, and do not assume a unique occurrence from the same participants.
6. **Distinguish the semantic criterion from what the engine can check** (**truth, not
   provability**, [ch. 3](03-truth-not-provability.md)). Record which expected conclusions
   derive, which exclusions have explicit support, and which cases remain open. A failure
   to derive membership does not prove that a negative control is a non-member: the engine
   reads open-world, and `ask` answers unknown, not false, for a membership nothing
   establishes.

## no teleology

*No teleology in a type's definition*

**Practice.** A type says what a thing is, not what it is for. A type defined by purpose,
by capacity for a role or by a designer's intent sweeps in every idle instance and every
thing that is put to the use once. When a comment defines membership by purpose or role,
make the purpose a relation, put the role's rules on the relation, and type the relation's
arguments by what the fillers are.

The verb test reads the verb that defines membership. A process or agency verb (operates,
is used, serves, does work) brings purpose in. A stative verb (contains, has as a part, is
made of) defines by structure, and a type defined by structure is rigid: a member stays a
member while it exists.

**Example.** abstract.txt defines its mechanism kinds by construction and says so in each
comment:

```clojure
(comment machine "A mechanism with parts that move relative to each other, driven by an energy source. Defined by its parts, not its use, so a stopped clock is still one.")
(positiveExampleComment machine "a stopped clock")
(positiveExampleComment electronic_device "a dead phone")
(comment output
         "(output ?happening ?thing) means that ?happening gave ?thing the form or content it has, as something it left behind. Whether that was the point of the happening does not matter.")
```

The defining verbs are stative: a machine has parts that move, and an electronic device is
built around a circuit. A stopped clock and a dead phone are members. A candidate `device`
defined as "operates when powered" fails the verb test: it admits a brick warming in
sunlight and a one-piece whistle. A candidate `tool` defined as "used to perform work"
admits a rock used once as a hammer.

**Why.**

- **Logic.** A purpose is a relation between a thing, a use and usually an agent. A type is
  one-place, so a purpose-defined type hides the second and third arguments and makes
  membership depend on intentions that are not facts about the thing. Most pacemakers are
  nobody's body part: they are in a warehouse or in a landfill.
- **Engine.** A membership is checked without time, as core.txt's comment on
  `diachronicallyDisjoint` states, so a membership that holds only while a thing is in use
  is stored as if it always held. A structural type keeps its members while they exist, so
  a separation over it is true: `(disjoint mechanism organism)` holds because a mechanism
  is defined by how it is built. A purpose type admits members of every kind, so a rock
  used as a hammer is a `formation` and a tool at once, and any separation involving the
  purpose type is false somewhere. The role as a relation carries the use, with argument
  types derived from what each filler is.
- **Maintenance.** The members of a purpose type change whenever uses change, and none of
  those changes is recorded in the KB. A structural type changes members only when things
  are made or destroyed.

**Why not the other ways.** A type defined by "can serve as" admits everything that could
be pressed into the role, and **does it have rules?** finds that nothing is true of the
members except the role. A type defined by designer intent excludes a found object used the
same way and includes a failed design that never worked. A type that is purpose in
disguise, such as one meaning "necessarily part of something", fails the same way.

**Audit.** For each new type, read the verb its comment defines membership with. If it is a
process or agency verb, restate the type by structure or make the purpose a relation. The
comment of a structural type names an idle member as a positive example, as `machine`
names a stopped clock.

## beware entity

*Beware "entity" (a discrete, countable object)*

**Practice.** Do not make discreteness or countability a type's differentia. Temporal and
spatial slices of a thing ("Einstein while at the patent office", "Einstein minus his left
pinky toe") behave almost exactly like the thing. Pick a differentia that slices and parts
inherit (made, grown, alive, has mass), or say explicitly in the comment how slices and
parts are treated.

**Example.** core.txt's `tangible` and abstract.txt's `made` define membership by
properties a part or a slice shares with the whole:

```clojure
(comment tangible "Something with mass. Having mass, it necessarily has a location in space and time too, so it is spatiotemporal.")
(comment made "A tangible shaped by an agent's action, or by something made. Contrast natural.")
```

A slice of a made thing was shaped by the same action, and a part of a thing with mass has
mass. A differentia written as "discrete objects whose form came from being made" would
exclude the slice. `made`'s differentia, found with **differentia from near-misses**, holds
of the slice as of the whole.

**Why.**

- **Logic.** Whether a portion counts as one discrete object depends on how it is cut, so
  discreteness is not a property the thing carries. A differentia that parts and slices
  inherit makes membership independent of the cut.
- **Engine.** The KB relates a part to its whole with `tangiblePartOf`, `subSituationOf`
  and `partOf`. `tangiblePartOf` declares `tangible` at both positions, so under the
  entailing reading `(tangiblePartOf LeftWing Pingu)` derives `(tangible LeftWing)`, and a
  part's memberships follow from the parthood fact. A differentia that the part shares
  keeps those derived memberships consistent with the type's definition. A discreteness
  differentia would make the derived part a member of `tangible` and leave its membership
  in the discrete type undecided, with no rule to settle it.
- **Maintenance.** Each new slice or part reopens the membership question for a
  discreteness type, and reviewers answer it case by case.

**Why not the other ways.** A type named `entity` looks like a natural kind and draws
members of every kind, since nearly anything can be counted one way or another, so no
separation or rule over it is true across its members.

**Audit.** For each new type, ask whether a part of a member, and a temporal slice of a
member, are members. If the differentia says no, the comment says how they are treated.

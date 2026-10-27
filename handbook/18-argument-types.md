# 18. Argument types

- **Covers:** `arg` and `genlArg`; the forms that type several positions or relate two
  (`args`, `argAndRest`, `argArg`, `interArg`, `interArgEqual`, `interArgs`, `quotedArg`);
  how tight an argument type should be when the KB reads every declaration as an
  entailment; declaring each position on the relation itself, and the six unary marks
  that declare none.
- **Not here:** the relation's own place in the hierarchy and the widening a `genl` causes →
  [ch. 17](17-predicate-hierarchy.md); the type of an application's value (`result`) →
  [ch. 22](22-functions.md).
- **Assumes:** [ch. 8](08-kind-of-term.md), [ch. 13](13-disjointness.md) (**classify
  before you constrain**), [ch. 17](17-predicate-hierarchy.md).

An argument declaration states what kind of term fills one position of a relation. By
default vaelii reads the declaration two ways at once: as a constraint, which convicts an
argument the taxonomy separates from the declared type, and as an entailment, which
derives the declared type of every symbol asserted in the position. The second reading is
what makes the choice of type matter beyond error checking.

## arg and genlArg

**Practice.** Use `(arg P n T)` when position `n` holds a member of `T`, and `(genlArg P n
T)` when it holds a subtype of `T`. An instance-level relation takes `arg`; a relation
between kinds takes `genlArg`.

**Example.** `abstract.txt` types the instance relation between two physical objects and
the type relation between two kinds of physical object:

```clojure
(arg tangiblePartOf 1 tangible)
(genlArg partType 1 tangible)
(genlArg partType 2 tangible)
```

The `comment` on `genlArg` in `core.txt` gives the contrast: "(genlArg partType 1
tangible) says the argument names a kind of physical object, where (arg tangiblePartOf 1
tangible) says it names one."

**Why.**

- *Logical.* `arg` says each filler is an instance of `T`; `genlArg` says each filler is a
  subtype of `T`. `penguin` satisfies `(genlArg partType 1 tangible)` and fails `(arg
  tangiblePartOf 1 tangible)`, which is the distinction between a claim about a kind and a
  claim about a thing.
- *Engine.* Under the entailing reading, `arg` derives `(T x)` and `genlArg` derives
  `(genl x T)`. An individual in a `genlArg` position is convicted, since an individual
  can never acquire `genl` edges.
- *Engine.* A declaration on a predicate binds the tuples of every predicate below it.
  `(genl fatherOf parentOf)` makes each `fatherOf` tuple a `parentOf` tuple, so `parentOf`'s
  declarations judge it.

**Why not the other ways.** An `arg` on a position that holds kinds derives a membership
for each kind, placing a type as an instance of the declared type. A `genlArg` on a
position that holds things convicts every individual written there.

**Audit.** For each declaration, name one filler and say whether it is a thing or a kind;
the answer picks `arg` or `genlArg`.

## As tight as the truth allows

**Practice.** Type each position with the narrowest type that every possible filler is a
member of. When no type below `thing` covers every filler, declare `thing`, and put the
reason on the line.

**Example.** `abstract.txt` declares `thing` on the doer of an event, and says why:

```clojure
(arg doneBy 1 happening)
(arg doneBy 2 thing)   ;; an event's doer: a person, an animal, a machine or a process
```

`CxSocial.txt` types `dwellsIn` narrowly because only a human dwells in a dwelling:

```clojure
(arg dwellsIn 1 human)
(arg dwellsIn 2 dwelling)
```

**Why.**

- *Logical.* `(arg P n T)` entails `(T x)` for every `x` in position `n` (**strongest form**:
  if only one kind of thing can fill a position, the declaration names that kind).
- *Engine.* With the entailing reading on, which is the default, `(dwellsIn Ann Flat3)`
  derives `(human Ann)` and `(dwelling Flat3)`; a mint is not stored while a believed
  membership already says the same thing more specifically. Each derived membership is a sentex
  justified by the fact and the declaration, plus the `genl` and `genlCx` edges the
  declaration descends through, and retracting the fact or the declaration withdraws it.
  The derived membership is ordinary content: rules fire on it and the separation check
  reads it.
- *Engine.* When the filler holds a type the taxonomy separates from the declared one, the
  derivation is a clash. `assert` stores the fact and the settle places the nogood;
  `try-assert` refuses the fact with `:definitional-clash`. A value is convicted outright,
  since its type is in its syntax: `5` is not a `string`.
- *Engine.* A declaration of `thing` mints nothing: a membership in `thing` says nothing
  about a term. `kb-quality` lists each such declaration under `:declarations
  :typed-thing` with the predicate's stored extent, the facts a narrower type would type.
- *Maintenance.* A type narrower than the truth mints a false membership on every filler
  outside it. `oe-defenses.md` makes the case for `doneBy`: a narrower type would conclude
  every doer a member of it, a machine included, and no type below `thing` covers every
  doer. `performedBy`, the intentional case, carries the narrower claim.
- *Maintenance.* The happening-participant relations declare their bounds on each
  predicate even where a parent states the same one, as every relation does
  ([below](#each-position-declared-on-the-relation)).

**Why not the other ways.** A type broader than the truth gives up the derived membership
and the clash check for every filler. A type narrower than the truth is worse under the
entailing reading than under a constraint-only reading, because it does not refuse the
outlier; it files the outlier under the wrong kind.

**Audit.** For each position, name the most unusual filler the relation admits and check
it is a member of the declared type. Read `kb-quality`'s `:typed-thing` list and, for
each entry, either name a filler that no narrower type covers or narrow the type.

## Each position declared on the relation

**Practice.** Declare `arg`, `genlArg` or `quotedArg` for each position of a relation on
the relation itself, even when a `genl` parent's declaration already gives the type. A
unary predicate whose parent carries an `arg` naming a type below `thing` restates it. Six
unary marks are the exception and declare no position: `instance_relation_predicate`,
`type_relation_predicate`, `equivalence_relation`, `injection`, `surjection` and
`bijection`.

**Example.** `abstract.txt` declares both positions of `performedBy`, though `doneBy`
above it declares the same two:

```clojure
(arg performedBy 1 happening)
(arg performedBy 2 thing)   ;; an event's doer: a person, an animal, a machine or a process
(genl performedBy doneBy)
```

`core.txt` states `(arg fixed_arity 1 relation)`, though the edge that
`(partition relation fixed_arity variable_arity)` installs names the same type. The
declaration is also the only check that refuses a value: the edge concludes `(relation 5)` from
`(fixed_arity 5)`, and nothing is disjoint from `relation` for a number, so without the
declaration `(fixed_arity 5)` would be accepted.

**Why.**

- *Logical.* A declaration on a parent binds the tuples of every predicate below it, so the
  child's own declaration adds no tuple the parent's does not judge. The two state one
  constraint from two places.
- *Maintenance.* A position declared on the relation states its type where a reader of the
  relation looks. A revision of the parent, such as a narrowed type or a removed `genl`
  edge, then cannot change the child's declared constraint.
- *Engine.* `kb-integrity`'s `:missing-arg` reads a position's declarations on the
  predicate and on every predicate above it, so it does not report a position only the
  parent declares. The check for this practice is the grep in the audit.
- *Engine.* The six marks are the exception because each one's own `genl` parent supplies
  the type a declaration would name. `instance_relation_predicate` sits under
  `binary_predicate`, which is below `predicate`. Under the constraint-only reading,
  `(arg instance_relation_predicate 1 predicate)` would turn the edge's conclusion into a
  precondition: it would refuse `(instance_relation_predicate P)` stated after
  `(arity P 2)`, because `P` is not yet a `predicate`, when the sentence itself supplies
  that classification ([argtypes.md](../docs/argtypes.md)).

**Why not the other ways.** A position left to the parent's declaration carries no type on
the relation, so a reader follows the hierarchy to find it, and a revision of the parent
moves it. A declaration on one of the six marks refuses the classification its own
sentence states. **State it once** ([ch. 4](04-economy.md#state-it-once)) does not drop an
`arg` for being derivable from a parent.

**Audit.** Run `kb-integrity` with `:categories #{:missing-arg}` over the change, which
reports a position no declaration types. For each relation with a `genl` parent,
`git grep -nE '^\((arg|genlArg|quotedArg) <relation> '` over `resources/kb` and confirm one
line per position. Review each declaration on one of the six marks, and remove it.

## Positions related to each other

**Practice.** When the type of one position depends on another position, use the form
that states the dependency instead of a broad type on each position.

**Example.** The shipped files use each form:

```clojure
(interArg typeGenl 1 meta_metatype 2 metatype)
(interArgEqual closedExtentForArg 2 3 1 at_least_ternary)
(argArg PredAllExistsFn 4 2)
(argAndRest orthogonalMetatypes 1 at_least_metatype)
(quotedArg relationshipLabel 3 string)
```

`interArg` says that when argument 1 of `typeGenl` is a `meta_metatype`, argument 2 is a
`metatype`. `interArgEqual` conditions on a value: when argument 2 of `closedExtentForArg`
is `3`, argument 1 is `at_least_ternary`. `argArg` reads the type off another argument of
each sentence. `argAndRest` types position 1 and every later one. `quotedArg` types the
term as written rather than what it denotes, so `relationshipLabel`'s label is a string.

**Why.**

- *Engine.* `argArg`, `interArgEqual` and `resultArg` are read as an `arg` row for the
  sentence in hand, so their conviction, their entailment and the derived membership's
  justification are `arg`'s own. `interArgEqual` compares a value of one of five kinds
  (number, string, keyword, boolean, character) by `=`; `wff` refuses a symbol there,
  because a merge could change a symbol and the derivation would then depend on arrival
  order.
- *Engine.* `args` and `argAndRest` type a variable-arity tail, which has no largest
  position for an `arg` to name. A position-specific `arg` and a covering form both bind
  the position, and an argument there is held to both.
- *Maintenance.* A dependent type states the real constraint once. A broad type on each
  position states a weaker one and loses the derived membership.

**Why not the other ways.** A rule that concludes the dependent type from the sentence
derives what `argArg` derives and convicts nothing: a value or an application in the
position passes, where the declaration convicts it.

**Audit.** Run `kb-integrity` with `:categories #{:missing-arg}` over the change. Each
finding is `{:predicate P :arity n :missing [k …]}`, naming the positions no declaration
types; `interArg` and `argArg` do not count as typing a position there. Read `kb-quality`'s `:declarations :stranded` list, which names each declaration
for a position its predicate's arity does not have.

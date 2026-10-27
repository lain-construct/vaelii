# 34. Generators

- **Covers:** a rule whose consequent is a rule; the holes a firing fills and the
  variables the generated rule keeps; the direction wrapper of the generated rule; nesting
  a level to fill a functor; and the exceptions and cycles a generator is refused for.
- **Not here:** the `predAll` family two of whose cells are generators →
  [ch. 21](21-claims-about-kinds.md), [ch. 33](33-existentials.md); a head existential
  inside a generated rule → [ch. 33](33-existentials.md); direction and placement of an
  ordinary rule → [ch. 29](29-rules.md).
- **Assumes:** [ch. 29](29-rules.md), [ch. 30](30-exceptions.md).

A generator is a rule whose consequent is a rule. Each firing stores one ordinary rule,
with the variables the generator's antecedents bound filled in. The stored rule is keyed,
triggered and proved through the paths a hand-written rule takes.

## One generator, not a rule per pair

**Practice.** When a family of rules differs only in predicates, types or fillers that
facts in the KB name, write one generator over those facts instead of one rule per
member of the family.

**Example.** `core.txt` defines `predAllInstance` by a generator:

```clojure
(implies (predAllInstance ?pred ?indep ?fixed)
         (set/defaultRule (set/forwardRule (implies (?indep ?x) (?pred ?x ?fixed)))))
```

Each `predAllInstance` fact fills `?pred`, `?indep` and `?fixed`, and the firing stores a
default forward rule with concrete functors, concluding `(?pred x ?fixed)` for every
member `x` of `?indep`.

**Why.**

- Logical: the generator states the family once, as a claim about the facts that select
  its members, and each generated rule is an instance of that claim.
- Engine: the minted rule is justified by the firing, the antecedent handles plus the
  generator's own handle, and is not a premise. Both chainers ask belief of a rule before
  using it, so retracting the fact that filled it un-believes the mint and every
  conclusion resting on it. A `:default` fill caps the mint's class, and a defeat of the
  fill hides the mint and its conclusions. Two generators that generate the same rule
  share one handle and add a justification each.
- Order independence: a newly stored generator joins over the facts already stored, and
  a newly minted rule is returned to the agenda the same way, so facts and generators
  arrive in either order with the same rules.
- Maintenance: only fills that occur become rules, and the family grows and shrinks with
  the facts. A hand-written family over `predicates × types` has a rule for every pair,
  occurring or not.

**Why not the other ways.** A rule with a variable in functor position of an antecedent
is refused `:not-indexable`: the antecedent index keys on a concrete symbol, and a
variable names none for an arriving fact to trigger. A family written out by hand keeps
its rules after the fact that justified one is retracted.

**Audit.** For each family of three or more rules in a change that differ only in
constants, check whether a fact the KB states selects the members, and write the
generator over that fact.

## Holes and the generated rule's own variables

**Practice.** Name a variable in the generated rule with a variable the generator's
antecedents mention when the firing should fill it in. Give every other variable a name
no enclosing level mentions.

**Why.**

- Engine: nothing in the spelling marks the two kinds apart; the split is computed. A
  variable an enclosing level's antecedents also mention is a hole, ground in what the
  firing generates. Every other variable belongs to the generated rule and survives as a
  variable. A hole may stand in functor position, because by mint time it holds a
  concrete predicate.
- Engine: range restriction is checked one level in, on the generated rule, with the
  holes counted as bound. A generated rule with a consequent variable that neither a hole
  nor its own antecedents bind is refused at the generator's assert, before any firing.
  A level that fills no hole the levels above it had not filled is refused
  `:not-range-restricted`, because it would generate the same rule at every firing.
- Engine: every mint runs the check list the assert entry point runs, with the holes
  substituted in. A mint that cannot stand is dropped and recorded in `violations`, naming
  the generator that produced it, never thrown: an exception escaping a firing would make
  the belief set depend on which rule fired first.

**Why not the other ways.** A variable reused by accident between levels becomes a hole
and is filled where the author meant a variable of the generated rule, so the generated
rule matches one value instead of all.

**Audit.** After a load, read `violations` for a dropped mint, and fix the generator or
the fill it names.

## The generated rule's direction

**Practice.** Write the direction wrapper of the generated rule inside the consequent.
Leave the generator itself bare; `set/inertRule` on the generator states a generator that
never fires.

**Example.** `core.txt` maps an arity to a relation-wide class with two generators over
one fact. The first generates a forward-only rule:

```clojure
(implies (relationTypeByArity ?type ?arity)
         (set/forwardOnlyRule (implies (arity ?relation ?arity) (?type ?relation))))
```

The second generates the converse as a backward rule, so a query for `(arity R n)` of a
class member is proved from the membership and nothing is stored:

```clojure
(implies (relationTypeByArity ?type ?arity)
         (set/backwardRule (implies (?type ?relation) (arity ?relation ?arity))))
```

**Why.**

- Engine: a generated rule with no wrapper is backward, as any bare rule is, so a
  generator whose rule is meant to store facts writes `set/forwardRule` or
  `set/forwardOnlyRule` inside the consequent. `set/defaultRule` rides there too and
  makes the generated rule defeasible.
- Engine: the generator defaults to forward even when bare. Its consequent predicate is
  `implies`, which no goal asks for, so a backward generator would fire in neither
  engine, and `set/backwardRule` on a generating level is refused `:not-indexable`.
- In the example, `set/forwardRule` on the first generated rule would give it a backward
  half, and that half and the backward converse would form a backward cycle between
  `arity` and the class. `set/forwardOnlyRule` keeps the first rule out of backward
  proofs.

**Why not the other ways.** A wrapper outside the generator sets the generator's own
direction and leaves the generated rule bare, so a rule meant to store facts stores none.

**Audit.** For each generated rule, name the engine that should run it and check that
the wrapper inside the consequent says so.

## Nesting to fill a functor

**Practice.** When a generated rule needs a functor that a literal beside it binds, move
that literal one level out, so the functor becomes a hole of the level that encloses the
rule using it.

**Example.** A composed generator over temporary predicates. The middle level binds
`?type`, and the innermost rule uses it as a functor:

```clojure composed
(implies (tmpBridge ?ipred ?tpred)
         (implies (?tpred ?type ?val)
                  (implies (?type ?instance) (?ipred ?instance ?val))))
```

**Why.** A hole is ground before the rule holding it is stored. A variable bound by a
literal beside it is not, because both literals are stored in one rule. With the two
literals in one antecedent, the stored rule has a variable functor and is refused
`:not-indexable`. With the literal one level out, every level that reaches the index has
concrete functors at its antecedents, and the generators above it are filed under
`implies`. Nesting is not capped: a variable belongs to the outermost level whose
antecedents mention it, and every level owes the checks a generator owes.

**Why not the other ways.** One rule per value of `?type` restates the family the middle
level generates.

**Audit.** Each level of a nested generator fills at least one hole that no level above
it fills.

## Exceptions and cycles

**Practice.** Put an exception to a generated rule inside the generated rule as an
`unknown` antecedent, or on the outermost generator as an `exceptWhen` that states when
the generator does not fire. Keep the generators of a KB acyclic.

**Why.**

- Engine: an `exceptWhen` is a separate meta-sentex keyed by the rule's handle, stored
  by the assert path, which a firing does not run. An `exceptWhen` on a generated level
  would mint a rule whose exception had been lost, so the generator is refused
  `:not-well-formed`. An `unknown` antecedent lives in the rule sentence and survives
  substitution.
- Engine: a generator cycle, in which a generator's innermost conclusion is a predicate
  some generator reads in an antecedent it generates from, is refused `:not-stratified`.
  The check runs in both directions at every generator's assert, so the cycle is refused
  in either arrival order. A nested generator generates one level further and stops; a
  cycle would generate without end, so the refusal is on the cycle and not on depth.

**Why not the other ways.** A depth cap on a generator cycle would make the rules stored
depend on the cap, and on which generator fired first.

**Audit.** `assert` refuses both cases, so a generator that loads clean meets them. For
each exception the author meant for a generated rule, find it inside the rule or on the
outermost level.

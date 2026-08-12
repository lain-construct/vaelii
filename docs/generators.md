# Rule generators: a rule whose consequent is a rule

- **Covers:** the generator form, the hole/own-variable scoping rule, what a firing
  mints, how a mint is retracted, and the four things a generator is refused for.
- **Not here:** the direction wrappers a stamped rule carries →
  [inference.md](inference.md); why a *variable-predicate* rule is refused →
  [indexing.md](indexing.md); skolemizing a head existential →
  [skolem.md](skolem.md).
- **Assumes:** sentex, rule, handle, justification, hole-free range restriction →
  [glossary.md](glossary.md), [inference.md](inference.md).

A rule normally concludes a fact. A **generator** concludes a *rule*, and its firing
stores that rule:

```clojure
(implies (and (planVerb ?outcome) (outcomeEmotion ?outcome ?emotion))
         (set/defaultRule
           (implies (and (planOf ?a ?p) (?outcome ?a ?p))
                    (feels ?a ?emotion))))
```

Given `(planVerb succeededAt)` and `(outcomeEmotion succeededAt Joy)`, the firing
stores one ordinary rule:

```clojure
(set/defaultRule (implies (and (planOf ?a ?p) (succeededAt ?a ?p)) (feels ?a Joy)))
```

Concrete functors, keyed by the rule index, triggered and proved through exactly the
paths a hand-written rule is. Add `(outcomeEmotion failedAt Regret)` and a second rule
appears; retract it and that rule goes.

## The scoping rule

Two kinds of variable live in a generator's consequent, and **nothing in the spelling
marks them apart** — the split is computed:

| | which variables | what happens to them |
|---|---|---|
| **holes** | those the generator's own antecedents also mention | bound by the join, ground in the mint |
| **the stamped rule's own** | everything else | survive as variables; they belong to the rule being stamped |

In the example `?outcome` and `?emotion` are holes; `?a` and `?p` are the stamped
rule's own. Sharing a variable name with the antecedents *is* how an author says "fill
this in", so there is nothing to declare and no second spelling that could disagree
with the first.

Two consequences worth stating, because both are easy to trip over:

- **A hole may stand in functor position.** `(?outcome ?a ?p)` is legal here and
  nowhere else, because by mint time it holds `succeededAt`. This is what lets one
  generator range over a family of predicates while every rule the index ever keys on
  has a concrete functor. A variable functor that is *not* a hole is refused
  (`:not-indexable`) — nothing will ever bind it.
- **Range restriction moves one level in.** The generator's own is vacuous: its
  consequent is a rule rather than a conclusion, and the stamped rule's free variables
  are unbound on purpose. What is checked is the *stamped* rule's, with the holes
  counted as bound. So `(implies (marker ?p) (implies (?p ?x) (dst ?x ?loose)))` is
  refused for `?loose`, at the generator, before any firing.

## The stamped rule's direction

The wrapper rides **inside** the consequent, where substitution never touches it, and
sets the direction of the rule that gets stored: `set/forwardRule`,
`set/backwardRule`, `set/inertRule`, `set/defaultRule`. That is the only place a
direction can be written for a rule nobody types out.

The **generator itself is forward-only**. Its conclusion is a rule, and no backward
goal asks for one — `res/concluding-rule-handles` reads a goal's predicate, and a
generator's consequent predicate is `implies`, which nothing queries. A
`set/backwardRule` generator is refused rather than stored claiming a capability it
cannot exercise. `set/inertRule` stays legal, since it claims nothing.

## A mint is derived content

This is what separates a generator from a load-time macro, and it is the reason to
have one.

A minted rule is **justified** by the firing — antecedent handles plus the generator's
own handle — not marked a premise. Both chainers ask belief of a rule before using it
(`res/rule-believed?`), so when what licensed a mint goes, the ordinary relabel
un-believes the mint, and the mint stops firing. Nothing has to hunt it down:

```clojure
(v/retract! kb pairing-handle)   ; (outcomeEmotion succeededAt Joy)
;; the stamped rule is no longer believed, and neither is anything it concluded
```

Dedup is the ordinary sentex dedup, so two generators that stamp the same rule share
one handle and collect a justification each — and the rule survives until the last of
them goes.

Both **arrival orders** agree, with no retroactive sweep of a generator's own. A
generator is a rule, and a newly asserted rule is a datum that joins over the facts
already stored (`chain/process-datum`); a newly *minted* rule is returned to the agenda
the same way, so it too sees what is already there.

## What a firing does

The mint goes through the same check list the assert door runs
(`checks/check-rule!`, read by both doors so neither can drift): range restriction,
indexability, naming, stratification, no imperative. A stamped rule concluding a
conjunction is polycanonicalized into one rule per conjunct, exactly as an asserted one
is.

A mint that **cannot stand is dropped and recorded**, never thrown — a fixpoint may not
abort halfway through itself, and an exception escaping a firing would make the belief
set depend on which rule fired first. The drop lands in the violation ledger
(`core/violations`) naming the generator that produced it.

## What is refused

| written | refused as |
|---|---|
| a rule generating a generator (three levels) | `:not-well-formed` |
| an `exceptWhen` on the stamped rule | `:not-well-formed` |
| `set/backwardRule` on the generator | `:not-indexable` |
| a stamped variable functor that is not a hole | `:not-indexable` |
| a generator sharing no variable with the rule it stamps | `:not-range-restricted` |
| a stamped rule that is not range-restricted | `:not-range-restricted` |
| a generator cycle | `:not-stratified` |

**An `exceptWhen` on the stamped rule** is refused because an exception is not a rule
field: it is a separate meta-sentex keyed by the rule's handle, split off and stored by
the assert path, which a firing does not run. The mint would be a rule whose guard had
evaporated in silence, firing on exactly the bindings its author wrote it not to — so
it is refused rather than dropped. Two things do work: an `(unknown …)` antecedent
*inside* the stamped rule, which lives in the rule sentence and so survives
substitution; and an `exceptWhen` on the **generator**, which says when not to stamp.

A head existential *inside* the stamped rule is fine, and skolemizes one firing later,
against the stamped rule's own handle — the generator's firing deliberately does not
skolemize, since the stamped rule's free variables are its own ([skolem.md](skolem.md)).

**One level of nesting**, and the third is refused rather than recursed into. The
scoping rule that makes a generator readable is that the stamped rule's free variables
are its own; a rule stamping a generator would need two such splits in one sentence
with nothing in the spelling to say which variable belongs to which.

**A generator cycle** is a generator whose stamped rule concludes a predicate some
generator reads in an antecedent — itself included. That is a rule set minting rules
that mint rules, and unlike ordinary recursion nothing bounds it: each round adds
*rules*, and the next round's rules are the ones the last round wrote. Refused outright
rather than depth-capped, because a cap would make the KB's contents a function of how
long the chainer happened to run, and "how many rules does this KB have" would stop
having an answer. It is the call [exceptions.md](exceptions.md) makes for a cycle
through negation, for the same reason. The check runs in both directions at every
generator's assert — the arriving one may stamp what a stored one reads, or read what a
stored one stamps — because checking only one would admit the cycle whenever the two
were asserted in the other order.

## What this is not

**Not storage compaction.** Materializing N rules stores N rule records. What it buys
instead is that only the fills that actually *occur* become rules: a hand-authored
cross-product is `predicates × types`, while a generator mints one rule per instance
fact that exists, and the family grows and shrinks with the data. Matching cost is
unchanged either way — the rule index is keyed by predicate, so N concrete rules are
never scanned, and each is reachable only through its own functors.

**Not a variable-predicate rule.** A rule with a variable functor is still refused
(`:not-indexable`, [indexing.md](indexing.md)): the index has two cells and both are
keyed on a concrete symbol. A generator is how that refusal's advice — *assert the
instantiated rules, one per predicate it ranges over* — stops being manual labour,
without the index having to learn to read a variable.

**Not a rule about rules.** A generator concludes a rule; nothing reads one as a term,
and no rule can take a rule as an antecedent. The one way to speak *about* a stored
rule remains the `(sentexHandle H)` meta-sentex layer
([exceptions.md](exceptions.md), [contexts.md](contexts.md)).

## Where the code is

- `vaelii.impl.rules` — `generated-rule`, `generator?`, `holes`, the generator arm of
  `range-problems`, and the hole-aware `variable-functor-literals`.
- `vaelii.impl.sentex` — `connective-problems`, whose consequent arm admits a rule at
  depth 1 and refuses it at depth 2.
- `vaelii.impl.naming` — `applied-literals`, which tags a stamped rule's literals
  `:generated-antecedent` / `:generated-consequent` so the index check can tell them
  from the generator's own.
- `vaelii.impl.checks` — `check-rule!` (the list both doors read), `rule-violation`
  (its value form, for the firing), `generator-cycle`.
- `vaelii.impl.chain` — `mint-rule`, and the `place-conclusion` dispatch that routes a
  rule-valued conclusion to it.
- `vaelii.impl.resolution` — `rule-believed?`, which is what makes a mint retractable.
- `vaelii.core` — `check-generator`, the forward-only and cycle refusals.

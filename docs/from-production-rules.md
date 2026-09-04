# Arriving from a production rule engine

- **Covers:** the CLIPS, Jess and Drools vocabulary mapped onto this one — facts,
  templates, the two rule halves, matching — and the three things a rule engine gives you
  that are absent here on purpose: RHS actions, conflict resolution, and an explicit run.
- **Not here:** how forward chaining and the alpha network actually work →
  [inference.md](inference.md); the `do/` imperatives, which are the nearest thing to a
  right-hand side and are a different mechanism → [labeling.md](labeling.md).
- **Assumes:** sentex, context, handle, justification → [glossary.md](glossary.md).

The match half will feel familiar: patterns with variables, incremental matching, a
fixpoint. The act half will not, because there is no act half. A rule concludes a
sentence, and that is the whole of what firing does.

## Word for word

| in CLIPS or Drools | here | what changes |
|---|---|---|
| a fact | a sentex | a sentence *plus* the context it holds in |
| `deftemplate` slot | an argument position, typed by `(arg P n T)` | positional rather than named → [argtypes.md](argtypes.md) |
| `defrule` LHS | the antecedents | canonicalized, so written order is not recoverable |
| `defrule` RHS | the **consequent sentence** | a conclusion, not a body of actions |
| a `not` conditional element | `(unknown S)` | ground and closed → [naf.md](naf.md) |
| a `test` CE | an evaluable prover | measure comparison, equality, arithmetic → [quantity.md](quantity.md) |
| salience | — | absent, deliberately |
| module | context | and a read sees up the `genlCx` ancestor set |
| a fact-index `?f` | a handle | allocated in assertion order, and belief must never key on it |
| `logical` support | a justification | not optional, and not per-rule |
| the agenda | the agenda | the word survives; the conflict-resolution strategy does not |

## The RHS is a conclusion, not an action

A rule concludes a sentence. There is no `printout`, no `bind`, no function call, no slot
mutation, no `assert` of something unrelated to what the rule proved. The consequent is a
literal in the same language as the antecedents, and firing stores it with a justification
pointing back at the match.

That constraint is what makes everything downstream possible: because a conclusion records
what it rests on, retracting the premise can withdraw it, `why` can print the tree, and
the same rule can be run backward. A rule with side effects has none of those properties.

Where you genuinely need to *make something happen* — enumerate answer sets, materialize a
labeling — there is a small explicit vocabulary of `do/` imperatives, which are never
stored and are legal only at top level. → [labeling.md](labeling.md)

## There is no conflict resolution

No salience, no LEX or MEA, no depth or breadth strategy to select. This is not an
omission; it is the point. **Order independence** is a property the engine holds: the same
knowledge asserted in any order yields the same beliefs, every tie-break keys on content
rather than on a handle, and there is a test that enumerates permutations and demands one
outcome. A strategy you could configure would be a way to break that.

Two familiar behaviors fall out rather than being configured:

- **Refraction** comes from canonicalization. The same conclusion reached twice is one
  handle with a second justification, not a second firing with a second fact.
- **Truth maintenance** replaces the salience idiom of ordering rules so that retractions
  happen before re-derivations. Belief is recomputed from current state, so there is no
  ordering to get right.

Forward chaining is a semi-naive fixpoint over one agenda — strict and defeasible rules
alike, not a two-phase defaults loop. Recursion is bounded by a derived-datum depth
(`:max-depth`, default 64) with a `:max-derivations` backstop. → [inference.md](inference.md)

## Matching: an alpha network, opt-in, and no beta network

`vaelii.impl.rete` is a TREAT-style alpha network, and it is **off by default**. The
reason is that the secondary index roots already answer what alpha memories would — facts
by functor, by argument position, by context — so an alpha network is a second copy of an
index that exists. Enable it with `(rete/enable!)` where a workload wants it.

**There is no beta network.** TREAT re-joins on every firing rather than maintaining
partial-match memories, which trades match cost for the memory and update cost a beta
network carries. A multi-way join is recomputed per firing. That is a stated design
position, and the doc for it says so as a fact rather than as a gap.

Connected conjunctive antecedents join on shared variables, and the join order is chosen
by a cost-based planner rather than by the order you wrote them.

## Logical support is not optional here

In CLIPS, `logical` is a keyword you put on the conditional elements whose retraction
should withdraw the conclusion. Here every conclusion carries a justification — antecedent
handles plus an informant — and retraction is dependency-directed by default: mark the
consequence closure, relabel (a conclusion with another surviving witness stays believed),
then sweep what has no support left.

The thing with no counterpart is **strength**. A sentex is `:monotonic` (known-true, never
defeasible) or `:default` (defeasible, and the common case for common-sense content), and
a justification confers the weaker of its own class and its weakest antecedent. Two
classes, total-ordered, and there is deliberately no third. → [nmtms.md](nmtms.md)

## Negation

The `not` conditional element becomes `(unknown S)`, with two constraints a rule engine
does not impose: it is ground and closed, so an open `(unknown (flies ?x))` is refused
rather than answered under the wrong quantifier, and a cycle through negation is refused
at assert time with `:not-stratified`.

`exceptWhen` is the one with no counterpart, and it is the reason most rules here need no
negated CE at all. A rule states its own exception; when the exception holds the
conclusion is **never created**, rather than being created and then removed. The exception
is re-evaluated per firing and never stored. → [exceptions.md](exceptions.md)

```clojure
(v/assert kb '(exceptWhen (penguin ?b)
                (set/defaultRule (implies (bird ?b) (flies ?b))))
          ctx)
```

`exceptWhen` wraps the rule rather than being an option beside it, so the exception is
part of the rule's identity — and a vector of literals in the exception slot blocks only
when **all** of them hold.

## The call you would have made

| in CLIPS | here |
|---|---|
| `(run)` | nothing — chaining happens on assert, and `settle` runs after every mutation |
| `(run N)` | a budget: `ask-within` / `prove-within` with `:max-results` or `:max-ms` → [anytime.md](anytime.md) |
| `(assert (f a))` | `(v/assert kb '(f a) ctx)` → a handle |
| `(retract ?f)` | `(v/retract! kb handle)` — and it cascades |
| `(facts)` | `(v/sentexes-in-context kb ctx)` |
| `(agenda)` | `(v/chain-stats kb)`, `(v/settle-stats kb)` |
| `(watch facts)` | `(v/watch kb goal context f)` — a callback when belief moves → [feed.md](feed.md) |
| `(undefrule r)` | `(v/retract! kb handle)` on the rule's own handle |
| `(dependencies ?f)` | `(v/why kb handle)` |

`with-deferred-settle` is what to reach for when you are loading in bulk and want one
relabel at the end rather than one per assert.

## What you keep

- Forward chaining to a fixpoint, incrementally
- Pattern variables, and joins on shared variables across conditional elements
- A fact's identity, so you can retract exactly what you asserted
- Logical support — now unconditional
- Modules, as contexts, with a visibility relation between them

## What you lose

- Salience and every conflict-resolution strategy
- RHS actions: no I/O, no bindings, no procedural functions
- An explicit `(run)`, and control over when the engine works
- A beta network, and the partial-match memories that come with it
- Named template slots. Arguments are positional, and typed by declaration

## What you gain

- Backward chaining over the same rules, so one rule base answers both directions
- Contexts, and a rule that fires differently depending on which one is read from
- `exceptWhen`, and defeasible defaults that need no negated CE
- `why` and `why-not` over any conclusion → [nmtms.md](nmtms.md)
- A rule you can *query for*, because a rule is a sentex like any other
- A cost-based planner for the join a beta network would have memoized → [inference.md](inference.md)

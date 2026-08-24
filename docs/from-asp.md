# Arriving from answer set programming

- **Covers:** the answer set programming vocabulary mapped onto this one — rules,
  choices, constraints, the three negations — and the two structural differences that
  matter more than any of the names: there is no grounding step, and belief is not a
  model.
- **Not here:** the clingo and clasp backend a contested edge is actually solved on,
  which is ASP the machinery rather than ASP the language → [asp.md](asp.md); the
  vocabulary that builds a program for it → [solving.md](solving.md),
  [labeling.md](labeling.md).
- **Assumes:** sentex, context, handle, defeasible → [glossary.md](glossary.md).

A solver you already know is in here, and reaching it feels nothing like writing a
program for it. Read the two structural sections before the tables.

## Word for word

| in ASP | here | what changes |
|---|---|---|
| atom | a ground sentex | a sentence *plus* the context it holds in |
| `h :- b1, b2.` | `(implies (and b1 b2) h)` | a rule is a sentex too, with a handle and truth maintenance → [inference.md](inference.md) |
| `{h} :- b.` | `set/assumptionRule` | a choice, and the only thing a solve is free to pick |
| `:- b.` | `set/hardConstraint` | renders as a genuine integrity constraint; the model is excluded |
| `:~ b. [w@l]` | `set/softConstraint` | a violation atom and a `#minimize` at that level |
| `not a` | `(unknown a)` | a query operator, ground-only, storing nothing |
| `-a` | `(not S)` | a **stored** negative sentex with its own handle, not an absence |
| an answer set | a labeling context | materialized, inert, one per optimal answer set |
| `X` | `?x` | |
| `p/2` | — | arity is not part of a name; declare it with `(arity p 2)` or `arg` |
| `#show` | — | reads are queries; nothing is projected at solve time |
| cautious consequence | `forced` | |
| brave consequence | `supportable` | |
| in no optimal model | `excluded` | |

## There is no grounding step

This is the difference to internalize first. There is no program text, no ground-then-
solve, no moment at which the rule base is handed to a grounder. Facts and rules are
asserted one at a time into a store, indexed as they land, and the truth maintenance
system relabels the affected region after every mutation. Nothing re-grounds because
nothing was ground.

What that buys is incrementality: asserting a fact costs the region it touches, not the
program. What it costs is that whole-program reasoning is not automatically available —
you ask for it, over a bounded region, and only where a contradiction actually needs
deciding.

When a solve does run, it grounds the assumption rules visible from its base context and
nothing else. **The ordinary rule base is not emitted to the solver**, so a choice does
not propagate through your `implies` rules the way it would through a program. That is a
real limit and [solving.md](solving.md) states it as one.

## The KB is not a program, and belief is not a model

There is one knowledge base, and almost everything in it is true almost all the time.
There is no "the answer sets of the KB" — the question does not typecheck. Belief is a
single labeling computed by a justification-based truth maintenance system as a least
fixpoint, recomputed from current state rather than accumulated, and it is *the* answer
rather than one of several. → [nmtms.md](nmtms.md)

Defeat is that system's, not the solver's. Two `:default` claims that rebut each other
both stay believed and are reported as a represented dilemma; the engine arbitrates
nothing on its own. ASP is what you reach for when a particular contested edge has to be
decided, and it is opt-in per KB:

```clojure
(v/set-solver kb :asp)          ; the default is a greedy stub that decides nothing
```

The consequence worth stating plainly: a plain rebuttal with neither side naming the
other's case — a Nixon diamond — builds no program at all, so classification over it
answers empty sets. That shape is exactly the one a solve cannot be demonstrated with.

## Negation, and there are three

| you want | write | what it is |
|---|---|---|
| negation as failure | `(unknown S)` | closed-world, evaluated at level 6, storing nothing → [naf.md](naf.md) |
| classical negation | `(not S)` | a stored sentex with a handle, believed or not like any other |
| "usually, but not when…" | `exceptWhen` | undercuts the **rule**, not the literal; the conclusion is never created → [exceptions.md](exceptions.md) |

`exceptWhen` is the one with no ASP counterpart, and it is the idiomatic way to write a
default here. It is undercutting defeat: the rule states its own exception, the exception
is re-evaluated per firing, and it is never stored.

Two constraints on `unknown` that a program would not impose. It is **ground and closed**
— an open `(unknown (flies ?x))` is refused rather than answered — and `thereExists`
projects a variable out so `unknown` can negate the result. And **stratification is
enforced at assert time**: a cycle through negation throws `:not-stratified`, including
the one-rule cycle and a cycle a `genl` edge would close. You learn about it when you
write it, not when you solve.

## Choices, constraints and the solve

The three wrappers, all assert-time and all canonicalized into the rule record:

```clojure
(v/assert kb '(set/assumptionRule (implies (candidate ?x) (chosen ?x)))     ctx)
(v/assert kb '(set/hardConstraint (implies (and (chosen ?x) (barred ?x)) (bannedChoice ?x))) ctx)
(v/assert kb '(set/softConstraint (implies (and (chosen ?x) (costly ?x)) (dearChoice ?x)))   ctx)
```

A constraint's head is a **contradiction marker** rather than a truth, and it is a real
literal held to the ordinary range restriction — every variable in it comes from the
body. A bare symbol there is refused `:not-well-formed`.

Each is a **virtual wrapper canonicalized into the rule record**, not a function you
call — it is part of the sentence, so a choice rule and its bare twin are different
sentexes with different handles. A constraint's head is a contradiction marker rather
than a truth. An assumption rule never chains into belief: `(candidate Item)` does not
derive `(chosen Item)`, and a solve is the only thing that consults it.

A solve is asked for by asserting a `do/` imperative, which is a virtual functor: it is
never stored, and it is refused anywhere but the top level — not as a rule antecedent,
not in a consequent, not inside `exceptWhen`.

| you want | write | what happens |
|---|---|---|
| enumerate and materialize | `(do/label Base Into)` | one **inert** context per optimal answer set, written under `Into` |
| one optimum, persisting nothing | `(do/label Base Into :one)` | |
| first model, no optimization | `(do/label Base Into :sat)` | |
| the three-way classification | `(do/classify Into)` | `forced` / `supportable` / `excluded` |
| label a context in place | `(do/labeling Ctx)` | entrenches what it records — classify *before* you label |

"Inert" is exact: a materialized labeling is stored outside the truth maintenance system
entirely, never believed, never chained, never scanned for contradictions. The base KB is
untouched by a solve. → [solving.md](solving.md)

Optimization is a three-level objective — caller priority above defeated assumptions
above a content-keyed tiebreak — and the tiebreak is what makes a solve deterministic
under reordering. Atom ids are allocated in content order, never in handle order.

## The solver you already run is in here

clingo runs **in-process** through raw JNA — no JNI, no generated bindings — and clasp
runs as a subprocess taking ASPIF on stdin. Which one answers is chosen by program byte
size (`VAELII_CLINGO_MAX_BYTES`, default 3000), and either can be forced. With no backend
reachable the seam degrades to the stub rather than failing. Install with
`brew install clingo`; the test profile is `lein with-profile +with-clingo test`.

`(v/last-program kb)` hands back the last program solved, which is the thing to read when
a solve answers something surprising. → [asp.md](asp.md)

## The call you would have made

| in ASP | here |
|---|---|
| `clingo prog.lp` | `(v/assert kb '(do/label Base Into) ctx)` |
| `clingo -n 0` | the `:all` mode, which is the default |
| `clingo --enum-mode=cautious` | `(do/classify Into)`, reading `forced` |
| the same, brave | `(do/classify Into)`, reading `supportable` |
| `#show p/1` | `(v/query kb goal ctx)` — an ordinary read → [api.md](api.md) |
| grounding | nothing; there is no such step |
| inspecting the ground program | `(v/last-program kb)` |

## What you keep

- The stable-model intuition for choices, and brave versus cautious consequence
- Integrity constraints that genuinely exclude a model
- Optimization by weak constraints with priority levels
- Determinism: same knowledge, any order, same answer — and it is a property the engine
  holds globally, not only inside a solve → [nmtms.md](nmtms.md)

## What you lose

- Whole-program semantics. A solve sees the assumption rules of one region
- Disjunctive heads
- `#count` and `#sum` as part of the **model**. The five reductions work in a rule body —
  `(agg/count ?n ?v Body)` after the generator antecedent that binds the group, re-checked
  as the census moves — but they are *query* operators a prover computes rather than atoms
  a solve reasons over, and none may be a rule's consequent. GROUP BY falls out of which
  variable an antecedent binds → [aggregate.md](aggregate.md)
- Multi-shot solving. A solve is one program, built from one region, answered once
- Theory atoms and any constraint layer over integers

## What you gain

- An incremental store with truth maintenance: assert one fact, pay for one region
- Contexts, so the same sentence can hold differently in two places → [contexts.md](contexts.md)
- Defeasible defaults with stated exceptions, which need no choice rule at all
- Cascading retraction, and `why` / `why-not` to ask why something is or is not believed
- Six qualitative relation algebras and metric time → [qcn.md](qcn.md), [stp.md](stp.md)
- Backward chaining over the same rules a forward pass uses

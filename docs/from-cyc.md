# Arriving from Cyc

- **Covers:** the OpenCyc and ResearchCyc vocabulary mapped onto this one — concepts,
  contexts, negation, operations, truth maintenance and rules — and the places where a
  shared name covers a different semantics.
- **Not here:** reading an OpenCyc corpus *in*, which is a plugin and a different task →
  [foreign.md](foreign.md), [kbs.md](kbs.md); the engine itself, which every row below
  links to → [README.md](README.md).
- **Assumes:** sentex, context, handle → [glossary.md](glossary.md). The API this page
  calls is [api.md](api.md).

One-way orientation, not a compatibility claim. The two systems share a great deal of
vocabulary and part company on the semantics more often than the names suggest, so the
third column is the one to read.

## Word for word

| in Cyc | here | what changes |
|---|---|---|
| `Mt` | context | a sentex is in exactly one, and reads see up the `genlCx` cone → [contexts.md](contexts.md) |
| `genlMt` | `genlCx` | cached and recomputed on edge change, not derived by a rule |
| assertion | sentex | a sentence *plus* the context it holds in; the pair is the unit |
| constant | symbol | the role is read off the spelling, and `assert` refuses one that breaks it |
| collection | a type, which is a **unary predicate** | `(dog Muffet)`, never `(isa Muffet Dog)` |
| `genls` | `genl` | |
| `genlPreds` | `genl` | one relation for both, because a type *is* a predicate here |
| `arg1Isa` / `arg2Isa` | `(argIsa P 1 T)` | the position is an argument, so there is no per-position predicate to learn |
| don't-care variable `??` | a head existential `(exists ?y C)` | syntactic rather than a naming convention, and skolemized to a deterministic NAT on firing → [skolem.md](skolem.md) |
| `wff?` | `check` | returns a vector of problem maps rather than a verdict, so it says *what* is wrong |
| rename | — | no equivalent. `sameAs` / `rewriteOf` **merge** two terms onto an elected representative and mark the displaced spelling superseded, which is a different act → [equality.md](equality.md) |

The four spellings, because `assert` enforces them (→ [naming.md](naming.md)):
`parentOf` is a predicate, `Fido` an individual, `physical_object` a type, `CxCore` a
context. A bare lowercase word like `dog` is both a predicate and a type name, and arity
decides which; an underscore commits the name to arity 1.

## What a Cyclist's habits do here

**`argIsa` is a gate first.** `(argIsa parentOf 1 animal)` — the shipped ontology's own
declaration — refuses `(parentOf Fern Mary)` where `Fern` is a `plant`: `ex-info` with
`:type :arg-type`, exactly as Cyc's constraint would refuse it. What convicts is that the
hierarchy **places** `Fern` and the place it puts him does not reach `animal`. The
`(disjoint animal plant)` sitting beside those types is not what does the work — a type
the constraint's own type does not subsume is enough on its own.

There is one open-world escape and it is deliberate: an argument the `genl` hierarchy
places nowhere *the asserting context can see* cannot contradict anything, so it passes.
`(parentOf Zork Mary)` stores when nothing is known about `Zork`, and `(parentOf 212
Mary)` stores for the harder version of the same reason — a number can hold no type
membership, so no declaration has anything to convict it on.

The *entailment* reading — the same declaration minting `(animal Fred)` from
`(parentOf Fred Mary)` — is real but **opt-in**, behind
`checks/*assertive-arg-types?*` (root value false, or `VAELII_ASSERTIVE_ARG_TYPES=1`).
It is additive: turning it on keeps the refusal and adds the derived type, as a justified
sentex that retracts like any conclusion. See [argtypes.md](argtypes.md).

**Undeclared is unconstrained — which is not the same as unchecked.** No predicate has to
be declared before use, so `(fghgwgads 212)` stores and a typo is the same bug class as a
predicate nobody has gotten to yet. But as soon as declarations exist they bind: `assert`
refuses on arity, `argIsa`, `argGenl`, `interArgIsa`, disjointness, asymmetry and
functionality, on top of the naming, groundness, structural and stratification checks it
always runs. `check` reports the lot without storing → [api.md](api.md).

**A contradictory pair coexists.** Two `:default` claims that rebut each other both stay
believed and are reported as a represented dilemma by `contradictions`; the engine
arbitrates nothing on its own. Insertion-time integrity is not the model —
[nmtms.md](nmtms.md) is why, and `set-solver` is what you reach for when an edge has to
be decided → [solving.md](solving.md).

## Negation and mutual exclusion

| in Cyc | here | what changes |
|---|---|---|
| `negationPreds`, unary | `(disjoint P Q)` | native, because collections *are* predicates; closed under `genl` |
| `negationPreds`, binary and up | a pair of implication rules | no declarative form — see below |
| `disjoint` | `disjoint` | same reading, and `(disjointMetatype M)` makes every member pairwise disjoint without writing the pairs |
| `SymmetricBinaryPredicate` | `(symmetric P)` | |
| `AsymmetricBinaryPredicate` | `(asymmetric P)` | convicts a claim whose **converse** is believed; it does not make `P` irreflexive, and `(P a a)` is admitted |
| `genlInverse` | a forward rule | `(inverse P Q)` exists but is the stronger biconditional |
| `unk` | `unknown` | negation as failure, ground-only, evaluated at level 6 and storing nothing → [naf.md](naf.md) |
| — | `(contradictions kb)` | no Cyc equivalent: the pairs that coexist, ordered by content |
| `assertedMoreSpecifically` | — | no equivalent. Specificity is behavioral: a stated specific claim undercuts an inherited general one, so nothing is derived to arbitrate → [inherit.md](inherit.md) |
| `completeExtentEnumerable` | — | no equivalent. Closure is chosen per goal by `unknown` / `thereExists` / the aggregates, never declared of an extent |
| `notAssertible` | — | no equivalent |

Binary mutual exclusion is written as the two rules, and `(not S)` is a stored sentex
with its own handle rather than an absence:

```clojure
(v/assert-rule kb ['(P ?x ?y)] '(not (Q ?x ?y)) 'CxSomeContext)
(v/assert-rule kb ['(Q ?x ?y)] '(not (P ?x ?y)) 'CxSomeContext)
```

`(inverse P Q)` is worth knowing properly, because it is stronger than `genlInverse` in
three ways: it is stored under an unordered key so one declaration installs both
directions, a predicate may declare **several** partners and all are live, and a partner
declared on a sub-predicate answers the super-predicate's goal.

## Well-formedness: lenient by default, assertive on request

Cyc's three modes, and what each maps to:

| mode | in Cyc | here |
|---|---|---|
| strict | constraints must be provable | no equivalent |
| lenient | constraints must not be disjoint | **the default** — a demonstrated conflict is refused, an argument with no place in the hierarchy is excused |
| assertive | that, plus eagerly concluding tighter `isa`s | `checks/*assertive-arg-types?*`, off by default, and additive rather than a replacement |

One naming collision to hold: `vaelii.impl.wff` is narrower than Cyc's "WFF". It is the
**structural** check on the special predicates — `genl` and `genlCx` acyclicity, the
shape of `disjoint`, `argIsa`, `argGenl` and `inverse` — and throws `:not-well-formed`.
The content constraints above are a separate stage. `check` runs both.

## The contexts you already have names for

| in Cyc | here | what changes |
|---|---|---|
| `LogicalTruthMt` | — | no analogue; the logical truths are the engine's, not a context's |
| `CoreCycLMt` | `CxCore` | the spindle head: the vocabulary code interprets |
| `UniversalVocabularyMt` / `BaseKB` | `CxUniverse` | the mid anchor, and where a decontextualized claim lands |
| `CurrentWorldDataCollectorMt` | `CxWell` | the collector — sees the whole shipped ontology |
| `InferencePSC` / `EverythingPSC` | `?ctx` | **not a context at all**: omit the argument or pass a variable to read unscoped |

That last row is the one that catches people. There is no everything-context to assert
into; scope is a property of the read.

## The call you would have made

| in Cyc | here |
|---|---|
| `assert` | `(v/assert kb sentence context opts)` → a handle |
| `unassert` | `(v/retract! kb handle)` → `{:removed-sentexes n :removed-justifications n}` |
| `find-assertion-cycl` | `(v/sentexes-matching kb sentence context)` — literal only, and a collection |
| `ask`, backward and bounded | `(v/query kb goal ctx {:max-depth n})` |
| `ask`, unbounded | `(v/prove kb goal ctx)` — DFS, terminating on the data |
| `ask`, boolean | `(v/provable? kb goal ctx)` |
| `ask`, no inference | `(v/ask kb goal ctx)` — the prover registry, and no member expands a rule |
| `fi-ask` | `(v/query kb goal ctx {:max-depth n})` |
| `wff?` | `(v/check kb sentence context opts)` |
| rename | — |

`prove` returns one binding map per **derivation**, so equal maps repeat; `distinct` if
you wanted a set. Which door answers what, and what each costs, is
[levels.md](levels.md).

## Truth maintenance

| in Cyc | here |
|---|---|
| TMS assert | `(v/assert kb s ctx {:strength :monotonic})` for known-true, `:default` — the default — for defeasible |
| TMS retract | `(v/retract! kb handle)`, tearing down whatever rested solely on it |
| `why` | `(v/why kb handle opts?)` — the proof tree, cycle-guarded |
| `why-not` | `(v/why-not kb handle)` → `:defeated` / `:superseded` / `:unsupported` / `:not-stored`; the sentence arity adds `:excepted` |
| — | `(v/in? kb handle)`, `(v/believed kb handles)` — a stored sentex is not a believed one |
| — | `(v/settle-stats kb)`, `(v/with-deferred-settle kb & body)` |

Two strength classes and no third: `:monotonic` and `:default`, total-ordered, with a
justification conferring the weaker of its own class and its weakest antecedent.
[nmtms.md](nmtms.md).

## Rules

A rule is a sentex — same structure, same handle, same truth maintenance, additionally
indexed by its antecedent and consequent predicates. So it can be retracted, asked about,
and believed or not.

| in Cyc | here |
|---|---|
| assert a rule | `(v/assert-rule kb [antecedents] consequent context opts)` |
| `forwardRule` | `{:direction :forward}`, or the `set/forwardRule` wrapper |
| `backwardRule` | `{:direction :backward}`, or `set/backwardRule` |
| both, the default | `{:direction :both}` |
| `:code` direction | `{:direction :inert}`, or `set/inertRule` — believed and indexed, fires neither way |
| rule variables | `?x` |
| range restriction | enforced: every consequent variable appears in an antecedent, the one exception being a marked head existential |

Three refusals to expect. A literal whose functor is a **variable** is `:not-indexable`,
in an antecedent or a consequent and whether or not something binds it — the index is
keyed by predicate, so there is nothing to key on. A consequent variable appearing in no
antecedent is `:not-range-restricted`. A cycle through negation is `:not-stratified`, and
it is refused at assert time rather than diagnosed later.

A rule whose consequent is *itself* a rule is not an error — it is a **generator**, and it
fires, stamping out a real indexed rule with concrete functors, justified by the firing
so that retracting the generator un-believes what it stamped. Variables the enclosing
antecedents also mention are holes filled at mint time, and a hole may stand in functor
position. Nesting is not capped. → [generators.md](generators.md)

## What you keep

- Anytime inference on a budget: `ask-within`, `prove-within`, `resume` → [anytime.md](anytime.md)
- Reactive queries: `(v/watch kb goal context f)` → [feed.md](feed.md)
- Abduction: `(v/abduce kb goal context opts)`, hypotheses minted as defeasible premises in a scratch context → [abduction.md](abduction.md)
- `argIsa` and `interArgIsa` → [argtypes.md](argtypes.md)
- One equality partition behind `rewriteOf` / `sameAs` / `equals` → [equality.md](equality.md)
- Defeasible defaults with exceptions → [exceptions.md](exceptions.md)
- Polycanonicalization, so a conjunctive consequent becomes one rule per conjunct

## What you lose

- Rename
- Natural-language generation
- `completeExtentEnumerable`, `notAssertible`, `assertedMoreSpecifically`
- `negationPreds` above arity 1 — the paired rules above are the translation
- `arg1Isa` / `arg2Isa` sugar
- Strict well-formedness mode
- `irreflexive`, `antiTransitive`, `antiSymmetric`. The marks that exist are `symmetric`,
  `asymmetric`, `transitive`, `reflexive`, `functional`, `inverse`, `arity` and
  `variableArity`, and `asymmetric` is not a substitute for the first: it convicts
  against a believed converse, and a self-tuple has none.

`transitiveViaArg` is **not** on this list — it is spelled `transitiveInArg` here:
`(transitiveInArg P n R)` and `(transitiveInArgInverse P n R)` carry a claim about argument
`n` across any declared-transitive `R`, with the direction and the argument position
declared separately → [inherit.md](inherit.md).

## What you gain

- `fork` — a private writable overlay over a shared frozen base → [overlay.md](overlay.md)
- An ASP solver behind the contradiction seam, `(v/set-solver kb :asp)` → [asp.md](asp.md)
- Six qualitative relation algebras, plus metric time → [qcn.md](qcn.md), [stp.md](stp.md)
- Export and import of a whole KB → [storage.md](storage.md)
- A browser over terms, sentexes and justifications → [web.md](web.md)
- Rule generators → [generators.md](generators.md)
- A query planner that orders a conjunction on cost, and `query-plan` to read what it
  chose → [inference.md](inference.md)

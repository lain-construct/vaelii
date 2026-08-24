# Arriving from Prolog or Datalog

- **Covers:** the logic-programming vocabulary mapped onto this one — rules, variables,
  negation, search — and the three habits that do something different here: capitalization,
  clause order, and what retraction reaches.
- **Not here:** how backward chaining actually works, the two chainers and the query
  planner behind them → [inference.md](inference.md); which of the query doors answers a
  goal, and what each costs → [levels.md](levels.md), [api.md](api.md).
- **Assumes:** sentex, context, handle → [glossary.md](glossary.md).

Most of what you know transfers. The engine unifies with an occurs-check, chains
backward, enforces the safety condition and stratifies negation. What does not transfer
is control: there is no cut, clause order is not a lever, and a name's capitalization
means very nearly the opposite of what it means to you.

## Word for word

| in Prolog or Datalog | here | what changes |
|---|---|---|
| clause | a rule sentex | it has a handle, it is believed or not, and it can be retracted and asked about |
| fact | a sentence in a context | the context is half the unit → [contexts.md](contexts.md) |
| `X`, `Foo` — a variable | `?x` | the question mark is the marker, and capitalization is doing something else entirely |
| an atom | a symbol whose role is read off its spelling | see below |
| compound term | a NAT — reified to a constant, or kept structural → [nat.md](nat.md) |
| `\+ G` | `(unknown G)` | ground and closed only |
| `dif/2` | `(different A B)` | a prover, never assertible; the unique-name assumption is kept |
| `p/2` | — | arity is not part of the name; `(arity p 2)` or `arg` declares it |
| module | context | and a read sees up the `genlCx` cone |
| EDB versus IDB | premise versus derived | both are sentexes; `premise?` tells them apart |
| `findall/3` | `prove`, then `distinct` | one binding map per **derivation**, so equal maps repeat |

## Your capitals mean the opposite here

This is the collision that will bite on the first line you type. In Prolog, `X` is a
variable and `foo` is an atom. Here:

| spelling | role | example |
|---|---|---|
| `?x` | a variable | the only variable form |
| `CapitalCamelCase` | an **individual** | `Fido`, `Tom` |
| `camelCase` | a predicate | `parentOf`, `genl` |
| `snake_case` | a type, which is a unary predicate | `physical_object` |
| `Cx` + `CapitalCamelCase` | a context | `CxCore` |

These are not style. `assert` reads a symbol's role off its spelling and **refuses** a
sentence that breaks one, with `ex-info` carrying `:type :naming`. A snake_case functor
names a type and a type is one-place, so `(lives_in ?x cold_place)` is refused — write
`livesIn`. A bare lowercase word like `dog` satisfies both the predicate and the type
convention, and arity decides which. → [naming.md](naming.md)

Two more refusals in the same family. A non-ground fact is refused: `(mortal ?x)` asserts
nothing, and a universal is a rule, which is where variables belong. And every literal is
checked, not only the outermost — a rule's consequent and an `exceptWhen` goal are held to
the same invariants as a fact.

## What your habits will do here

**Clause order is not control.** A rule's antecedents are canonicalized at storage, so
their written order is not recoverable and cannot be a lever. A conjunctive goal is
ordered by a **cost-based planner** under sideways information passing, not left to right,
and `query-plan` will show you what it chose. Left-recursion is not a state a rule can be
in. → [inference.md](inference.md)

**There is no cut**, and nothing else prunes a branch by fiat. The nearest things are a
budget (`:max-results`, `:max-ms`) and a tactician mode that reduces the answer set and
says so. If you were using cut for determinism, the honest translation is usually
`exceptWhen` — a stated exception that undercuts the rule rather than a scar in the
search.

**The same clause twice is one handle.** Sentences identical up to variable naming,
antecedent order, symmetric argument order or comparison direction canonicalize to a
single stored sentex. Asserting a duplicate adds a justification, not a second copy. →
[canonicalization.md](canonicalization.md)

**`assert` can refuse you.** It is not the unconditional store you are used to: naming,
groundness, structural well-formedness, arity, argument types, disjointness and
stratification all run first, and each throws a distinguishable `:type`.

## Search: what terminates, and what you bound

| you want | call | termination |
|---|---|---|
| everything, unbounded | `(v/prove kb goal ctx)` | DFS with a per-path visited set over variable-collapsed goal keys — it terminates on the data |
| bounded rewrites | `(v/query kb goal ctx {:max-depth n})` | the node engine, bounded at that many rule rewrites |
| no inference at all | `(v/ask kb goal ctx)` | the prover registry; no member expands a rule |
| a stored-shape read | `(v/sentexes-matching kb sentence ctx)` | an index read, belief-filtered |

Two things to know. `query` **without** `:max-depth` does not open a proof search at all —
it answers from the prover registry, and the depth bound is what turns it into
backchaining. And `prove` returns one solution per *derivation* where the node engine
returns one per *answer*, so counting results is a question about which engine ran.

A vector goal is a conjunctive join, planned rather than sequenced. Eight named levels
sit between a raw index read and full backchaining, and `explain-levels` will tell you
which one answered → [levels.md](levels.md).

## Negation

`(unknown G)` is `\+`'s closed-world reading. Three differences from Prolog's:

- It is evaluated at **level 6**, so a forward-derived fact counts, but something
  reachable only by backward chaining does not.
- It is **ground and closed**. An open `(unknown (flies ?x))` is refused rather than
  quietly answered under the wrong quantifier. `(thereExists ?x S)` projects a variable
  out so the result can be negated.
- **Stratification is enforced at assert time**, not diagnosed at runtime. A cycle
  through negation throws `:not-stratified`, including a cycle that a `genl` edge would
  close. → [naf.md](naf.md)

`(not S)` is a different thing again: a stored negative sentex with its own handle, which
is neither failure nor absence.

## Rules

Range restriction is Datalog's safety condition, and it is enforced rather than advised:
every consequent variable must appear in an antecedent, on pain of
`:not-range-restricted`. The one exception is a marked head existential `(exists ?y C)`,
skolemized to a deterministic NAT constant when the rule fires.

| you want | write |
|---|---|
| forward only | `{:direction :forward}` or `set/forwardRule` |
| backward only | `{:direction :backward}` or `set/backwardRule` |
| both — the default | `{:direction :both}` |
| neither, but stored and believed | `{:direction :inert}` or `set/inertRule` |
| a defeasible rule | `set/defaultRule` |
| a stated exception | `exceptWhen` → [exceptions.md](exceptions.md) |

A conjunctive consequent splits into one rule per conjunct. A rule **antecedent** whose
functor is a variable is refused `:not-indexable`, whether or not something binds it: the
antecedent index is keyed by predicate, so a variable there names none for an arriving
fact to trigger, and the rule would fire over whatever happened to be stored when a
concrete antecedent beside it arrived. A variable functor in the **consequent** is legal —
range restriction makes it antecedent-bound, so a forward firing is ground, and the
consequent slot files it under a catch-all cell every backward goal reads. A rule whose
consequent is itself a rule is a **generator**, and a variable in functor position there
is a hole the enclosing level fills at mint time → [generators.md](generators.md).

## Retraction actually retracts

`retract/1` removes a clause and leaves everything derived from it lying around.
`(v/retract! kb handle)` is dependency-directed: it marks the consequence closure,
relabels — a conclusion with another surviving witness stays believed — and then sweeps
what no longer has support. Nothing you derived from a withdrawn premise silently
outlives it.

This is the piece with no Prolog analogue at all, and it is why every conclusion carries a
justification. `(v/why kb handle)` is the proof tree; `(v/why-not kb handle)` answers
`:defeated` / `:superseded` / `:unsupported` / `:not-stored`, and the sentence arity adds
`:excepted`. → [nmtms.md](nmtms.md)

## The call you would have made

| in Prolog | here |
|---|---|
| `?- G.` | `(v/prove kb 'G ctx)` |
| `?- G, H.` | `(v/prove kb ['G 'H] ctx)` — a planned join |
| `?- G.` as a yes/no | `(v/provable? kb 'G ctx)` |
| `findall(X, G, L)` | `(v/prove kb 'G ctx)`, then read `?x` — `distinct` for set semantics |
| `assert/1` | `(v/assert kb sentence context)` → a handle |
| `retract/1` | `(v/retract! kb handle)` — and it cascades |
| bottom-up Datalog evaluation | `(v/forward-chain kb)`, semi-naive to a fixpoint |
| `listing/1` | `(v/sentexes-with-functor kb 'p)` |

## What you keep

- Unification with an occurs-check, and a Prolog-style rest pattern `(?pred . ?args)`
- Backward chaining, and a goal stack you can bound
- The safety condition, enforced
- Stratified negation, checked earlier than you are used to
- One solution per derivation, from `prove`

## What you lose

- The cut, and control by clause order
- Side-effecting builtins, and `assert` during a proof
- Operator declarations, and DCG notation
- Term ordering as a general facility. A Knuth-Bendix order exists, but it orients
  equations for rewriting rather than comparing arbitrary terms → [equational.md](equational.md)

## What you gain

- Contexts: the same sentence holding differently in two of them → [contexts.md](contexts.md)
- Truth maintenance, and retraction that reaches what rested on the premise
- `exceptWhen`, which is the defeasible default you have been writing with cut
- A cost-based query planner, and `query-plan` to read its choice
- The eight-level stack, which names what answering a goal actually took
- Forward and backward chaining over the *same* rules

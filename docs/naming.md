# Naming invariants

`vaelii.impl.naming`. The KB relies on lexical conventions to tell the role of a symbol.

| Role | Convention | Regex (on the symbol name) | Examples |
|------|-----------|----------------------------|----------|
| predicate | camelCase, lowercase-initial, no `_` | `[a-z][a-zA-Z0-9]*` | `parentOf`, `genl`, `argIsa` |
| individual | CapitalCamelCase | `[A-Z][A-Za-z0-9]*` (not a context) | `Fido`, `Tom` |
| type | snake_case, a **unary** predicate | `[a-z][a-z0-9_]*` | `dog`, `physical_object` |
| context | CapitalCamelCase ending in `Context` | `[A-Z][A-Za-z0-9]*Context` | `UniverseContext`, `CoreContext` |

## Notes

- **Types are unary predicates.** Write `(dog Fido)`, not `(isa Fido Dog)`.
  `thing` is the root of the `genl` hierarchy.
- **Overlap is expected.** A plain lowercase word (`dog`, `genl`, `parentOf`)
  satisfies both `predicate?` and `type-symbol?`. Role is disambiguated by
  position and arity, not the symbol alone — `genl` is a predicate in
  `(genl dog animal)`, `dog` is a type in `(dog Fido)`.
- **Accessors.** `functor`, `args`, `arity` destructure a sentence.

## Enforcement: every literal, and snake_case is unary

`assert` calls `nm/check!` and `check` (docs/api.md, "Validating without writing") calls
`nm/blocking-problems`; both read the KB's policy, and both are `nm/problems` underneath.
It reports, in order: the context's own name, then **every literal's** functor, then any
`ist` context slot, then a dotted rest marker where one cannot appear. Argument-level type
checks are `argIsa`'s job, not a lexical rule's.

### Literals, frames, and arguments

A naming invariant is about a **literal** — a predicate applied to arguments. A
sentence is built from literals plus *frames*, and `nm/literals` descends the frames
to reach the literals:

| Frame | Descends to |
|-------|-------------|
| `(not X)` | `X` |
| `(and X …)` | each conjunct |
| `(implies A C)` | each antecedent (`:antecedent`), then `C` (`:consequent`) |
| `set/forwardRule` · `backwardRule` · `inertRule` · `defaultRule` · `assumptionRule` · `hardConstraint` · `softConstraint` | the rule inside, wrappers nesting in any order |
| `(exceptWhen Q R)` | `Q`'s conjuncts (`:exception`), then `R` |
| `(ist Ctx S)` | `S` (and `Ctx` is checked as a context name) |
| `(unknown S)` · `(thereExists ?v S)` · `(exists ?v C)` | the query / consequent framed |
| `(agg/count ?n ?v B)` and its four siblings | `B` — an aggregate's body is a goal, not an argument ([aggregate.md](aggregate.md)) |
| `(sentexHandle N)` | nothing — it names a stored sentex by id |

Two positions are deliberately **not** literals. **Arguments** are never walked: a
compound in argument position is a *term*, and its head names a function or is plain
data — an arithmetic expression `(evaluate ?s (+ 1 2))`, a NAUT `(QuantityFn 5
Meter)`, a quoted connective `(comment not "…")`. And a **variable in functor
position** is a pattern that names no predicate, so the dotted rest form
`(?pred . ?args)` and a bare `(?p ?x)` pass.

Descending the frames is what makes the check reach a rule. A rule's outermost functor
is `implies`, which is engine vocabulary, so a check that stopped there would examine
nothing an author wrote: `(implies (penguin ?x) (lives_in ?x cold_place))` is refused
for its consequent, and a consequent is exactly where derived and generated content
lands.

### snake_case is a type name, hence unary

A functor carrying an underscore satisfies `type-symbol?` and not `predicate?`, so it
names a **type**, and a type is used as a unary predicate. It is therefore legal at
arity 1 and nowhere else:

```clojure
(physical_object Rock1)              ; fine — a type membership
(lives_in penguin cold_place)        ; refused — a type name doing a relation's job
(livesIn Tweety Antarctica)          ; fine — camelCase, unconstrained in arity
```

A bare lowercase word (`dog`, `likes`) is both, so arity decides and nothing is
refused.

### What a rejection says

The `ex-info` `:type` is `:naming`. A repair loop is handed the message verbatim, so
each one names the literal, the frame it sits in, and the spelling to use instead:

```
functor lives_in in rule consequent (lives_in ?x cold_place) is snake_case, which
names a type and is legal only as a unary predicate, but has 2 arguments — write it
camelCase as livesIn, or as (lives_in <one argument>)
```

A rejection is **data before it is prose**. `nm/problems*` yields one
`{:class :role :symbol :literal}` map per violation — `:class` one of
`:context-name` `:functor` `:functor-arity` `:argument` `:ist-context` `:dot-marker` —
and `nm/message` renders one; `problems` is the two composed. `assert` wants the
sentence it refused spelled out, but anything *counting* violations wants to group, and
a message embeds the literal, so it is unique per record and counting messages counts
records.

### Whose invariants: the two doors

How hard these are enforced is the **KB's** to say, not the build's. `open-kb`'s
`:naming` selects the policy:

| | |
|---|---|
| `:strict` | the default — refuse the assertion, `ex-info` `:type` `:naming` |
| `:warn` | log each one and store anyway (a corpus being cleaned up) |
| `:off` | store in silence (a corpus with spelling conventions of its own) |

It lives on the KB as a plain value, settled when the KB is opened: a store whose policy
moved under it would hold two vocabularies with nothing recording which sentence arrived
under which. So a lenient loader and a strict editor can hold the *same store* at once,
and neither has to win.

`:constraints` is the other door of the same kind, over what a **definitional clash**
does rather than over how a symbol is spelled — `:refuse` or `:arbitrate`, on the KB as a
plain value for the same reason ([nmtms.md](nmtms.md), "Which door the content came through").

What no setting moves is the role **reading**. `predicate?` and its three siblings answer
the same way under every policy, so `:off` stores a name nothing can classify — `term-role`
says nil, a `(Type Individual)` goal takes the general path rather than the shortcut —
never one classified differently. That is the entire cost of opening the door, and it is
why the check is worth keeping on wherever the content is hand-written.

A **bulk** path is not on that list because it does not consult it: an import builds
records directly through `res/kb-sentex` and never asks, which is what makes an
11M-record corpus loadable at all. The two doors are reconciled by a **count** instead.
Both import paths fold `nm/tally` as the frames go past — the one cheap moment, with each
record already decoded — and a non-zero result is logged and returned in the summary as
`{:checked n :refused n :by-class {…}}`:

```
this corpus and `assert` disagree: 11,314,049 of 11,314,049 records (100.0%) hold names
`assert` would refuse: context-name 11,314,049, argument 10,059,528, functor 395,259,
functor-arity 58, dot-marker 9 — they are stored, findable and countable, but
re-asserting one throws under :naming :strict
```

The operator who chose the bulk path learns the fraction then, rather than from a
re-assertion that throws a year later. `lein bench-survey naming` is the same question
asked exhaustively — every record, grouped by class, by frame and by *distinct spelling*,
with candidate widenings priced against the corpus.

### What this does not check

This is a check on the **shape** of a name, never on whether the name is worth having.
A *unary* snake_case functor is a well-formed type name, so

```clojure
(implies (penguin ?x) (has_black_and_white_feathers ?x))
```

passes — as would `capable_of_swimming` or
`thermoregulates_via_blubber_and_feathers`. Nothing about a symbol distinguishes a
type the ontology wants from a one-off coined for a single sentence; judging that needs
the KB's existing vocabulary, which is a different question asked elsewhere. Reading
this check as a guard against vocabulary fragmentation is wrong in the expensive
direction.

## Temporaries in tests

`vaelii.test-util/with-terms` infers a temporary's role from the symbol's own shape and
embeds it in the generated name. A `:type` temp keeps the base's spelling: a base
already carrying an underscore (`physical_object`) becomes snake_case
(`tmp_physical_object_17`) and is therefore unary-only, while a bare lowercase word
(`dog`, `likes`) becomes another bare lowercase word (`tmpdog17`) and stays usable at
any arity — as ambiguous as the word the test wrote. Writing the base with an
underscore is how a test says "a type, and only a type".

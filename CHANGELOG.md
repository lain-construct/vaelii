# Changelog

Notable changes to `vaelii`, newest first. Versions follow
[semantic versioning](https://semver.org/spec/v2.0.0.html); pre-1.0, a **Breaking**
entry raises the minor. What each class means, and why a **Refusal** is patch-eligible,
is [CONTRIBUTING.md §3](CONTRIBUTING.md).

**Releases before 0.17.0 are summarized rather than reproduced.** Each one keeps its
title, its class census and every `*Breaks:*` token, so an upgrade across several
releases is still a grep for the name you call. The full entry prose for a released
version is in this file's git history, at the tag of the release that shipped it —
`git show v0.16.0:CHANGELOG.md`.

## 0.18.0 — 2026-09-09 — "declarations that mint the types they constrain, and rules that forward-chain only when asked"

- **Assertive argument types are on by default: an `arg` / `genlArg` / `interArg`
  declaration now mints the type it constrains, not only tests for it.** The entailment
  shipped in 0.17.0 behind `VAELII_ASSERTIVE_ARG_TYPES`, off by default; it is now the
  default reading. A declaration and a fact together mint a derived, justified, retractable
  membership (`arg`) or `genl` edge (`genlArg`), so a KB holds — and `isa?` / `types-of`
  and the definitional checks read — types the constraint-only reading leaves to a prover's
  on-demand answer (docs/argtypes.md). The starter load ships more stored sentexes as a
  result, and a caller counting them, or reading a type it did not assert, sees the minted
  content.

  Loading the shipped ontology under the entailment surfaced one ill-formed mint: the
  meta-declarations `(genlArg arg 3 thing)` / `(genlArg genlArg 3 thing)` would draw
  `(genl thing thing)` from every `(arg P n thing)` declaration, a reflexive edge `wff`
  refuses. `arg-entailments` now never mints a reflexive `(genl t t)`, so the shipped KB
  loads with a clean violations ledger. *Class:* **Breaking** (the default reading changes
  what a KB contains). *Migration:* `VAELII_ASSERTIVE_ARG_TYPES=0` restores the
  constraint-only default. *Breaks:* `VAELII_ASSERTIVE_ARG_TYPES`.

- **A bare `implies` rule defaults to `:backward`, and `set/forwardRule` now means
  forward and backward.** Forward chaining materializes a conclusion per match, which is
  intractable on a large KB, so a rule forward-chains only where its author asks. A rule
  asserted bare — no `set/*Rule` wrapper and no `:direction` — ran forward and backward
  before (`:both`); a bare rule now backchains only and materializes nothing.
  `set/forwardRule` adds forward chaining to the backward use rather than replacing it: a
  rule wrapped `set/forwardRule` answers backward goals as well as forward-chaining, where
  the wrapper made the rule forward-only before. `rules/backward?` reads `:forward` and
  `:both` as one class, so `{:direction :forward}` and `set/forwardRule` name the same
  forward-and-backward rule. The old forward-only reading moves to a fourth direction,
  `set/forwardOnlyRule` / `:direction :forward-only`, which forward-chains but never
  answers a backward goal — a mode the shipped ontology does not use. A generator, a rule
  concluding a rule, defaults to `:forward` even when bare, because a generator stamps a
  rule by firing forward and no backward goal asks for a rule; the shipped ontology's
  forward-materializing meta-rules and bounded theories carry `set/forwardRule`
  explicitly, so no shipped content changes what it derives. *Class:* **Breaking** (a
  documented default, and the meaning of the `set/forwardRule` wrapper). *Migration:* to
  restore forward materialization of a bare rule, wrap it `set/forwardRule` or assert it
  with `:direction :forward` (or `:both`); to restore the old forward-only reading of
  `set/forwardRule`, rewrite it to `set/forwardOnlyRule` or `:direction :forward-only`.
  [docs/inference.md](docs/inference.md), [docs/generators.md](docs/generators.md)

  *Breaks:* `(implies` asserted bare, `set/forwardRule`

- **A variable-arity application shorter than its relation's declared `arityMin` is now
  refused at the arity check.** 0.17.0 shipped `arityMin` deriving the
  `at_least_*_relation` classifications, but no well-formedness reader consumed the
  declaration, so a variable-arity relation was exempt from the arity check at every
  length. `checks/arity-problem` now reads `arityMin` on the variable-arity branch through
  `provers/arity-min` and convicts an application below the minimum, reporting an `:arity`
  violation carrying `:minimum? true` with the message "`P` takes at least `n` arguments
  but has `m`". A relation with no `arityMin`, or with two visible minima that disagree,
  keeps the outright exemption; the floor lands at assert only, so a late `arityMin` does
  not re-file the too-short applications stored before it. The same commit gives
  `admitsArgnum` a runtime reader: `AdmitsArgnumProver` answers `(admitsArgnum R n)` for a
  ground relation and position from `R`'s declared arity and variable-arity mark —
  provable for every position of a variable-arity relation, provable up to the declared
  arity of a fixed one, and unprovable where the KB declares neither — replacing the inert
  record 0.17.0 shipped. `provers/admits-position?` is the one decision the prover and
  `checks/arg-position-problem` both read, so the position query and the argument-position
  refusal cannot answer one position two ways. *Class:* **Refusal** (a too-short
  variable-arity application, which no well-formed caller relied on storing). *Migration:*
  extend a refused application to the relation's `arityMin`, or correct the `arityMin`
  declaration. [docs/predicates.md](docs/predicates.md), [docs/argtypes.md](docs/argtypes.md)

  *Breaks:* `arityMin`, `(lessThan`, `(greaterThan`, `(termsRelated`, `(functionCorrespondingPredicate`

- **`intersection` names the kind that is the overlap of others, and an asserted
  intersection fact derives the taxonomy edges.** `(intersection ?combined ?type1 ?type2 …)`
  declares `?combined` as definitionally the intersection of the listed types: a thing is
  a `?combined` exactly when it is each type. `intersection` is a `variable_arity_predicate`
  with `(arityMin intersection 3)` — the combined kind plus at least two types — and
  carries `(genlArg intersection 1 thing)` and `(genlArg intersection 2 thing)` on its kind
  positions; `(termsRelated disjoint intersection)` records `intersection` as the
  definitional twin of `disjoint`. Two CxCore rules fire on an asserted fact at binary and
  ternary arity: forward `intersection`→`genl` rules materialize `(genl ?combined ?typeN)`
  for each type, so the taxonomy closure and `ask?` / `ask` read the derived edge, and a
  membership generator stamps one concrete-functor rule per fact concluding `(?combined ?x)`
  from `(and (?type1 ?x) (?type2 ?x) …)`. General arity above ternary awaits the
  list-membership vocabulary. A one-type `(intersection C T)` is refused at the assert
  entry point with `:type :arity` and stores nothing, since the intersection of a single
  type is that type. CxCore now ships a rule whose consequent predicate is `genl`, so the
  `/levels` report for a `genl` goal names a `:rules` method beside the closure rather than
  the closure alone; the derived `genl` answer is unchanged. No shipped KB asserts an
  intersection fact, so the starter load is unchanged. *Class:* **Additive**.
  [docs/taxonomy.md](docs/taxonomy.md)

- **A state-of-affairs and causality cluster joins the upper ontology in CxAbstract.**
  Seven collections are added: `situation` (`genl temporal_thing`), with the
  specializations `static_situation` (a state that holds unchanged) and `event` (an
  occurrence whose state changes); `causal` and `acausal`, dividing `thing` by whether a
  thing can occupy a cause slot; and `causal_event` and `acausal_event`, defined through
  `intersection` — `(intersection causal_event causal event)` and
  `(intersection acausal_event acausal event)` — so the CxCore intersection rules derive
  their `genl` edges and membership rather than restating them. Two disjointness
  declarations partition the divisions: `(disjoint static_situation event)` and
  `(disjoint causal acausal)`. The `genl` closure of disjointness carries
  `(disjoint causal acausal)` down to the intersection-defined kinds, so `causal_event` and
  `acausal_event` read `:disjoint` without a separate declaration, and a term asserted
  `causal` and then `acausal` is refused at the assert entry point as a contradiction.
  *Class:* **Additive**. [docs/taxonomy.md](docs/taxonomy.md)

- **`(bravely S)` and `(cautiously S)` read the brave and cautious status of a labeling
  dilemma as a query that commits nothing.** A coexisting `P` / `¬P` dilemma leaves both
  sides believed, and an ordinary `ask` cannot separate the forced belief from the
  arbitrary one. `(cautiously S)` holds when `S` is in every optimal labeling and
  `(bravely S)` when `S` is in some — the classification `do/labeling` draws. The query
  delivers that classification on the read path: after asking, belief, `contradictions`
  and `last-program` are unchanged, where `do/labeling` commits a labeling. The
  `:brave-cautious` reasoner answers both, added opt-in with
  `(add-reasoner kb :brave-cautious)` and resolved lazily so the ASP stack stays off a
  KB's load path. `bravely` and `cautiously` are computed, not assertible — the assert
  entry point, the special table and `wff` refuse a stored one, as they refuse `unknown`
  and the aggregates — and each takes a ground `S`. A `bravely` or `cautiously` antecedent
  carries no support, so the forward join drops it: the pair is a read, not a premise
  belief rests on. *Class:* **Additive**. [docs/labeling.md](docs/labeling.md),
  [docs/naming.md](docs/naming.md)

- **`asp/atMost` / `asp/atLeast` state a cardinality bound over choice heads, and ground
  to one solver cardinality atom per group.** `functional P` bounds a choice predicate at
  one value per subject, but a bound past one had no construct, and a hand-written
  at-most-`k` grounds one hard constraint per `(k+1)`-subset of the contending heads —
  `C(n, k+1)` of them. `(asp/atMost k ?v pattern)` and `(asp/atLeast k ?v pattern)` state
  the bound directly, with `asp/softAtMost` / `asp/softAtLeast` as soft twins that penalize
  a breach once rather than excluding the model. The surface mirrors `agg/count`'s
  projection: `?v` is the counted variable and the pattern's other variables are the group,
  so a bound with no other variable is one global bound over every ground head, and a bound
  with a free group variable is one bound per group. `rules/normalize-cardinality` rewrites
  the surface to a constraint rule carrying a `cardAtMost` / `cardAtLeast` marker,
  `solve-context` matches the pattern against the ground choice heads and emits one
  `:cardinalities` entry per group, and `edge/translate` renders each as a single ASPIF
  weight-body statement, so a cap of 10 over 30 heads is one constraint rather than
  `C(30, 11)`. A cardinality bound is a solver atom that prunes inside the search, unlike
  `agg/count`, which is a census over believed facts computed outside any solve and counts
  a never-believed choice head as zero. Each head weighs one; a weighted `#sum` variant is
  unbuilt. A malformed bound is refused with `:not-well-formed`, and `check` reports that
  refusal rather than throwing; a global `asp/atLeast` whose predicate grounds to no head
  is infeasible rather than silently unbounded. *Class:* **Additive**.
  [docs/solving.md](docs/solving.md), [docs/asp.md](docs/asp.md)

- **`subsumption-status`, `subsumption-statuses` and `disjointness-audit` classify every
  type pair and name both the missing `disjoint` assertions and the contradictions.**
  `(subsumption-statuses kb a b)` returns the set of applicable relationships between types
  `a` and `b`, any subset of `#{:genl :spec :coextensional :disjoint :orthogonal}`: `:genl`
  when `(genl a b)` holds, `:spec` for the converse, `:coextensional` when each is `genl`
  the other, `:disjoint` when a `disjoint` declaration or the taxonomy proves no shared
  instance, and `:orthogonal` when neither subsumes the other yet a shared instance is
  provable. `(subsumption-status kb a b)` reduces the set to one keyword: a singleton
  returns that status, an empty set returns `:unknown`, and two or more return
  `:inconsistent` — a pair asserted both `genl`-related and `disjoint`, a contradiction
  rather than a precedence resolved silently. `genl?` and `disjoint?` read the global
  cached closures; the `:orthogonal` witness, a member of `a` that is also a member of `b`,
  is read from an optional vantage `context` (default `CxUniverse`) as a facts-only query
  (`{:max-depth 0}`), so the status is the same under every query engine.
  `(disjointness-audit kb)` runs the classification over every unordered pair of distinct
  types and returns
  `{:types n :pairs n :by-status {status count} :pairs-data [{:a t :b t :status s} …]}`; a
  caller takes `:by-status` for the census, filters `:pairs-data` on `:status :unknown` for
  the candidate missing-`disjoint` pairs, and on `:status :inconsistent` for the pairs a KB
  asserts both ways. Each function takes an optional trailing `context`. A `:coextensional`
  relationship needs a `genl` cycle, which `wff` refuses at assertion, so it appears only
  from a belief-state cycle or an equality merge. *Class:* **Additive**.
  [docs/api.md](docs/api.md), [docs/taxonomy.md](docs/taxonomy.md)

- **`args` / `argsGenl` / `argAndRest` / `argAndRestGenl` type a whole variable-arity tail
  in one declaration.** Where `(arg P n T)` types one numbered position, `(args P T)` types
  every accepted position of `P` as an instance of `T`, so a variable-arity relation whose
  tail repeats one role is typed without naming a largest finite position. `argsGenl` is
  the subtype reading: `(argsGenl P T)` types every position as a subtype of `T`, standing
  to `genlArg` as `args` stands to `arg`. `(argAndRest P n T)` and `(argAndRestGenl P n T)`
  type position `n` and every later one and exclude the prefix below `n`, so `(args P T)`
  states what `(argAndRest P 1 T)` states. `args` and `argsGenl` are `binary_predicate`s
  typed `(arg _ 1 relation)` and `(genlArg _ 2 thing)`; `argAndRest` and `argAndRestGenl`
  are `ternary_predicate`s that add `(arg _ 2 positive_integer)`. Each is `enforced` in
  family `:argument-constraint` with facets `#{:convicts :answers}`, checked by
  `checks/covering-args-problem` for the instance forms and `checks/covering-genls-problem`
  for the subtype forms, and answered up the `genl` closure by `MetaConstraintProver`.
  Three properties hold, each of them `arg`'s: a covering constraint composes conjunctively
  with a position-specific `(arg P n T)`, both binding the slot; a super-predicate's
  covering constraint binds a sub-predicate's tuples through the shared declaration reader
  `res/constraining-predicates`; and the check is convict-only and open-world, refusing a
  tail value the KB places outside the type, passing an argument of unknown type, and
  minting nothing, so a covering declaration arriving after the facts convicts none of
  them. The check walks the positions a sentence has, guarded by `arity-problem`, so the
  arity reader and the covering check agree about where the tail ends. No shipped relation
  carries a covering constraint, so a KB without one adds nothing to the firing budget.
  *Class:* **Additive**. [docs/argtypes.md](docs/argtypes.md)

- **`query-status` runs the same search `query` runs and returns a report, so a truncated
  read is distinguishable from an unprovable one.** `query` with `:max-depth` returns the
  same empty or short sequence whether the goal is genuinely unprovable or the depth bound
  cut the search, so a bound set one too low returns "no" rather than "not deep enough".
  `query-status` runs the same search at the same depth and returns a map: `:answers` and
  `:count`, `:status` (`:complete` or `:truncated`), `:truncated?`, `:depth`,
  `:time-to-first-answer-ms`, `:total-time-ms`, and `:stats` (the node engine's
  `tree-stats`, present only where a depth sent the read to that engine). `:truncated?` is
  conservative: `true` means the depth bound stopped at least one rewrite the search would
  otherwise have taken, so the answers may be incomplete, and `false` guarantees the
  answers are every answer the KB entails at that depth; a facts-only read is never
  truncated. The probe stays off the plain `query` path, since `session` allocates the
  truncation flag only under `:track-truncation?`, which only `query-status` sets, so
  `query` is unchanged. `query-status` reports one search over one concrete context's
  frontier, so it takes `[kb goal context]` or `[kb goal context opts]` and refuses a
  variable or query context with `:unsupported-context`. *Class:* **Additive**.
  [docs/inference.md](docs/inference.md), [docs/api.md](docs/api.md)

- **`functional_at_instant` is the per-instant counterpart of `functional` for a value
  carried as a fluent: `(functional_at_instant F)` states that `F` has at most one value
  for one subject at a single instant.** `functional` enforces at-most-one-value over a
  predicate's bare literals, but a value carried under `initiates` never becomes a bare
  literal, so the equality closure never sees the pair.
  `vaelii.core/functional-at-instant-violations` reads the residual invariant on demand and
  returns the clashes of one declaration as a set of maps
  `{:function :subject :instant :values :kind}`, and
  `all-functional-at-instant-violations` sweeps every visible declaration into
  `{f #{violation…} …}`, omitting a declaration that clashes nowhere. `:kind` is `:merge`
  when the clashing values are all symbols, the pair `functional` would merge, and
  `:contradiction` otherwise, two numbers or strings `functional` refuses. The audit
  reports rather than merges, because whether two fluents overlap at an instant follows
  from the clipping closure and is not known when a fluent is asserted. `impl/fluent.clj`
  sits below `vaelii.core`, reading facts through `provers/ask` and the one `holdsAt` rule
  through `inference/solutions` at depth 4. CxTime ships
  `(unary_predicate functional_at_instant)`. *Class:* **Additive**.
  [docs/time.md](docs/time.md), [docs/equality.md](docs/equality.md)

- **`matchesPattern` is a computed string-shape predicate:
  `(matchesPattern ?string ?pattern)` holds when the whole of a ground `?string` matches
  the regular expression `?pattern`.** `EvaluableProver` answers it, extending the
  evaluable set from `lessThan` / `greaterThan` / `integer` to a fourth member. Both
  arguments are `quotedArg` strings, and a non-string subject yields no solution, so the
  shape test alone defines a string subtype —
  `(defnSufficient dotted_quad (matchesPattern ?x "\\d+\\.\\d+\\.\\d+\\.\\d+"))` carries no
  separate `(string ?x)` conjunct, which the registry does not evaluate. The match runs
  through a step-limited `CharSequence` capped at 1,000,000 characters, so a pattern that
  would backtrack past the budget raises a `:pattern-too-costly` refusal at query time
  rather than running unbounded. A ground pattern the regex engine cannot compile is
  refused at the assert entry point as `:bad-pattern`, rather than a goal that never
  matches and reports no error. CxCore ships `(binary_predicate matchesPattern)` and the
  two `quotedArg` string declarations. *Class:* **Additive**. [docs/defns.md](docs/defns.md)

- **An interrupted `:one` label solve returns its best model instead of no answer.** An
  optimising `do/label … :one` over many equal-cost optima finds an optimum in
  milliseconds but proves it slowly, so the solve can reach the time limit
  (`VAELII_ASP_TIME_LIMIT`) mid-proof. Both backends reported `:interrupted` and the
  imperative reader `edge/kept-of` discarded the model already in hand, so the caller
  received no labeling for a solve that had a valid one. The clingo and clasp `:label`
  modes now solve with `--opt-mode=opt` and no model cap, streaming each improving model,
  so a cancelled search keeps its lowest-cost one; a run cut off after finding a model
  reports the new status `:best-effort` — a model found, optimality unproven — rather than
  `:interrupted`. `edge/kept-of` reads a `:best-effort` result as an answer, and the
  `do/label` `:one` / `:sat` result map carries `:best-effort? true` when the returned
  labeling is one whose optimality went unproven. The belief path `edge-solver` still
  treats `:best-effort` as undecided, so a wall clock never moves belief and order
  independence holds. *Class:* **Fix**. *Migration:* a caller that ignores the new key
  reads a valid labeling where it read none; a caller that needs a proven optimum tests
  `:best-effort?` and rejects it. [docs/asp.md](docs/asp.md), [docs/labeling.md](docs/labeling.md)

- **`recover` requires a stored `genl`/`genlCx` declaration to carry the complete edge
  shape before it replays the edge.** 0.17.0's `replay-edge` guard required both endpoints
  to be symbols, but the rebuild arm reads the stored sentence positionally (`[_ a b]`), so
  two malformations an older or foreign writer could leave under the `genl`/`genlCx`
  functor root still passed. An over-arity row `(genl a b surplus)` replayed as
  `(genl a b)` with its surplus term dropped, and a wrong-functor row such as
  `(disjoint a b)` handed up under the `genl` root replayed as `(genl a b)`. Both rows
  carry symbols in both endpoint positions, so neither crashed and both fabricated a
  spurious edge. `replay-edge` now activates an edge only when the stored sentence is
  exactly `(<functor> <symbol> <symbol>)` — arity three, the literal expected functor, both
  endpoints symbols — and otherwise skips the declaration and counts it, logged once at
  `:warn`, the discipline the 0.17.0 fix drew for the two-element crash. No well-formed
  store holds such a declaration, so a store the current entry point wrote replays
  unchanged. *Class:* **Fix**. *Migration:* none.
  [docs/storage.md](docs/storage.md#persistence--recovery)

- **The web term search matches a name case-insensitively.** The `/find?q=` handler pinned
  `:case-sensitive? true` on its `find-terms` call, so a lowercase query matched no
  camelCase term even though `find-terms` itself defaults to case-insensitive. The handler
  now passes `:case-sensitive? false`, so a literal query matches a term of any case and
  `parentof` finds `parentOf`. A regex query carries its own case in the pattern and
  requests insensitivity with `(?i)`, which the regex matcher already honours, so a regex
  query is unchanged. *Class:* **Fix**. *Migration:* none. [docs/web.md](docs/web.md)

## 0.17.0 — 2026-09-06 — "arity as vocabulary over every relation, and declarations that stop restating their own conclusions"

**14 entries** — 1 Breaking, 4 Refusal, 4 Additive, 5 Fix. A declaration that restates
what the taxonomy already concludes turns that conclusion into a precondition, so the
arrival order of two assertions decides which facts a KB holds. Four entries retire such a
declaration — on `genl`, on fifteen unary marks, on six arity marks, and in the `predAll`
pair's third argument — and the arity vocabulary underneath is rebuilt so `relation` is
the common parent of `predicate` and `function` and every relation lands in exactly one
arity policy. `predAllSpecified` and `predSpecifiedAll` go binary and derive the filler
type from the predicate's own slot contract. Three composite function marks — `injection`,
`surjection` and `bijection` — arrive as one declaration each, a `genlCx` edge's merge
sweep stops growing with the KB, and a late `symmetric` declaration folds a mirrored pair
no earlier version could fold.

*Breaks:* `(predAllSpecified`, `(predSpecifiedAll`, `specified-violations`,
`all-specified-violations`, `(binary_predicate P)` beside `(variable_arity P)`,
`:arg-type`, `*assertive-arg-types?*`, `VAELII_ASSERTIVE_ARG_TYPES`,
`(genlArg genl 1 thing)`, `(arg symmetric 1 predicate)`, `(arg functional 1 predicate)`

## 0.16.0 — 2026-09-04 — "the predAll quantifier family, refusals that name their kind, and declarations that reach back"

**18 entries** — 3 Breaking, 1 Refusal, 7 Additive, 7 Fix. The `predAll` quantifier
family lands in all eight cells. Three refusals stop answering with the wrong keyword:
an unpinned indeterminate term is not provably `different` from anything, a missing
adapter is not an unknown backend, and a wrong operand count is not an unknown option.
Declarations arriving after the facts now reach them — a `(symmetric P)` mark folds
records already stored, a computed `genlCx` edge runs the reconcilers a stated one runs,
and `quotedArg` is answered along the `genl` closure. Every refusal declares what its
`ex-data` carries, and a throw that drops a key fails the build.

*Breaks:* `(different`, `indeterminate_term`, `:unknown-backend`, `:sqlite`, `:pg`,
`:unknown-option`, `:not-stratified`

## 0.15.0 — 2026-09-01 — "definitions that compute, and two renames"

**7 entries** — 2 Breaking, 5 Additive. Definitional membership is answered at query
time rather than only by a forward rule. Two renames: the sentex polarity slot is
`:polarity`, and the `AtomicSentex` record is `LiteralSentex`. A unary predicate is
snake_case and `assert` enforces the spelling in both directions, which retired the
camelCase marks. CxCore names the expression kinds and gains a curation vocabulary.

*Breaks:* `unaryPredicate`, `reifiableFunction`, `abduciblePredicate`,
`closedExtentPredicate`, `disjointMetatype`, `siblingDisjoint`, `warmBlooded`, `:truth`

## 0.14.0 — 2026-08-29 — "the index image as a backend, and the heap it stops paying"

**10 entries** — 1 Refusal, 1 Additive, 5 Fix. The mapped index image becomes a backend
of its own, `:disk-snapshot`, rather than a property of the disk store, and stops
carrying the argument roots into heap. The disk store's live-handle sets become
compressed bitmaps. The writer refreshes a drifted image mid-life and can be told not
to. A `functionalInArg` declaration arriving after the facts it convicts is reported
rather than silently late. Neither adapter shipped at this version; both stayed at
0.13.0.

*Breaks:* `vaelii.index.snapshot`, `:argument-family-ceiling`

## 0.13.0 — 2026-08-25 — "calendar time, joined queries, and the entry points that refuse"

**93 entries** — 5 Breaking, 12 Refusal, 32 Additive, 22 Fix. The largest release:
calendar time, joined queries and a sweep through the entry points that refuse.
`CxChange` ships an event calculus, calendar constructors give a date its own endpoints
so it orders itself, and a metric constraint narrows an interval relation. `or` is
accepted in a rule antecedent, stored as one rule per alternative, and refused as a
goal. Every search entry point takes a bound and the daemon holds them to its ceiling.
Twelve refusals close inputs whose acceptance stored junk, and the `:disk` and
`:pg-disk` pairings are renamed to say that both halves are out of core.

*Breaks:* `:disk`, `:pg-disk`, `VAELII_TEST_BACKEND=disk`, `edit!`,
`edit-with-consequences!`, `apply-proposal!`, `contexts`, `count-in-context`,
`contextDenotingFunction`, `lein cli load`, `prove`, `provable?`, `query`, `argue`,
`forward-chain`, `ask`, `ask?`, `query-plan`, `abduce`, `sentexes-matching`,
`handle-of`, `assert`, `load-text!`, `lein cli assert`, `unaryPredicate`,
`binaryPredicate`, `ternaryPredicate`, `/kbs`, `lein serve --listen <flag>`,
`vaelii.client/client`, `:timeout-ms`, `:token`, `dereference`, `resolve-by-locator`,
`set-trust!`, `trust-of`, `display-name-of`

## 0.12.0 — 2026-08-23 — "query contexts, bulk loading, and a literal's type"

**99 entries** — 3 Breaking, 3 Refusal, 7 Additive, 5 Fix. Query contexts, bulk loading,
and a literal's type. `resultIsa` and `resultGenl` become `result` and `genlResult`; the
four function marks classify what they mark, and the reifiability criterion is written
down. A records read stays lazy, and a proof's witness is one of its bindings. Three
reads that could not answer the question stop answering empty. First release of the two
adapters, `com.vaelii/postgres` and `com.vaelii/sqlite`, each at this version.

*Breaks:* `resultIsa`, `resultGenl`, `reifiableFunction`, `unreifiableFunction`,
`quotingFunction`, `contextDenotingFunction`, `ist`, `:proof?`, `?ctx`,
`qualitative-network`, `possible-relations`, `:arg-type`, `:quoted-arg-type`, `result`,
`genlResult`, `:arg-genl`, `character_string`, `:pg-disk`, `:dir`,
`:stale-index-records`, `register-modal-predicate!`

## 0.11.0 — 2026-08-22 — "contradiction solving, arrival order, and the durable log"

**67 entries** — 2 Breaking, 4 Additive. Contradiction solving, arrival order, and the
durable log. `antiTransitive` convicts the chain it forbids rather than being declared
and deferred. Definitional collection relations tie membership to a defining condition,
and sibling disjointness lets a collection's specializations separate themselves, with
an escape hatch for a pair that must overlap. A computed predicate or function is
registered in one line.

## 0.10.0 — 2026-08-20 — "more than one agent over one knowledge base"

**9 entries** — 4 Additive. Koinii: several agents coordinate over one shared knowledge
base, with belief projection for what each agent holds true. A context can be a reified
function application whose `genlCx` edges compute themselves. Mention-opacity arrives —
a quoting function reads its argument by spelling — and `quotedArg` types an argument
against a syntactic type. The `argIsa`, `argGenl` and `interArgIsa` spellings become
`arg`, `genlArg` and `interArg`.

## 0.9.0 — 2026-08-17 — "the truth-maintenance network defaults to dense"

**15 entries** — 5 Breaking, 8 Additive. The dense truth-maintenance network becomes the
default and gives a concurrent reader a consistent view. Four relation properties are
enforced rather than documented. A subsumption rests on its strongest route rather than
its shortest. An algebraic property becomes one predicate instead of a mark and a twin,
which retired the `...Predicate` spellings.

*Breaks:* `defeat-class`

## 0.8.0 — 2026-08-14 — "predicates inherit down the hierarchy"

**50 entries** — 1 Breaking, 1 Additive. Predicates inherit down the hierarchy. A KB
whose declared hazards are unresolved refuses writes rather than accepting them
unchecked, and a derived record's teardown is refused where belief was never built.
`check` and `check-edit` answer for the entry point they mirror. Five refusals close
recovery paths that believed records the store did not hold.

*Breaks:* `:unrecovered-kb`, `write-hazards`, `note-hazards!`, `contradictions`,
`violations`, `:constraint-exposure`

## 0.7.0 — 2026-08-12 — "contexts get one spelling"

**2 entries.** Contexts get one spelling. A context name is `Cx`-prefixed rather than
`Context`-suffixed, and the context-transitivity predicate is `genlCx`.

## 0.6.0 — 2026-08-12 — "stored rules become first-class"

**22 entries** — 2 Breaking, 4 Refusal, 2 Additive. Stored rules become first-class: a
rule can conclude a rule, and a rule carries a handle, TMS support and retraction with
no rule-specific machinery. A capability claim about a kind is `capabilityType` and
about a member is `hasCapability`. A NAF guard written as a conjunction now guards, and
the strictest policy stops being the leakiest.

## 0.5.1 — 2026-08-11 — "faster writes, more to watch"

**15 entries.** Faster writes, more to watch. A settle pays for the region it moved
rather than for what the KB holds. The arbitrating half of a bounded pass says when its
budget stopped it. Four places where arrival order decided an answer are closed.

## 0.5.0 — 2026-08-07 — "operating the engine as a service"

**23 entries.** Operating the engine as a service. The daemon authenticates and refuses
to bind an address without a token. One space number names a KB's stores, `:space`,
replacing the separate record and index spellings. `context-size` becomes
`count-in-context`, `different` descends into compound arguments, and a name can carry a
sense and a lexeme.

*Breaks:* `:record-space`, `:index-space`, `docs/storage.md`

## 0.4.0 — 2026-08-05 — "correctness fixes against the invariants"

**33 entries.** Correctness fixes against the four invariants. A conjunctive query could
answer nothing while each of its conjuncts answered, and no longer does. `assert`
refuses a sentence that is not an s-expression, an `exceptWhen` query's literals are
held to the naming invariants, and an `edit!` batch key nothing reads is refused.

## 0.3.0 — 2026-08-04 — "a type on every refusal"

**29 entries.** A type on every refusal: every `ex-info` the engine throws carries a
`:type`, and the daemon's refusal keywords become plain. Both servers hold one
request-body ceiling, and the browser serializes its writes. An `ist` form must have
exactly three elements.

## 0.2.0 — 2026-08-03 — "the public API boundary, drawn"

**17 entries.** The public API boundary is drawn — six public namespaces, everything
else `vaelii.impl.*` and free to change. Every handle-taking function refuses a
non-handle. `close!` releases a durable KB's directory, an argument-constraint refusal
names its convicting declaration in content order, and the five sweeps start running in
CI.

## 0.1.0 — 2026-07-31 — "the first release"

The first public release.

## 2026-07-19 .. 2026-07-30 — the pre-release dailies

Twelve dated entries before versioning began, one per day of the initial build: the
whole stack on day one (2026-07-19), then order independence made an invariant, equality
and a sudoku solved, sound negation as failure, performance fixes and an operational
surface, denser storage measured first, OpenCyc in the engine's own format, reads scoped
to the asking context, aggregation over query results, the gate (lint, suite and
scaling), one entry point for backward chaining, and declarations that re-check what
they change (2026-07-30).

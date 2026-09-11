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

## 0.18.1 — 2026-09-11 — "a typed bound at every entry point, and an upper ontology divided by space and time"

- **Every bounded entry point refuses a value outside its domain by name, and the anytime
  budget roster splits into what `ask-within` reads and what `prove-within` reads.** A bound
  holding a value it cannot mean — a string `:max-ms`, a non-integer `:max-depth`, a non-fn
  `:on-progress`, a string `:believed?` — reaches arithmetic or a call and throws a bare
  `ClassCastException`, which the daemon answers `:internal-error` (a 500) where every sibling
  refusal is a typed 400. `prove` / `ask` / `query` / `why` / `find-terms` already refuse
  their caps; `prove-within`, `ask-within`, `search-tree`, `compare-tacticians`,
  `forward-chain`, `assert`, `assert-rule`, `abduce`, `kb-quality`, `export!`, `import!`,
  `clear-caches` and the extent readers now do too, reading the one shared domain table
  (`vaelii.impl.opts/bound-domains`). A bound of `0` stays a real question wherever it was
  one — no time, no rule expansion, realize nothing and resume, report at every opportunity.
  Beside the value gaps: `add-evaluatable` refuses a key off `#{:result :arity :cost
  :completeness}`; `set-cache-limit` warns and records a pin for an id no cache has registered
  yet rather than refusing it, since the register fills lazily; and `assert-rule` runs the
  unrecovered-KB gate before its range check, so an unrecovered KB answers `:unrecovered-kb`
  and not `:not-range-restricted`. The anytime roster splits the way `ask` and `prove` split
  theirs: `ask-within` reads `:max-ms` / `:max-results` / `:max-cost` and refuses a rule
  depth, `prove-within` reads the two clocks plus `:max-depth` / `:max-term-growth` and
  refuses `:max-cost`, and `resume` holds the union so a continuation of either passes.
  *Class:* **Refusal** (the two accepted-and-wrong boolean values answered at a setting nobody
  chose, and the bad numbers crashed the daemon). *Migration:* nothing for a caller whose
  bounds are numbers of the right kind; `(clear-caches kb {:counters? "yes"})` and an extent
  read with a string `:believed?` were both accepted as `true` and are now `:unknown-option`,
  so pass an actual boolean. [docs/api.md](docs/api.md), [docs/anytime.md](docs/anytime.md)

  *Breaks:* `:counters?`, `:believed?`, `:max-cost`, `:max-depth`, `:max-term-growth`, `add-evaluatable`

- **`assert-inert` refuses an open sentence and stores an `(ist Ctx S)` form as S in
  Ctx; `describe` refuses a `:limit`, and `why-not` a `:nearest`, that is not a count.**
  An inert `(dog ?x)` was a stored record a `CxEverything` read answered as a fact, and a
  stored sentence is closed (`checks/check-ground`, the refusal `assert` makes:
  `:not-ground`). An `(ist CxA S)` stored as written was a record with the `ist` functor,
  which `handle-of`, `contexts-of` and every read resolve past — reachable by its handle
  and by nothing else; it now stores S in CxA, as `assert` does, and a malformed one is
  `:shape`. `(describe kb t c {:limit 0})` answered every window empty under a `:total`
  that read as an answer, and `{:limit "5"}` reached `take` and threw a bare
  `ClassCastException`, which the daemon reports as `:internal-error`; both are
  `:unknown-option` now, as at `find-terms`. `(why-not kb s c {:nearest "3"})` read the
  value as no request and answered the plain `:not-stored`; a `:nearest` that is not a
  non-negative integer is `:unknown-option`, and `0` still asks for nothing.
  *Class:* **Refusal** (the stored records matched no query, and the accepted values
  answered nothing a caller asked for). *Migration:* nothing for a caller whose inert
  sentences are ground and whose caps are positive integers; a caller passing
  `{:limit 0}` to `describe` for the totals alone passes `1` and reads `:total`.
  [docs/api.md](docs/api.md), [docs/solving.md](docs/solving.md)

  *Breaks:* `assert-inert`, `describe`, `why-not`

- **The upper ontology gains a space/time division, a metatype-order ladder and an
  expression subtree, renames `spatial_thing` to `spatial` and `temporal_thing` to
  `temporal`, and adds a `CxUniverse` collector context for the cross-member disjoints.**
  CxCore roots the space/time divisions — `spatial` and `aspatial`, `temporal` and
  `atemporal` — and the `abstract` collection under `thing`, declares the complement
  disjoints `(disjoint spatial aspatial)` and `(disjoint temporal atemporal)` beside the
  cross-division `(disjoint intangible spatial)`, and re-roots `abstract` under
  `intangible`; the rename removes `temporal`'s only prior upward edge, so
  `(genl temporal thing)` restores it and `(disjoint physical_object intangible)` lands in
  CxAbstract. A metatype-order ladder — `metatype`, `meta_metatype`, `at_least_metatype`,
  `fixed_order_type`, `variable_order_type`, `type_type_by_order` — states the three-order
  partition and its subtype edges, and the inert predicates `genlInverse`, `typeGenl` and
  `partitionedByType` classify without an inference path. CxAbstract gains an `expression`
  subtree under `abstract` holding `context`, `formula`, `relation`, `relation_application`
  and `unrepresented_term`, and a substance division whose states are `solid`, `liquid`,
  `gas` and the added `plasma`, with `liquid` moved out of `stuff_type_by_substance`
  because a liquid is a state and not a material. The two `typeGenl` claims move from
  CxCore, which sees no member, to CxAbstract, which sees `substance` and the stuff
  metatypes, so a type-relating claim is written only in a context that sees the terms it
  names. A new top-level `CxUniverse.txt` collector context holds `(disjoint organization
  animal)`, a disjointness a single context sees both members of, and the starter loader
  now discovers and loads top-level `kb/Cx<Name>.txt` collector files after the upper and
  middle theories so the cross-member axiom is a live sentex. Three tests pin the shipped
  set: one refuses a type-relating claim whose context cannot see a term it names, one
  holds the six head-context terms kept there on purpose, and `ontology_test` pins the
  quality clash census at `{:negation 4, :disjoint 8}` (the remaining eight come from the
  integer-and-person checker, a stated limitation rather than real conflicts).
  *Class:* **Additive** (shipped ontology content, which takes no Breaking label however
  far it moves an answer). *Migration:* a KB that wrote `spatial_thing` or `temporal_thing`
  renames to `spatial` / `temporal`; the old spelling stores clean under open-world
  semantics but attaches to nothing in the taxonomy, so a spatial or temporal argument
  check does not admit it. [docs/contexts.md](docs/contexts.md),
  [docs/glossary.md](docs/glossary.md)

  *Breaks:* `spatial_thing`, `temporal_thing`

- **A process-wide cache profile scales every derived cache's count bound by one
  multiplier, tunable through `VAELII_CACHE_SCALE` and three new `vaelii.core`
  functions.** `caches/limit-of` is the one resolver every count-bounded cache reads, on
  both its store path and its `caches` reporting row, so the enforced bound and the
  reported bound are one number. It returns the shipped default at scale `1.0` with no
  override, and otherwise `default × scale` floored at 16 entries. `VAELII_CACHE_SCALE`
  (default `1.0`, a number at or above zero, read at load) sets the scale a process starts
  with and refuses a non-number or a negative value at engine load. `(set-cache-scale x)`
  multiplies every counted bound on a running process, `(set-cache-limit id n)` pins one
  cache's bound or clears the pin with `nil`, and `(cache-profile)` returns the profile in
  force as `{:scale m :overrides {id limit}}`; `set-cache-scale` and `set-cache-limit` each
  refuse a value they cannot mean with `:type :unknown-option`. The browser `/caches` page
  gains a scale form posting an origin-checked write beside the existing clear. At scale
  `1.0` with no override the resolver returns the shipped default unchanged, so the cost
  budgets and the perf gate read the same bounds as before. *Class:* **Additive** (three
  new public functions and one new configuration name; `test/golden/api-surface.edn` and
  `test/golden/config-surface.edn` move with them). [docs/caches.md](docs/caches.md),
  [docs/operations.md](docs/operations.md)

- **A memory-pressure guard shrinks the caches when the old generation fills after a
  collection and grows them back as it drains.** The guard adds a second multiplier,
  `:pressure`, to the cache profile, so a counted cache's bound becomes
  `default × scale × pressure` floored at 16 entries and a pinned cache's bound becomes
  `override × pressure`. A post-collection notification listener reads the old-generation
  used-over-max fraction after each garbage collection: at or above `0.85` it halves
  pressure and trims the counted caches to the lower bound, at or below `0.60` it raises
  pressure by half again while pressure is below `1.0`, and otherwise it holds. Pressure
  is clamped to `[0.125, 1.0]`, so a heap under sustained pressure keeps an eighth of each
  cache rather than emptying it. The trim keeps the earliest entries of a plain map and
  defers to a shape-aware cache's own recency order rather than clearing. The daemon and
  the browser install the guard at startup — the browser feeds it the live KBs through the
  catalog — and nothing attaches it at engine load, so a library embedding arms no
  listener. A JVM whose collectors emit no such notification, or that names no
  old-generation pool, holds pressure at `1.0`. `limit-of`'s docstring is corrected in the
  same batch to say a pin is scaled by pressure alone, not by the profile scale.
  *Class:* **Additive** (`install-memory-guard!` and the profile's `:pressure` field are
  new; the guard's functions stay in `vaelii.impl.caches` and the servers install them, so
  no public-API golden moves). [docs/caches.md](docs/caches.md)

- **A reified NAT or context constant is named by the SHA-256 of its expression, not a
  per-process counter, so the same expression reifies to the same constant across
  processes and rebuilds.** `constant-for` names a minted constant `nat/a<17 base62
  digits>`, or `cx/a…` for a context NAT, from the first 96 bits of the SHA-256 of the
  printed expression, where the prior scheme minted `nat/g<N>` from a process-local
  `gensym` counter. The base62 payload holds `[A-Za-z0-9]` only, because a reified constant
  sits in argument position and the naming check forbids the `-` and `_` a base64url
  payload would carry. The constant symbol is documented as opaque and never read back — a
  page and a remote reader are held to never show it, and belief never keys on it — so a
  caller resolving the constant through `term-expression` or `expand-expression` still
  reads the expression `(FruitFn AppleTree)` and observes no change. The content name
  extends the engine's order-independence property to the constant symbol itself: two
  processes that mint the same NAT now spell it identically, where the counter spelled it
  by allocation order and left the cross-process merge to the collision-repair path. A dump
  written by an earlier release keeps its `nat/g…` names, because dedup by the stored
  `termOfUnit` expression runs before any mint and re-reifying resolves to the existing
  constant. The skolem head-existential witnesses inherit the scheme through the same mint
  path, and a hash collision degrades only into the ordinary two-expressions-one-constant
  case the merge already reconciles by content. *Class:* **Fix** (the documented
  order-independence invariant and the opaque-constant contract both held; the constant
  symbol moves to match them). [docs/nat.md](docs/nat.md), [docs/skolem.md](docs/skolem.md)

- **`kb-quality` stops reporting a clash that no ground term can reach, when an antecedent
  `arg` declaration demands a type disjoint from the term the paired rule types.**
  `kb-quality`'s contradictions-in-waiting reading reports two rules whose consequents
  place one unified term in two disjoint types, a clash that could form if both rules fire
  for that term. A fourth rule-out reads each antecedent predicate's `arg` declarations up
  the predicate hierarchy — through the reader `assert` uses — and drops a pair when a
  declared argument type is disjoint from another type the two rules place the unified term
  in, because no ground term then satisfies both antecedents. The rule-out reads the two
  consequents beside the antecedents, since the demanding literal states nothing about its
  own argument's type and the demand lives on the paired rule's `arg` declaration. At least
  one side of a disjoint pair must be a declared argument type, so two stated unary-literal
  types that clash stay the clash the pair reports. The rule-out reads `arg` and not
  `genlArg` or the covering forms, because `genlArg` demands a subtype one stratum up and
  no shipped rule concludes a unary type from a `genlArg`-typed antecedent. The docstring
  and `docs/quality.md` already described the reading as one that reports a clash that could
  form, so the code moves to stop reporting the unreachable pairs; the shipped clash census
  drops the relation-classification false positives the upper-ontology additions
  introduced, leaving the eight integer-and-person residual pairs `ontology_test` pins.
  *Class:* **Fix**. [docs/quality.md](docs/quality.md)

- **`handle-of` and the sentence arity of `why-not` resolve a ground reifiable NAT to
  its stored constant, as `sentexes-matching` and `ist` do.** After
  `(ist kb C '(likes Rex (FruitFn Apple)))` stored `(likes Rex nat/…)`,
  `(handle-of kb '(likes Rex (FruitFn Apple)) C)` answered nil and `why-not` answered
  `:not-stored`, so `(retract! kb (handle-of kb s c))` — the composition the docstrings
  name — retracted nothing and reported `{:removed-sentexes 0}`. Both now run the
  read-mode reify (dedup, never mint) before the lookup. *Class:* **Fix**.
  [docs/nat.md](docs/nat.md), [docs/api.md](docs/api.md)

- **`provable?` and `ask?` refuse a non-map `opts` by name (`:unknown-option`), as
  `prove` and `ask` do.** `(provable? kb g c :oops)` threw a bare
  `IllegalArgumentException` out of the `seq` that picks the bounded arm; the roster
  check now runs first. The daemon pads its arguments to the option arity and answered
  `:bad-args` already, so only an in-process caller saw the difference. *Class:* **Fix**.
  [docs/api.md](docs/api.md)

- **`docs/api.md` matches the code for `reasoners`, `subsumption-status`, `contexts-of` and
  `has-prop?`.** The API reference is corrected in four places to state what the functions
  return. `reasoners` lists `:brave-cautious`, the ASP dilemma reader, beside the algebras.
  `subsumption-status` returns `:inconsistent` when two of the `genl` relationships hold at
  once, which the documented keyword set had omitted. `contexts-of` lists the contexts a
  sentence is stored and believed in, so a defeated sentex's context is not among them,
  where the line had said asserted. `has-prop?` recognizes six `:declares-*` prop kinds,
  adding `:declares-arg-and-rest-isa` and `:declares-arg-and-rest-genl`. *Class:* **Fix**
  (documentation only; the code already answered this way). [docs/api.md](docs/api.md)

- **`docs/solving.md` states that a constraint background literal and an `assumptionRule`
  antecedent ground over the registry leaf.** A constraint background literal and an
  `assumptionRule` antecedent reach `provers/solve-goal`, the registry leaf, so a stored
  fact, a backward rule, or a registered prover or evaluatable answers one, not only a
  believed fact, and a computed relation is a legal antecedent. The documentation had
  understated the reach. A new `solve_context_test` case pins that a constraint body reaches
  a prover. *Class:* **Fix**. [docs/solving.md](docs/solving.md)

- **The vocabulary load and the minting-assert path drop a redundant settle and two
  redundant declaration reads.** The CxCore and starter loaders wrap their bodies in
  `with-deferred-settle`, so the JTMS settles once at the end rather than once per asserted
  sentence, measured at roughly 200 ms off the starter load on the memory backend.
  `constraining-predicates` stops seeding an undeclared predicate — a mint's own type
  functor — into its result, dropping the per-assert match walk that returned nothing,
  measured at the CxCore load falling from 327 ms to 272 ms with assertive argument types
  on. The first-level materializer skips the definitional constraint re-check when the
  assert-path entailment check already ran it, threaded through a `pre-checked?` flag, while
  the deeper cascade levels and the retroactive sweeps still run the re-check;
  `assert_cost_test` re-pins the read counts down. `cascade-clash` builds the disjointness
  separation frame once and applies its closure per candidate, where it had rebuilt the
  frame inside a filter, and `perf`'s `disjoint-clique-membership` and
  `disjoint-metatype-membership` claims guard the result at linear in member count.
  *Class:* neither label — the prior path and the new one compute the same belief,
  justification set and stored-sentex fingerprint, so only the load and assert latency move.

- **The one-shot clingo solve injects its ground program through the `clingo_backend_*`
  accessors rather than writing an ASPIF text to a temp file, and the extracted batch
  loader backs a new incremental session API.** `do/label` and `do/classify` reach
  `clingo/solve` through `solve-context` and `solver/solve`, so the one-shot solve runs
  whenever a KB modification triggers an ASP labeling. `edge/translate` now returns its
  structured `:stmts` beside the ASPIF text, and `backend-batch!` interns each program atom
  as the symbol `a(<id>)` carrying its label, remaps every head and body literal through the
  vid→cid table, and emits the rules into a live backend — no temp file, no re-parse, no
  `#show` statement; a model's true atoms return through `clingo_model_symbols` and map back
  to labels through the symbol association the batch returns. `solver/solve` and
  `clingo/solve` now take the translated program map `{:aspif :stmts}`; AUTO routing still
  keys on the ASPIF byte length and clasp still consumes the rendered text. The extracted
  `backend-batch!` also backs a new session API in `vaelii.impl.asp.clingo` — `open-session`,
  `add-program!`, `declare-external!`, `assign-external!`, `solve-session`, `close-session!`
  — which grows a live control a batch at a time and toggles an external atom's truth between
  solves with no re-grounding; the session entry points have no production caller yet.
  *Class:* neither label — the one-shot path returns the same answer sets it returned through
  the temp file, so only the solve mechanism and the ~0.3 ms per-solve temp-file write move,
  and the session functions add no believed content. [docs/asp.md](docs/asp.md),
  [docs/solving.md](docs/solving.md)

- **A script renders the upper-ontology `genl` hierarchy to one SVG.**
  `scripts/ontology-graph.py` reads the `resources/kb/*.txt` authoring files and emits a
  layered is-a diagram — one node per type in the `genl` hierarchy, one edge per
  `(genl sub super)` — with node fill set by the context a term is defined in and edge color
  by the context the edge is written in, and it needs no KB boot. It draws through Graphviz
  `dot` when `dot` is on the path and falls back to a dependency-free layout otherwise.
  `--engine` selects among `dot`, `gridfold`, `icicle` and `dendrogram`, `--ratio` sets the
  sheet aspect, and `--text-scale` sets the label point size independently of `--ratio`.
  *Class:* **Additive**.

## 0.18.0 — 2026-09-09 — "declarations that mint the types they constrain, and rules that forward-chain only when asked"

**15 entries** — 2 Breaking, 1 Refusal, 9 Additive, 3 Fix. Assertive argument types become
the default reading: an `arg` / `genlArg` / `interArg` declaration mints the type it
constrains rather than only testing for it. A bare `implies` rule defaults to `:backward`
and materializes nothing, and `set/forwardRule` adds forward chaining to the backward use
rather than replacing it, so a rule forward-chains only where its author asks. The arity
vocabulary gains a runtime floor — a variable-arity application below its `arityMin` is
refused — and `admitsArgnum` answers a position query from the declared arity. New
declaration vocabulary types a whole variable-arity tail (`args`, `argsGenl`, `argAndRest`,
`argAndRestGenl`) and names an `intersection` kind that derives its taxonomy edges, and new
readers report the brave and cautious status of a labeling dilemma, a cardinality bound over
ASP choice heads, and the subsumption status of every type pair. A state-of-affairs and
causality cluster joins the upper ontology in CxAbstract.

*Breaks:* `VAELII_ASSERTIVE_ARG_TYPES`, `(implies` asserted bare, `set/forwardRule`,
`arityMin`, `(lessThan`, `(greaterThan`, `(termsRelated`, `(functionCorrespondingPredicate`

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

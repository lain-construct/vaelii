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

## 0.17.0 — 2026-09-06 — "arity as vocabulary over every relation, and declarations that stop restating their own conclusions"

**Not a drop-in upgrade from 0.16.0.** Five of the fourteen entries are labelled
**Breaking** or **Refusal**, and each carries its own `*Migration:*` line. One entry
changes a working caller: `predAllSpecified` and `predSpecifiedAll` are binary, and the
audit that reads them returns a `:status` map where it returned a bare set. The other
four withdraw or add a refusal, and one of those four fires only under the opt-in
`VAELII_ASSERTIVE_ARG_TYPES` toggle, which is off by default.

The release has one subject. A declaration that restates what the taxonomy already
concludes turns that conclusion into a precondition, and the arrival order of two
assertions then decides which facts a KB holds. Four entries retire such a declaration —
on `genl`, on fifteen unary marks, on six arity marks, and in the `predAll` pair's third
argument — and the arity vocabulary underneath them is rebuilt so `relation` is the
common parent of `predicate` and `function` and every relation is classified in exactly
one arity policy. The starter ships 1,600+ asserted / 3,200+ stored, the core vocabulary
850+.

- **`predAllSpecified` and `predSpecifiedAll` go binary: the filler type derives from
  the predicate's own slot contract.** The ternary forms restated in a third argument
  what `(arg P 2 R)` / `(genlArg P 2 R)` already say, and a restated type can disagree
  with the contract it copies — a second type system inside one declaration. The
  declarations are now `(predAllSpecified P D)` and `(predSpecifiedAll P R)`; the audit
  derives the filler constraints from the visible slot typing of the predicate **and
  every super-predicate whose declarations bind its tuples** — the same
  `constraining-predicates` union the assert-time checker reads — with `arg` →
  membership, `genlArg` → subtype through the reflexive `genl` closure, and a
  `type_relation_predicate` membership requiring the filler to be visibly a type at
  every position, composed conjunctively as the checker composes them. A declaration
  over a predicate with **no** visible denotation typing is reported as an explicit
  `{:status :gap :gap :missing-slot-typing}` declaration-contract diagnostic, never
  silently audited unconstrained, and a stored pre-migration ternary sentex — which
  the bulk import path can carry past the assert-time refusal — surfaces from the
  sweep as `{:gap :legacy-ternary-declaration}` rather than silently vanishing.
  `specified-violations` accordingly returns `{:status :audited :violations #{…}}` or
  `{:status :gap …}` — discriminate on `:status`, not key presence — drops its `dep`
  parameter, and refuses a non-`:second`/`:first` `arg-pos` with a typed `:bad-args`
  naming the removed-dep migration (the shape an unmigrated caller's context symbol
  lands in); `all-specified-violations` keys by `[functor pred indep]` — a legacy
  ternary gap by its whole stale tuple `[functor pred a b]`, so it displaces neither
  the migrated declaration it shares a prefix with nor another stale sentex over the
  same predicate — and always carries gaps, so an empty map remains a clean sweep a
  gap cannot fake. The
  function-mark rules thin to one antecedent each — totality reads only `(arg P 1 D)`,
  ontoness only `(arg P 2 R)`. New vocabulary `arg1` / `arg2` / `arg3` — binary
  projections of `arg`, bridged by rules in both directions and held to `arg`'s own
  declaration checks at the projected position, so neither spelling launders a
  declaration the other refuses — lets a positional constraint stand in a binary
  declaration's subject position, `(predAllSpecified arg1 predicate)` being the
  founding use.  The pair is wired as `arity` and the predicate-type memberships are:
  six rules deriving each other, one shared refusal path, both spellings `enforced`
  with `#{:convicts :reach}`, and `:family` left nil, `mark-families` rostering the
  lanes that must recognize one spelling set rather than every pair of spellings.
  The projections relate stored declarations only, generalized and
  inherited readings staying `arg`'s. *Class:* **Breaking** (declaration arity and
  audit return shape). *Migration:* rewrite `(predAllSpecified P D R)` to
  `(predAllSpecified P D)` and `(predSpecifiedAll P D R)` to `(predSpecifiedAll P R)`,
  ensure the audited slot carries its `arg`/`genlArg` typing, and read
  `(:violations result)` under a `:status` check where a bare set was read before.
  [docs/predall.md](docs/predall.md), [docs/taxonomy.md](docs/taxonomy.md)

  *Breaks:* `(predAllSpecified`, `(predSpecifiedAll`, `specified-violations`,
  `all-specified-violations`

- **Arity policy is vocabulary over every relation.** `relation` is now the common
  parent of `predicate` and `function`. Unsuffixed `unary` / `binary` / `ternary` are
  the relation-wide exact classes, with predicate and function specializations;
  `relationTypeByArity` owns their shared numeric mapping, and its two generators run the
  cycle both ways: `(arity R 2)` and `(binary R)` derive each other, well-founded, so
  retracting whichever was asserted collapses both. The cycle stops at the relation-wide
  class because `arity` covers functions — concluding `(binary_predicate R)` would make
  every shipped binary function a predicate. Exact `arity` is fixed-only,
  while `arityMin` states a variable relation's lower bound and derives the generic
  `at_least_binary_relation` / `at_least_ternary_relation` floors. `fixed_arity` and
  `variable_arity` are disjoint, and every shipped relation is classified in exactly
  one. `admitsArgnum` remains documentary. The vocabulary takes CxCore to 978 sentexes
  and the starter to 3,280 stored — the figures this release ships, and what the floors
  above are measured against — so `docs/kbs.md`'s core row and
  `core_context_test`'s band now read 850+.

  An exact predicate type beside `variable_arity` is refused as a result, `(disjoint
  fixed_arity variable_arity)` closing under the `genl` edges that put `unary_predicate`
  and its peers below `fixed_arity`. CxCore itself shipped that pair for `lessThan`,
  `greaterThan`, `termsRelated` and `functionCorrespondingPredicate`, and the four now
  carry `variable_arity_predicate` with an `arityMin` floor instead. The refusal is
  `:disjoint` whichever of the two is written first: the policy classes declare their
  one argument position on `fixed_arity` and `variable_arity` alone, because a narrower
  `(arg fixed_arity_predicate 1 predicate)` below them convicts a relation whose only
  stated type is `variable_arity` for its argument's type rather than for the policy it
  contradicts. *Class:* **Refusal**. *Migration:* a KB declaring both an exact predicate
  type and `variable_arity` for one predicate replaces the exact type with `arityMin`;
  the arity check reads `variable_arity` and exempts the predicate exactly as before,
  and `arityMin` is documentary, so nothing else changes.
  [docs/taxonomy.md](docs/taxonomy.md#relations-and-arity-policy)

  *Breaks:* `(binary_predicate P)` beside `(variable_arity P)`

- **Assertive argument types read one declaration one way, and the cascade closes.**
  With `*assertive-arg-types?*` on, `args-problem`'s **symbol arm yields** to the
  entailment that reads the same declaration: `(arg parentOf 1 animal)` read as an
  entailment says Fred *is* an animal, so there is no state of the KB in which Fred
  fills the slot and fails it. Running both readings at once was what stopped the
  cascade — a minted `(t1 Fred)` re-entered the check, `t1`'s own declaration convicted
  it for Fred not yet being a `t2`, and the conclusion `(t2 Fred)` would have been drawn
  from was dropped — so the entailment cascaded only for an argument holding **no** type
  at all, and one unrelated membership, or a unary triggering sentence typing its own
  argument, was enough to stop it after the first link. A `(p1 Fred)` under
  `(arg p1 1 p2)` was refused when re-asserted, by the membership it had itself created.
  Values, function applications and inherited declarations still convict: no mint can
  answer a value's syntax, a function's declared `result`, or a declaration that
  constrains a descendant context without minting there. What refuses in the symbol
  arm's place is the **consequence**: `checks/entailment-check` walks the whole cascade
  of prospective mints before anything is stored and refuses the assert with the first
  mint's own violation, so the entry point refuses a sentence exactly when it would
  refuse what the sentence entails. Two arms, because a clash has two shapes —
  `disjoint-problems` names an opposing handle and so reads clashes against stored
  memberships, and `cascade-clash` reads the pair the cascade supplies both sides of,
  which no stored sentex witnesses. `refuses-assert?` is not consulted for that second
  question: a minting caller **declines** a mint it cannot admit rather than placing it,
  so admitting the trigger under `:arbitrate` would store the fact and drop the
  consequence, which is the state the check exists to prevent. The derivation path is
  unchanged and still reports rather than throwing. *Class:* **Refusal** (only under the
  opt-in toggle; the shipped reading is untouched). *Migration:* a KB run with
  `VAELII_ASSERTIVE_ARG_TYPES=1` that relied on an `:arg-type` refusal of a symbol
  argument gets a minted membership instead — read the refusal off the mint's own
  `:type` (`:disjoint` where a disjointness axiom covers the pair), or run with the
  toggle off, which is the default. `:disjoint` gains a row in `type_contract_test`'s
  `carried` roster, `cascade-clash` being a second throw site that names no opposing
  handle. [docs/argtypes.md](docs/argtypes.md)

  *Breaks:* `:arg-type`, `*assertive-arg-types?*`, `VAELII_ASSERTIVE_ARG_TYPES`

- **`genl` declares neither argument position.** `(genlArg genl 1 thing)` read "the
  subtype is a subtype of `thing`", which stopped being true when `genl` gained predicate
  specializations of other arities: `(genl predicateTypeByArity relationTypeByArity)`
  relates two binary predicates and neither end is under the root. Under
  `VAELII_ASSERTIVE_ARG_TYPES=1` the declaration entailed `(genl predicateTypeByArity
  thing)` from that edge, which the arity descension check refused — two dropped
  conclusions and two `:arity` ledger entries on every load of the shipped KB, plus the
  `ontology_test` and `starter_test` sweeps that read them. Position 2 was already
  undeclared for the neighbouring reason (`(genl thing thing)` is not well-formed), and
  the comment now covers both. Neither position is thereby unconstrained: an individual at
  either end is `:not-well-formed` through `wff/genl-problems`, a disagreeing arity is
  refused by the descension check, and `(type_relation_predicate genl)` says of every
  position what a `genlArg` says of one.
  *Class:* **Refusal** (one withdrawn). *Migration:* a KB relying on `:arg-type` for a
  `genl` whose subtype argument has a visible place outside the `thing` hierarchy no
  longer gets one — that argument is now a legitimate predicate specialization.
  [docs/taxonomy.md](docs/taxonomy.md#genl-the-type-hierarchy)

  *Breaks:* `(genlArg genl 1 thing)`

- **A unary predicate's one position owes no `arg` declaration, and fifteen that
  convicted nothing are dropped.** `(arg P 1 T)` on a unary predicate says of the same
  extent what `(genl P T)` says — one record per instance against one edge — and for a
  term the engine interprets the shape in `vaelii.impl.predicates` refuses a wrong
  argument before any declaration is read. Measured per term over all 34 shipped unary
  predicates carrying one: fifteen are refused by the shape (`(symmetric Fred)` with Fred
  a person is `:not-well-formed`, never `:arg-type`) and their declarations convict
  nothing, so `abducible_predicate`, `anti_symmetric`, `anti_transitive`, `asymmetric`,
  `closed_extent_predicate`, `decontextualized_predicate`, `disjoint_metatype`,
  `forced_decontextualized_predicate`, `functional`, `irreflexive`, `modal_predicate`,
  `reflexive`, `symmetric`, `target_following_predicate` and `transitive` lose theirs.
  Every one of the 34 still refuses the same argument with the same `:type` afterwards.
  The other nineteen keep theirs, because for them the declaration is the only check
  there is — the eight state predicates in `CxLife` and `CxTime`, the four function marks
  and the seven relation-property marks the shape does not cover. `ontology_test`'s
  demand accordingly stops at arity 2, and `[not 1]` and `[contested 1]` leave its
  excused roster, being unary and now exempt as a class rather than by name. Fifteen
  declarations and their derived `arg1` projections leave the starter, each dropped
  declaration retiring one of each; the arity vocabulary below puts more back than this
  takes out, and the figures the tree ships are stated there. *Class:* **Refusal** (nothing the shape does not already
  refuse). *Migration:* none for a caller — the refused argument and its `:type` are
  unchanged. A KB extending one of the fifteen marks with a sub-predicate that relied on
  the declaration descending to it should declare its own.
  [docs/argtypes.md](docs/argtypes.md), [docs/predicates.md](docs/predicates.md)

  *Breaks:* `(arg symmetric 1 predicate)`, `(arg functional 1 predicate)`

- **`injection`, `surjection` and `bijection` name what a relation is as a function, and
  the engine reads each half where it can.** Saying a relation was a one-to-one function
  took four separate declarations — `(functional P)`, `(functionalInArg P 1)`,
  `(predAllSpecified P D)` and `(predSpecifiedAll P R)` — and an author who wrote some
  of them got partial enforcement with no report of the gap. The three composite marks are
  one declaration each, and eight CxCore forward rules derive the parts, so nothing is
  keyed on the new names. `injection` is single-valued, one-to-one and total; `surjection`
  is single-valued, total and onto; `bijection` derives the other two. The **domain and
  range are not arguments of the mark**: totality and ontoness are claims about two
  collections rather than about `P`, and `(arg P 1 D)` and `(arg P 2 R)` already state
  them, so the rules read them from there. A predicate declaring no `arg` pair gets the
  enforced marks and no audit. The two halves divide on what an open world can refuse: a
  second filler is refused or merged at the assert entry point, while totality and
  ontoness become `predAllSpecified` and `predSpecifiedAll` requirements that
  `all-specified-violations` reports when a caller asks. No new API function, and
  retracting the mark or either `arg` declaration withdraws what rested on it. The
  glossary gains `injection` and `surjection` and rewrites `bijection`, 173 to 176.
  *Class:* **Additive**. *Migration:* none — `bijection` shipped in no release, and the
  reading it had on `develop` (single-valued and one-to-one, with no totality or
  ontoness) is now `(functional P)` beside `(functionalInArg P 1)`, written directly.
  [docs/taxonomy.md](docs/taxonomy.md), [docs/predall.md](docs/predall.md)

- **The exact arity classes derive downward only, and the nine spellings of an arity are
  the nine the checks read.** Every `genl` edge on them runs one way — a
  `binary_predicate` is `binary` and is a `predicate` — and CxCore states no converse:
  the six `defnSufficient` facts that did (`(defnSufficient binary_predicate (and (arity
  ?x 2) (predicate ?x)))`) are not shipped. `(predicate ?x)` matches every class
  membership of every predicate by subsumption, once per `genl` route between the two, so
  the six cost **748 justifications and 600 ms of a 3.2 s starter load for 36
  memberships**, and a firing re-derived through a route that appeared after it left the
  KB's justification set depending on arrival order — 50 namespaces failed
  `test-util`'s net-neutrality check under `VAELII_ASSERTIVE_ARG_TYPES=1`, where a minted
  `(genl instance_relation_predicate predicate)` is the shorter route.

  What the classification was wanted for is the **arity**, and that is answered without
  it: `checks/exact-arity-classes` holds all nine — the relation-wide `unary` / `binary` / `ternary` beside the six predicate and
  function specializations — so `(binary R)` and `(binary_function F)` declare a length
  the assert check enforces, `settle`'s retroactive report triggers on, and a refusal
  names as its `:opposing-handle`, exactly as `(binary_predicate P)` always did. The six
  new spellings gain `#{:convicts :reach}` in `vaelii.impl.predicates`, and the roster is
  read in key order wherever a term could hold two, so which spelling a refusal names is
  content and not a map's iteration order. A KB wanting the kind membership as well
  writes the `defnSufficient` in its own context.
  *Class:* **Additive** — three relation-wide and three function spellings the checks did
  not read before; nothing that was refused is now accepted.
  *Migration:* none. A KB that wrote `(binary_function F)` and relied on the arity check
  ignoring it now has that length enforced.
  [docs/taxonomy.md](docs/taxonomy.md#relations-and-arity-policy)

- **The upper ontology's five-term skeleton moves to CxCore, the upper spindle's head,
  where every member can see it.** A spindle is three layers — a head every member sees,
  members that see the head and not each other, and a collector that sees every member —
  so a term defined in one member and *extended* from a second is invisible where it is
  extended and the closure breaks: with `living_thing` defined in `CxAbstract`, `(genl
  animal living_thing)` written in `CxOrganism` left `(genl? kb 'animal 'thing
  'CxOrganism)` answering **false** — `animal` could not reach the root from the context
  that defines it, so every `arg` constraint written there convicted nothing in its own
  context and only `CxUniverse`, which collects the whole upper spindle, resolved the
  chain. `intangible`, `spatial_thing`, `physical_object`, `living_thing` and
  `capability` — the five collections a member has to see to place its own types under
  the root — move with their comments and their own `genl` edges into `CxCore`, and are
  classified `inert` in `vaelii.impl.predicates` because the engine reads none of them by
  name. The kinds hanging off them stay with their members: `(genl artifact
  physical_object)` is CxAbstract's and `(genl animal living_thing)` is CxOrganism's, and
  both now resolve from their own context.
  `starter_test/a-term-two-spindle-members-touch-is-defined-in-the-head` reads the
  shipped files and holds the rule for both spindles — CxCore for the upper, CxUniverse
  or anything CxUniverse sees for the middle. *Using* another member's term is a separate
  question the rule does not cover; extending one is what breaks a closure.

  **The topology is described as what it is: two three-layer spindles, not one
  five-layer one.** A spindle is a head, its members and a collector; `CxUniverse` is the
  upper spindle's collector and the middle spindle's head, and it can be the second's
  head because it is the first's collector. `docs/contexts.md`, `docs/api.md`,
  `docs/glossary.md` (which gains a **Spindle** entry, and whose `CxUniverse` / `CxWell`
  entries stop calling themselves anchors), `vaelii.impl.starter`, `vaelii.starter`,
  `catalog`'s blurb and four comments now use head / member / collector throughout, in
  place of the "band" the docs had for a spindle's members.

  `starter_test/the-starter-ships-the-counts-its-docstrings-quote` goes with this: it
  pinned two exact sentex counts that every deliberate KB edit had to re-pin, and the numbers it guarded are now written as floors, which the arity vocabulary below then
  raises: `docs/kbs.md`, `catalog`'s `:scale` and `test_util` ship "1,600+ asserted /
  3,200+ stored" for the starter and "850+ sentexes" for the core vocabulary. `core_context_test`'s band still catches a core load
  that goes wrong in bulk. *Class:* **Additive** — a context move, a roster of five inert
  entries, a test and prose; no engine behaviour changes and no declaration is retired.
  *Migration:* none. A KB that asserted one of the five itself is unaffected, `CxCore`
  being visible from everywhere. [docs/contexts.md](docs/contexts.md)

- **A `genlCx` edge's merge sweep visits the readers it widened, not every reader.**
  `equate-under-context-edge` folds the functional and antisymmetric merge derivations
  over the facts a `(genlCx sub super)` edge newly exposes, and each derivation swept
  every reader below the candidate's own storage context — including readers this edge
  had changed nothing for, which were being asked a question already answered when the
  fact arrived. The readers whose ancestor set the edge moves are `context-down(sub)`,
  and that is now the set both twins sweep. The set is exact rather than an
  approximation: `context-down` filters its candidates by each one's own forward walk,
  so it is the inverse of `context-up` with `except` holes included. One edge over the
  shipped starter falls from 5,141 derivations to 352, and the count stops growing with
  the KB — three successive edges cost 5,141 / 5,492 / 5,843 before and 352 each after,
  which is what made every `genlCx` edge more expensive as a KB gained contexts.
  `starter/load-into` falls from 3,235 ms to 2,176 ms. No answer changes: the merges,
  their contexts, the justifications `why` reports, the truncation notice and belief are
  the same, and `genlcx_sweep_test` and `genlcx_sweep_cost_test` pin both halves — what
  must still be derived, and that the cost no longer grows with readers the edge does
  not reach. *Class:* **Fix**. *Migration:* none.

- **A unary predicate declares its one argument position only when its own `genl` parent
  does not already imply the type.** Six marks whose parent sits *below* the type they
  declared — `instance_relation_predicate`, `type_relation_predicate`,
  `equivalence_relation`, `injection`, `surjection` and `bijection`, each of which genls
  `binary_predicate` or `functional` — drop `(arg X 1 predicate)`. The declaration
  restated in a weaker form what the edge already concludes and turned that conclusion
  into a precondition: `(instance_relation_predicate P)` stated after `(arity P 2)` was
  refused `:arg-type` for P not yet being a predicate, when the assertion supplies
  predicate-hood through the edge, while the same pair in the other order was accepted.
  A declaration that demands its own conclusion is the reason for the drop; the
  ordering asymmetry it removes is the consequence. `arg`'s refusal half convicts on an
  absence and is scoped out of the order-independence invariant by design
  ([docs/argtypes.md](docs/argtypes.md), "Three directions"), so a KB given a narrowing
  declaration and its fact in different orders still holds different facts — what these
  six had on top of that is a declared type their own parent already supplies.
  `arity_vocabulary_test/a-predicate-only-classification-is-order-independent-of-the-arity`
  compares the two orders on the whole closure rather than on acceptances. The refusals the rows carried
  are both retained and one of them is sharpened: a term outside the relation hierarchy
  is still `:arg-type` through the `(arg fixed_arity 1 relation)` floor the marks
  inherit, and a **function** is now `:disjoint — cannot be both
  instance_relation_predicate and function` where it read `:arg-type: must be a
  predicate`, which names the contradiction instead of a missing type. `fixed_arity`,
  `variable_arity` and the seven function marks keep their declarations, because their
  parent *is* the type they declare and the edge alone refuses nothing there.
  *Class:* **Fix** — the engine did not hold an invariant it documents; a caller relying
  on the refusal keyword for the function case reads `:disjoint` instead of `:arg-type`.
  [docs/argtypes.md](docs/argtypes.md)

- **Starter loading preserves non-unary predicate specialization.** The starter
  assigns `unary_predicate` only to the `thing` subtype hierarchy, not every `genl`
  node. Binary mapping predicates retain their declared arity. Exact `arity` derives
  `fixed_arity` even when argument-type entailment is disabled. Taxonomy coverage
  excludes declared non-unary predicates without hiding unknown type islands.
  Argument metadata (`arg` and its projections, `genlArg`, `quotedArg`, `interArg`)
  accepts relations, including functions, which is what lets a function carry one at
  all: `InstantFn` gains `(arity InstantFn 6)` and the six `(arg InstantFn N integer)`
  declarations its calendar fields never had, and `YearFn`, `MonthFn`, `DayFn`,
  `QuantityFn` and `QuantityIntervalFn` gain their exact classes. Recursive
  function-input enforcement remains follow-up work, documented in
  [docs/argtypes.md](docs/argtypes.md#relation-wide-declarations-and-the-runtime-boundary).
  *Class:* **Fix**.
  [docs/taxonomy.md](docs/taxonomy.md#relations-and-arity-policy)

- **A late `(symmetric P)` folds a mirrored pair both of whose rows a rule concluded.**
  The mark's effect is canonicalization, so a declaration arriving after both spellings
  were written migrates the records into one. The fold ran only where one of the pair
  stood on nothing but its own premise: a pair two rules had concluded was left alone,
  pair and all, so the mark arriving first left one record and the mark arriving last left
  two, each believed, and a predicate above them answered the proposition twice.
  `integrate/fold-supports!` re-hangs the justifications naming the doomed row as their
  *consequence* onto the survivor — the consequence-side twin of `fold-dependents!` —
  which leaves the doomed row supporting nothing for the ordinary sweep to collect. No
  justification is deleted and the JTMS gains no entry point; a justification naming the
  survivor among its own antecedents is skipped rather than retargeted, since a datum that
  grounds itself is groundable for ever. The tie-break is unmoved: the row standing on
  nothing but its premise is still the one that goes, and between two rows the fold has no
  other reason to separate the lower handle survives. *Class:* **Fix**. *Migration:* none.
  [docs/canonicalization.md](docs/canonicalization.md)

- **`recover` drops a malformed `genl`/`genlCx` declaration rather than crashing on it.**
  The taxonomy rebuild reads each stored `genl`/`genlCx` sentex positionally for its two
  endpoints, and it replays what is **stored** rather than what would pass the assert-time
  `wff` check. A store an older or foreign writer left a non-edge sentex under the
  `genl`/`genlCx` functor root then reached the rebuild arm as a malformed edge — a
  two-element sentence binds the member as the subtype and nil as the super — and the nil
  entered the closure as a node, where `strong-components` threw a `NullPointerException`
  the moment `restore-depths` condensed a loose relation (the crash blocked recovery of the
  whole store, with no partial-recovery fallback). `replay-edge` now activates an edge only
  when both endpoints are symbols, so a malformed declaration is skipped and counted,
  logged once at `:warn` under `::edges-malformed` — the taxonomy's twin of the
  `::justifications-unrooted` skip `rebuild-tms` already makes. No well-formed store holds
  such a declaration, so a store the current entry point wrote replays unchanged.
  *Class:* **Fix**. *Migration:* none.
  [docs/storage.md](docs/storage.md#persistence--recovery)

- **The order-independence sweep draws the last three releases' new vocabulary.**
  `mixed_order_property_test`'s chain pool spanned the mechanisms that existed when it was
  written and none that arrived after, so a `different` guard, a `functionalInArg` mark
  descending a predicate edge, a `symmetric` mark over a pair two rules concluded and the
  `predSpecifiedAll` audit were permuted by nothing. Twelve chains join the pool and two
  keys join the reading: the `different` answer over five probe pairs, and the audit's
  violation set, both per view context. The guard's two arguments are a pair one of the
  pool's own `equals` edges merges, and the `indeterminate_term` category reaches it twice
  more — a direct membership, and a kind declared under it that arrives through the genls
  fan rather than by name. The witness runs the whole pool and a second draw with neither
  suspension in it, so the guard is on the record holding as well as withdrawn.
  `entry_point_and_report_test` gains the two `quotedArg` rows the argument-constraint
  non-reach was covering without naming, and `docs/taxonomy.md`'s arrival-order table
  names the spelling and what separates its conviction from the other three.
  *Class:* **Additive** — tests, a roster row and prose. *Migration:* none.
  [docs/taxonomy.md](docs/taxonomy.md)

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

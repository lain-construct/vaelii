# Changelog

## 0.13.0 — 2026-08-25 — "calendar time, joined queries, and the doors that refuse"

- **`:disk` and `:pg-disk` are `:disk-log` and `:pg-disk-log`.** The second `disk` in each
  reads as *out of core*; it means *durable*. `DiskKvBackend` holds the whole key→value map
  in RAM — a `Long` at each counter key, a set at each set key, the shape `MemoryKvBackend`
  holds — and logs its mutations to a write-ahead log it replays once at open and thereafter
  writes but never reads; its own docstring says the quiet part, "the disk only buys
  durability." The pairing itself is a good one and none of it changes: durable records
  under an index that opens populated and needs no `reindex`. `:disk-log` is what that is.
  *Class:* **Breaking** for any opts map, script or `VAELII_TEST_BACKEND` value naming
  either name. *Migration:* rename the selector — `{:backend :disk}` →
  `{:backend :disk-log}`, `{:index :disk}` → `{:index :disk-log}`, `{:backend :pg-disk}` →
  `{:backend :pg-disk-log}`, `VAELII_TEST_BACKEND=disk` → `=disk-log`. **The on-disk layout
  does not move**: a directory written under either old spelling opens under the new one
  with no reindex, no recovery and no `format-version` bump, and its record files are
  byte-identical across the open. Neither name is aliased — `open-kb` refuses both
  spellings with `:type :unknown-backend` and names the pairing to take instead, since an
  index axis names a directory *layout*, and a name that answers to two layouts opens a
  store in one its caller did not ask for.
  [docs/storage.md](docs/storage.md#backend-selection-two-independent-axes)

  *Breaks:* `:disk`, `:pg-disk`, `VAELII_TEST_BACKEND=disk`

- **`edit!` is all-or-nothing.** A batch refused by an engine check `check-edit` cannot
  predict — one that only bites because an earlier entry in the same batch landed first, a
  `disjoint` clash or an `arg` violation or a `functional` slot — used to leave the entries
  before it stored with the settle not run. It is now rolled back at the handles it wrote:
  every add retracted (which collects what it derived through the dependency-directed
  sweep), every premise mark undone, every strength it raised restored, the violations
  ledger and the program and the refusal record put back. Belief and the handle roster are
  what they were before the call, and the change feed is told nothing. The refusal is
  rethrown carrying its own `ex-data` plus `:rolled-back true` and `:in` / `:index` /
  `:entry` naming the line. The rollback is `preview`'s, one implementation and two
  callers. `with-deferred-settle`, `assert-many` and `bulk-assert-facts!` stay
  non-transactional and now say so — the order-insensitive seed loader is built on partial
  progress. *Class:* **Breaking** for a caller that read a half-applied batch back, and for
  one reading `apply-proposal!`'s `:applied`, which now answers zero on a refusal instead
  of counting the prefix that landed. *Migration:* delete the recovery step — there is no
  half-applied batch to settle by hand or to clean up. Discriminate a refusal on `:type` as
  before; `:rolled-back true` is new alongside it.
  [docs/api.md](docs/api.md), [docs/preview.md](docs/preview.md),
  [docs/troubleshooting.md](docs/troubleshooting.md), [docs/feed.md](docs/feed.md)

  *Breaks:* `edit!`, `edit-with-consequences!`, `apply-proposal!`

- **A reified context is collected when nothing is in it, names it or wires it.** An
  object NAT is swept when the last sentence naming it goes, and a `cx/` context stood
  outside that gate — so a KB that mints contexts, one per calendar period, accumulated
  empty constants nothing could reach and nothing would remove. A context is now collected
  on the same `retract!` / `edit!` sweep when all three of its liveness sources are empty:
  nothing stored in its context slot, no stored sentence naming it as a term, no stored
  `genlCx` edge mentioning it. Whichever goes last is the retraction that collects, and
  the end state is the same in every order. A `genlCx` edge the structural producer
  **computed** off the context's own `termOfUnit` is none of the three — decided by
  authorship, since reading a computed edge as a reference leaves every ordered pair
  holding the other end up forever. The trigger stays local: a removed sentex's context
  slot is read beside its sentence, so the last fact leaving is the removal that orphans,
  and each candidate costs one O(1) `count-in-context` plus, only when that is zero, one
  term-index read over its own footprint. A KB declaring no `contextDenotingFunction` pays
  nothing. *Class:* **Breaking** — a caller that emptied a reified context and then read it
  back by its constant, or looked for it among `contexts`, finds it gone rather than
  standing empty. *Migration:* name the expression, never the constant: `(CxTimeFn CxMonad
  (DatetimeFn "2000"))` resolves through the map at every door and re-mints where the KB
  has collected it, dedupping to one constant as it always has — the `cx/` symbol and the
  handle are freshly allocated, as any re-mint's are. A context to be kept while its extent
  is empty takes a stored `genlCx` edge or a sentence naming it.
  [docs/context-nat.md](docs/context-nat.md), [docs/nat.md](docs/nat.md)

  *Breaks:* `contexts`, `count-in-context`, `contextDenotingFunction`

- **`lein cli load` reads a text KB, not an EDN vector.** It took a file holding one EDN
  vector of `[sentence context opts?]` entries; it takes a `Cx<Name>.txt` file or a
  directory of them, the file name naming the context, and answers
  `{:contexts :sentences :files :path}` instead of `{:loaded :stored}`. One format across
  the shipped ontology, `export-text!` and this command, rather than a third spelling only
  this command read. *Class:* **Breaking** for a script feeding it the vector form.
  *Migration:* write one file per context named for it, holding the bare sentences
  (`(dog Muffet)`), and drop the per-entry context; a `{:strength :monotonic}` entry becomes
  a `(set/monotonic (dog Muffet))` wrapper. [docs/operations.md](docs/operations.md),
  [docs/api.md](docs/api.md)

  *Breaks:* `lein cli load`

- **The proving levels agree with belief about a defeated answer.** `prove` and `query`
  with a depth re-opened the rule that concluded a defeated datum and proved it again from
  believed premises, answering both sides of a settled clash where `ask` reported the
  defeat — the standing disagreement labeling.md named. An answer a rule expansion
  produces that names a stored sentex the JTMS holds defeated is dropped where it becomes
  ground — a third goal-stack marker in the DFS, a `:derived` slot on the node engine's
  node — so neither a top-level answer nor an intermediate subgoal feeding a further rule
  re-derives it. A defeated premise re-derived from other believed premises reads OUT:
  belief decided that datum under the current state, and a derivation is not a second
  chance. A KB with no contradiction pays nothing; the index is nil while the defeated set
  is empty. *Class:* **Breaking**: labeling.md documented the re-derivation, so a caller
  could have read it as a contract. *Migration:* a caller that read `prove`'s answer on a
  defeated side as a second opinion now gets belief's; `why-not` says `:defeated`.
  [docs/labeling.md](docs/labeling.md), [docs/levels.md](docs/levels.md),
  [docs/defenses.md](docs/defenses.md)

  *Breaks:* `prove`, `provable?`, `query`, `argue`

- **A forward firing that rests on a measure comparison names the unit rows it read.**
  A `quantityLessThan` antecedent fired with a justification that omitted the
  `dimensionOf` / `conversionFactor` rows the comparison converted through, so retracting
  a unit row left the conclusion believed. The quantity prover now answers a forward join
  *with support*, and those rows enter the firing as ordinary justification antecedents —
  so the strength cap, the placement and the retraction sweep follow with nothing added. A
  reading taken over a set of agreeing declarations names all of them, so retracting one
  of two identical rows withdraws a conclusion the survivor still licenses, the same
  over-approximation the qualitative pass states; a pure arithmetic comparison still adds
  no supporter. A datum arriving on a support predicate re-joins the rules carrying such
  an antecedent, so the unit table may arrive last. *Class:* **Breaking**, in the sense
  that belief after a retraction is observable — a caller depending on the conclusion
  outliving its unit row was depending on the bug. *Migration:* none;
  a conclusion that outlived its unit row is withdrawn with it now, and `why` names the
  row. [docs/quantity.md](docs/quantity.md), [docs/inference.md](docs/inference.md)

  *Breaks:* `forward-chain`

- **Calendar constructors, and a time context computes its own year–month–day cone.**
  `(YearFn 2000)`, `(MonthFn 2000 1)` and `(DayFn 2000 1 15)` are `unreifiableFunction`s
  in `CxTime` whose arity is their precision; `(CxTimeFn CxMonad (MonthFn 2000 1))` is a
  computed spec of the year's context and a day of its month's, with no `genlCx`
  asserted, and the calendar and ISO spellings name the same intervals. An `(R a b)`
  evidence fact arriving after both contexts now reconciles the functions declared to
  order by `R`, the retroactive oracle the doc listed as unbuilt. *Class:* **Additive**.
  [docs/context-nat.md](docs/context-nat.md), [docs/time.md](docs/time.md)

- **A calendar term now has endpoints, so a date orders itself.** `(startOf (YearFn 2000)
  ?i)` and `(endOf …)` are answered with an `(InstantFn 2000 1 1 0 0 0)` moment computed
  from the term's fields — six integer fields so one moment has one spelling, and
  **half-open**, so the end of 1999 and the start of 2000 are the same term and
  consecutive calendar terms `meets` rather than `before` (`precedes` is the ordering that
  covers both). `MonthFn`, `DayFn` and a reduced-precision `DatetimeFn` answer the same
  way, down to the second. Two computed moments order by field comparison; a *stated*
  instant is never invented an order. The Allen relation between two calendar terms is
  classified straight from their bounds rather than through a network, so `(during
  (MonthFn 2000 3) (YearFn 2000))` and `(meets (MonthFn 2000 2) (MonthFn 2000 3))` come
  out with nothing stored — no sentex, no handle, no justification, and so nothing to
  retract and no orphan to sweep. Opt-in as `(v/add-reasoner kb :calendar)`, the roster's
  tenth; `InstantFn` ships in `CxTime` either way and the starter is 1,843 sentexes.
  `provers/shadowing-channels` gains a fourth channel, `:calendar`, so a term's field
  structure — a source no fact-reading prover has — stops the interval or point calculus
  answering such a goal alone. *Class:* **Additive**: a new opt-in reasoner and three new
  `CxTime` declarations, no public var moves, and a KB that registers nothing is unchanged.
  [docs/time.md](docs/time.md), [docs/context-nat.md](docs/context-nat.md)

- **`CxChange`: a shipped event calculus.** `happens`, `initiates`, `terminates`,
  `initially`, `holdsAt`, `clipped` and `clippedBefore` in `CxTime`, the `fluent` type in
  `CxAbstract`, and four rules in the new middle context `CxChange`. `clipped` and
  `clippedBefore` chain forward — an `unknown` antecedent is answered at level 6, which
  expands no rule, so a backward `clipped` would leave every fluent holding for ever —
  and `holdsAt` is a backward rule with inertia through `(unknown (clipped …))`. A fluent
  is a reified NAT, `(AsleepFn Whiskers)`. The theory is stratified as written. The
  forward join reads the `instantBefore` pairs a narrative states, not the point
  algebra's closure. The starter is 1,843 sentexes. *Class:* **Additive**.
  [docs/time.md](docs/time.md), [docs/commonsense.md](docs/commonsense.md)

- **A metric constraint narrows an interval relation, without a word being written about
  intervals.** `startOf` / `endOf` make a `temporalDistance` and an Allen relation claims
  about the same thing, and the reading back — the closure as an interval network, through
  the thirteen endpoint signatures — is now the Allen calculus's **narrowing**: a second
  reader of the same network, intersected pair by pair into the one read from stored facts.
  So a KB stating two meetings' endpoints and the gap between them answers
  `(before Standup Review)`, `(precedes …)` and the refutation
  `(not (sharesTimeWith …))` off the measures alone, and one pair narrowed metrically
  composes with the next narrowed by a stored fact, because what the pass runs over is one
  network value either way. The entailment **carries its support**: the `startOf` / `endOf`
  facts naming both intervals' instants, plus the constraints along the shortest chain each
  of the four endpoint gaps was composed out of — the path and not the whole network, so a
  forward rule joining on such a relation is an ordinary firing that the JTMS withdraws when
  a constraint behind it is retracted, and does not withdraw when an unrelated one is. The
  narrowing declares its **sources** — `temporalDistance`, `startOf`, `endOf`, `dimensionOf`,
  `conversionFactor` — so one of them arriving after the rule and the facts re-checks and
  re-joins the rules carrying an interval antecedent, which is what keeps the firing
  order-independent. Sound but not sharp, as the reading always was: the four bounds are
  read independently, which can only leave a relation in that the metric network excludes.
  Reading the network does not depend on a prover being registered, the same rule every
  qualitative network follows; `:metric-time` remains the opt-in for answering a
  `temporalDistance` goal. *Class:* **Additive**: no public var changes, nothing that was
  entailed stops being entailed, and a KB stating no `temporalDistance` reads exactly the
  network it read before.
  [docs/stp.md](docs/stp.md)

- **An arriving `temporalDistance` constraint is relaxed into the metric closure rather
  than closing the network again.** The all-pairs pass is cubic in the instant count and is
  memoized on the network *value*, so every arriving constraint is a different network — and
  a timeline being loaded one fact at a time paid for a whole pass per fact, 86 ms of it at
  four hundred instants. A closed network now carries the distance matrix its bounds were
  read off, and a network that **tightens** the one last resident for the context is relaxed
  into that matrix — `d[i][j] = min(d[i][j], d[i][p] + w + d[q][j])` over every pair at once,
  with only the bounds that moved read back — which takes the same arrival to 1.9 ms. A
  *widening* (a retraction, a defeat, a loosened bound) has no such identity and still pays
  the whole pass. No answer moves: `stp_incremental_test` folds generated networks in every
  order against one run from nothing, the closed network bound for bound and the
  inconsistency verdict alike, and `lein perf`'s `metric-closure-warm-start` pins the shape
  at 8× the instants under 35× per arrival. `lein bench-stp` is the report the figures come
  from. *Class:* **Additive**: a cost change with no answer change — `stp/close` keeps its
  signature and its meaning, the new `close-state` / `close-state-from` / `tightening-of?`
  are `vaelii.impl`, and `test/golden/api-surface.edn` does not move.
  [docs/stp.md](docs/stp.md)

- **`SupportingProver`, and the metric and duration provers reach a forward join.** A
  prover whose answer is a function of stored facts implements `SupportingProver`
  (`support-functors` / `support-sources` / `solve-with-support`) beside `Prover`, and
  `chain` unions its supported answers with the matcher's. `temporalDistance`,
  `totalDuration` and `overlapDuration` were unreachable from a forward join — `ask`
  answered what forward chaining derived nothing from — and now fire carrying the handles
  the bound rests on: for the metric network the shortest-path chain plus the unit rows
  each leg converted through, from a successor table the same Floyd–Warshall pass fills,
  falling back to the whole network when a zero-weight cycle closes the walk.
  *Class:* **Additive**: a new SPI protocol, pinned in `test/golden/spi-protocols.edn`, and
  forward rules that derived nothing now derive. [docs/inference.md](docs/inference.md),
  [docs/stp.md](docs/stp.md), [docs/duration.md](docs/duration.md)

- **A quantity can be rising.** Nothing in the engine said which way a quantity was
  going, and a KB usually has that where it has no figure at all — nobody knows how fast
  the tap runs, and everybody knows the tub fills when the tap beats the drain.
  `vaelii.impl.sign` is the layer for it: a quantity's sign is `SignNegative`, `SignZero`
  or `SignPositive`, `(qualitativeSum A B Q)` / `(qualitativeDifference A B Q)` /
  `(qualitativeProduct A B Q)` declare which quantities add, subtract and multiply into
  which, and `(derivativeOf R Q)` names the rate that makes `(trendOf Q S)` the sign of R
  read at the other end of the edge — a constraint both ways, so a stated trend pins its
  rate as well. **An ambiguity is answered with nothing.** A positive and a negative sum
  to the sign of whichever is larger, so all three values survive and no goal about the
  total is answered until a `(greaterInMagnitudeThan A B)` says which — never a guess
  between three. That comparison is between two *quantities*, not two measures, which is
  the case the layer exists for; it is declared `transitive` and `asymmetric`, so a cycle
  of magnitude claims is a contradiction the KB reports. The reading is a greatest
  fixpoint over sets of possible signs — order-independent by intersection, with a set
  narrowed to nothing reported as `:sign-inconsistency` and no sign goal answered in that
  context. `SignProver` is a `SupportingProver`, so a forward rule resting on a derived
  sign names the facts behind it and is withdrawn when one goes, and its `support-sources`
  put a comparison stated *after* the rule and the facts in front of the rules concerned.
  Opt-in as `(v/add-reasoner kb :sign)`, the roster's ninth; the vocabulary ships in
  `CxMeasure` either way, and the starter is 1,843 sentexes. *Class:* **Additive**: a new
  opt-in reasoner and new vocabulary, no public var moves, and a KB that registers nothing
  stores and retrieves these facts as ordinary facts.
  [docs/sign.md](docs/sign.md)

- **The instance-level comparatives compose.** `heavierThan`, `tallerThan` and
  `olderThan` are declared `transitive` beside the `asymmetric` two of them already
  carried, so two stated comparisons answer the third off the closure prover with no
  measure anywhere: a KB told an elephant outweighs a horse and a horse a dog answers the
  elephant against the dog, which is how a common-sense KB usually knows it. The pair
  `asymmetric` + `transitive` is the strict order `largerThan` already stands in — the two
  are not disjoint, only `transitive` and `antiTransitive` are — and it entails
  irreflexivity as a reading without setting the mark, so a lone `(heavierThan a a)` is
  still admitted rather than refused. The backward rules over `weightOf` / `heightOf` /
  `birthYearOf` are untouched and answer the same pairs they did; where both routes reach
  a pair they agree, a chain of strict measure comparisons being one. The starter is 1,843
  sentexes. *Class:* **Additive**: three declarations arrive, no predicate loses a
  property, and nothing that was answered stops being answered.
  [docs/commonsense.md](docs/commonsense.md)

- **The two numbers that bound the relation-algebra mask layer are written down.** Every
  bounded cache in the qualitative and metric layers already declares itself to the cache
  register with its limit — the compiled algebras at 64, the decode tables at 8192, the
  path-consistency and support passes at 256 each, the metric closures and their
  reconstruction tables at 256, the closure answers at 100 000 members. The two figures
  that are *not* caches had no reader-facing statement anywhere: the **algebra width**, 62
  base relations, above which `compile-algebra` refuses rather than truncating, because a
  constraint is the bits of a long; and the **dense-table threshold**, 2^18 entries, which
  decides whether a composition table covers whole masks or base relations only. Both are
  build decisions — nothing is held, nothing is evicted — so they belong beside the
  fallback in [qcn.md](docs/qcn.md) rather than on the caches page, which now says so and
  points there. `qcn_mask_test` pins both values against the doc. *Class:* **Additive**: no
  constant moves and no answer changes; two numbers a reader could find only by reading
  the source are stated.
  [docs/qcn.md](docs/qcn.md)

- **`or` in a rule antecedent, stored as one rule per alternative.**
  `(implies (or A B) C)` is written directly and stored as the two rules `(implies A C)`
  and `(implies B C)` — the antecedent twin of the conjunctive-consequent split, and the
  same mechanism: the connective is gone before anything is canonicalized, keyed or
  indexed, so each alternative is an ordinary rule sentex with its own handle, its own
  justifications, its own retraction, and it dedups against an individually asserted
  twin. The distribution is to DNF, so `(implies (and (or A B) D) C)` becomes two rules
  with `D` in both; the two polycanonicalizations compose into the **product**, so a rule
  that disjoins its antecedent and conjoins its consequent stores four; and an
  `exceptWhen` is re-attached once per expansion, against that expansion's own handle.
  `assert` / `assert-rule` return the vector of handles whenever a rule expanded, which
  they already do for a conjunctive consequent. Range restriction is asked **per
  alternative** — `(implies (or (dog ?p) (cat ?q)) (fed ?p))` passes the flat read, and
  one of the two rules it expands to concludes about a variable nothing binds — and the
  refusal names the disjunct. *Class:* **Additive**: no rule that stores today stores
  differently, `or` having no meaning to change.
  [docs/canonicalization.md](docs/canonicalization.md)

- **`:disjunction-too-wide`, and the positions `or` is refused from.** A disjunctive
  antecedent is capped at 16 alternatives, refused under a `:type` of its own with the
  count named; the width is paid in handles, index entries and TMS nodes rather than at
  query time, and nested disjuncts multiply, so a rule that reads like one line can cost
  thousands. Past the cap the alternatives are better named as a type. `or` elsewhere is
  refused `:not-well-formed`, each refusal carrying the rewrite that is expressible: a
  rule **conclusion** or a standalone sentence points at `set/assumptionRule` plus a solve
  (belief is a label on a sentex, not on a set of them); an `unknown` / `thereExists` /
  aggregate **body** points at the rewrite for that frame, each being answered as one
  closed level-6 query that unions nothing; an `exceptWhen` **query** points at one
  `exceptWhen` per alternative, since a rule's exceptions already block if any holds;
  `(not (or A B))` points at two negated antecedents, that being what De Morgan makes it;
  and an empty `(or)` expands to no rules at all. *Class:* **Additive**: a `:type` where
  none was, over input the engine has no other reading for — `or` is not a declared
  predicate, so a literal on it matches nothing and fires never.
  [docs/canonicalization.md](docs/canonicalization.md)

- **A disjunctive *goal* is refused (`:shape`) rather than unioned.** `ask`, `ask?`,
  `prove`, `query`, `query-plan`, `abduce`, `sentexes-matching` and `handle-of` refuse an
  `or` anywhere in a goal, as a whole goal or as a conjunct. A rule is expanded once, at
  the write door; a goal would have to be expanded at every read, and a read normalizes to
  **one** conjunction that the planner orders once (`query-plan` shows *the* chosen order)
  and both engines walk as one — so answering the union at `prove` while `query-plan` and
  `abduce` refused it would make one spelling mean something different at each door. The
  message names the two-line rewrite: run the query once per alternative and concatenate,
  or put the disjunction in a rule, which *is* expanded, and ask for its conclusion.
  *Class:* **Refusal**: a goal on the undeclared predicate `or` matches nothing, so the
  door answers with no solutions — the answer shape a caller is least likely to question,
  since it reads as "no" rather than as "I cannot". *Migration:* run the query once per
  alternative and concatenate, or put the disjunction in a rule — which *is* expanded —
  and ask for its conclusion.
  [docs/canonicalization.md](docs/canonicalization.md)

  *Breaks:* `ask`, `ask?`, `prove`, `query`, `query-plan`, `abduce`, `sentexes-matching`,
  `handle-of`

- **A `watch` on a disjunctive goal is refused rather than registered.** No stored
  sentence unifies with an `or`, so a watch on one delivered nothing for the life of the
  KB while `watchers` listed it as live — the silent-nothing every other
  `:not-watchable` refusal exists to prevent, and the one shape the read doors already
  turn away at their own guard. *Class:* **Refusal**: a registered watch on an `or` goal
  never called its listener, so no working caller exists. *Migration:* register one
  watch per alternative. *Breaks:* `watch`, `:not-watchable`
  [docs/api.md](docs/api.md), [docs/feed.md](docs/feed.md)

- **A NAF query joins its conjunction, and `forall` is the sugar over it.**
  `(unknown (thereExists ?x (and A B)))` — and a `thereExists` or an `exceptWhen` query
  over a conjunction — is answered as one join whose conjuncts share a witness, where it
  was refused. Every conjunct's predicate is posted to the re-check index and is a
  negative edge for stratification. NAF nests as far as it stratifies, which is what `(forall ?y (implies Body Head))`
  canonicalizes into — `(unknown (thereExists ?y (and Body (unknown Head))))`, ¬∃?y
  (Body ∧ ¬Head), true on the empty domain — so the sugared and the nested spelling are
  one handle. A quantified variable no conjunct of the query can produce is refused
  `:naf-not-closed`. *Class:* **Additive**: input the engine refused is read, and a
  `:type` where none was. [docs/naf.md](docs/naf.md)

- **An aggregate's census body joins.** `(agg/count ?n ?c (and (childOf Bob ?c) (asleep
  ?c)))` counts the children who are asleep — one witness satisfying both conjuncts —
  where a conjunctive body was refused. `provers/aggregate-values` runs it through
  `conjunction-solutions`, the joined evaluator `unknown` / `thereExists` / `exceptWhen`
  already read, so `?v` is threaded across the conjuncts and a body variable named nowhere
  else in the rule is the census's own join rather than a group it has to be handed. Every
  conjunct's predicate is posted to the re-check index and is a negative edge for
  stratification, so a fact arriving on any of them re-takes the census and a cycle
  through any of them is refused. A census variable no conjunct of the body binds and no
  earlier antecedent names is refused `:naf-not-closed`; a disjunctive body stays refused,
  a count over a union not being the sum of two counts. *Class:* **Additive**: input the
  engine refused is read, and the `:quantified-conjunction` refusal is retired with the
  last site that raised it. [docs/aggregate.md](docs/aggregate.md)

- **`closedExtentPredicate` closes one predicate's extent, per context.** Declared the way
  `abduciblePredicate` is and read from the asking context's up-cone: where the grant is
  visible, `(not (P a …))` with no positive answer at level 6 is answered true by a prover
  that stores nothing, and a `(not (P …))` antecedent under it is negation as failure —
  withheld from the join, decided at derive time in the placement context, and brought
  back by the re-check index when `(P a …)` arrives. A rule concluding `P` whose body reads
  `(not (P …))` under the grant is a cycle through negation and is refused from either
  end, the rule or the declaration. `why-not` reports `:closed-extent`.
  *Class:* **Additive**. [docs/naf.md](docs/naf.md), [docs/from-cyc.md](docs/from-cyc.md)

- **A forward join over a transitive predicate reads the closure, and names the edges it
  crossed.** A rule antecedent on a `(transitive P)` predicate — `causes`, `partOf`,
  `instantBefore` — matched stored edges only, so a rule fired across one hop and a
  narrative had to write down the pairs it wanted read. `chain/join-antecedent` now unions
  the walk's answers with the matcher's, per reader context, and
  `provers/TransitivePredicateProver` is a `SupportingProver`: each answer carries the
  handles of one chain of edges (breadth-first, so a shortest one), the firing rests on
  exactly those, and retracting or defeating a hop of the chain withdraws the conclusion
  while an edge the chain never crossed withdraws nothing. An arriving edge re-joins the
  rules carrying such an antecedent in full, so the answer does not depend on which hop
  came last, and neither does the `(transitive P)` declaration arriving after the edges it
  walks. Both ends open still contributes nothing from the walk, a closure being quadratic
  in a chain's length, and a rule that concludes on the predicate it would walk takes the
  matcher alone — such a rule is the closure written out, and racing it would make the
  chain a function of firing order. `instantBefore` and `instantAfter` are declared transitive
  in `CxTime`, so `CxChange`'s `clipped` reads the order a narrative's consecutive links
  imply rather than the pairs it spells out. *Class:* **Additive**: a rule that fired
  before fires on at least as much, and the closure was already what `ask` answered.
  [docs/taxonomy.md](docs/taxonomy.md), [docs/inference.md](docs/inference.md),
  [docs/time.md](docs/time.md)

- **A rule joined to a growing transitive extent now derives the same conclusions
  whichever order its facts arrived in.** A declared-`transitive` predicate's closure is
  answered, never stored, so no pair of it is ever a datum on the chaining agenda: a rule
  like `[(does ?a ?act) (causes ?act ?e)]` could reach a closure pair only from its other
  antecedent's trigger, and when a later link extended the closure nothing put that
  trigger back. Twelve of twenty-four arrival orders of four facts derived
  `(responsibleFor A1 E2)` and twelve did not — an **order-independence** failure, the
  first of the four properties, in the shipped configuration. `special/transitive-seeds`
  and `transitive-rule-seeds` close it on all three arrival orders the closure has
  ingredients for — a link, the `transitive` declaration, or the rule arriving last — the
  way `subsumption-seeds` already did for a `genl` edge, whose docstring states the
  principle: firing the rules keyed on the arriving predicate is not the same thing as
  re-firing the rules the arrival just connected. Both arms are off unless some rule takes
  an antecedent on the predicate, so `assert_cost_test`'s per-family read budgets are
  unmoved. The re-seed is taken **only for a new conclusion**, which is what keeps the
  remedy from costing more than the defect: where the rule *concludes* the transitive
  predicate, the partner facts it seeds are the very ones whose firing concluded the link,
  so a re-derivation re-drives its own trigger and the agenda — a plain queue with no
  dedup — never drains. Two `edge` facts under a recursive rule ran to
  `:max-derivations` and truncated. A re-derivation adds a justification rather than a
  link, so the closure it would re-drive the join over is the one the join already ran
  against. Found by the `VAELII_PLAN=0` sweep; the surrounding audit found `genl`,
  `genlCx`, `symmetric`, `inverse`, `transitiveInArg`, the equality partition and
  `instantBefore` already order-independent over the same shape. *Class:* **Fix**.
  *Migration:* none; a KB that worked around it with an explicit `forward-chain` still
  works. [docs/inference.md](docs/inference.md)

- **A rule concluding a more general predicate keeps its transitive walk.** A forward rule
  whose antecedent walks a `(transitive P)` closure was declined the walk whenever the rule
  concluded a predicate `genl`-related to `P` in **either** direction — but only the
  sub-predicate direction feeds `P`'s own graph and could make the shortest chain depend on
  how far the rule had run. A rule concluding a *super*-predicate of `P` never does: a
  general conclusion is no fact about `P`, so the walk was suppressed for nothing, and the
  rule fired across one stored hop where backward `ask` reached the pair through the
  closure. `walks-its-own-conclusion?` now tests the one direction (`genls*`, which is
  reflexive, so the `P`-from-`P` closure rule is still declined), and the two chainers agree
  again. *Class:* **Additive**: a derivation the walk was suppressed from now lands and no
  answer is withdrawn — a KB with no `genl` edge between a declared-transitive predicate and
  a rule conclusion is untouched, the shipped ontology included.
  [docs/inference.md](docs/inference.md)

- **A `genlCx` edge arriving last re-joins a rule over the subtypes of what its antecedent
  names.** An edge that widens a context's view puts the facts it newly exposes back on the
  chaining agenda, enumerated from the predicates rules take as antecedents. That
  enumeration read each predicate's own extent, where matching **fans**: a rule on
  `(dog ?x)` is answered by a stored `(terrier Rex)` down the `genl` spec closure, and a
  rule on `(not (dog ?x))` by a stored `(not (animal A))` up it. So five sentences — two
  context edges, a `genl` edge, a fact and a rule — derived the conclusion in the arrival
  orders that wired the contexts before stating the rule, and in no other. The extents are
  read fanned by `genl` now, contravariantly for a negated antecedent, which is the pair
  `subsumption-seeds` already reads from the other side. A predicate outside the type
  hierarchy closes to itself, so a KB with no hierarchy under its rule antecedents pays
  nothing. *Class:* **Fix**. *Migration:* none; a KB that was loaded in an unlucky order
  gains the firings it was owed at its next `recover`.
  [docs/contexts.md](docs/contexts.md)

- **A `genlCx` edge arriving last restates the facts its widened cone newly exposes to a
  merge.** An equality applies where it is *visible*, so the context cone decides what a
  merge restates as much as the closure does — and the edge is the ingredient nothing
  keyed on. `(equals Tom Thomas)` in `Up`, `(mammal Tom)` in `Low` and `(genlCx Low Up)`
  agreed in four of their six arrival orders; in the two that wired the contexts last the
  record kept the spelling `Low` stored it under while every read from `Low` asked after
  the representative, so the fact was believed and answered no query, under either name.
  Migration now runs on the edge as well as on the merge and on the fact, over both cones
  and enumerated from the standing merges through the term index — so a KB that has merged
  nothing pays one set-empty test, and a derived edge runs the same arm an asserted one
  does. *Class:* **Fix**. *Migration:* none; a KB loaded in an unlucky order gains the
  restatements it was owed at its next `recover`.
  [docs/equality.md](docs/equality.md)

- **A rule reaching a merged term concludes once, at the elected spelling.** A merge
  retires a spelling without moving a label — supersession is deliberately not a forced
  OUT inside the fixpoint, since the twin is justified by the spelling it displaced — so a
  retired spelling that reached the chaining agenda drew a conclusion that stayed
  *believed* under a name no read asks after. `(equals Tom Thomas)`, a rule over
  `(mammal ?x)` and `(mammal Tom)` therefore believed both `(hasFur Tom)` and
  `(hasFur Thomas)` in the two arrival orders that put the fact behind the other two, and
  only `(hasFur Thomas)` in the other four. A superseded datum no longer fires a forward
  rule; the restatement is on the agenda beside it, and an un-merge re-seeds the revived
  spelling through the channel it already had. A defeated default still fires, which is
  the asymmetry that matters: a defeat is a label the conclusion inherits.
  *Class:* **Fix**. *Migration:* none; a conclusion under a retired spelling stops being
  believed, and the representative's was already believed beside it.
  [docs/equality.md](docs/equality.md)

- **A rule asserted after a predicate merge is restated under the representative, as one
  asserted before it is.** A `rewriteOf` between two predicates migrates the rules that
  reason over the retired one — `(birthplaceOf ?x ?c) ⇒ (knownPlace ?c)` becomes
  `(bornIn ?x ?c) ⇒ (knownPlace ?c)`, the original superseded and the twin carrying the
  inference. That ran for a rule already stored when the merge arrived and not for one
  written afterwards, so the rule door and the fact door disagreed about the same merge.
  The rule door restates on arrival now, and the twin joins the chaining agenda beside
  it. An individual-only merge still holds a rule back, which is the case rewriting a
  schema rather than ground content. *Class:* **Fix**. *Migration:* none; a rule written
  after a predicate merge is stored superseded with its twin believed, which is what the
  other arrival order already produced. [docs/equality.md](docs/equality.md)

- **A cycle through negation that runs through a `different` antecedent is refused in
  every arrival order.** The stratification walk started from the rules carrying an
  exception, and a rule whose only negative dependency is `different` carries none — so
  the same two rules were refused in one order and stored in the other, and a `genl` edge
  closing the cycle under stored rules was accepted. Both doors now start from every rule
  a negative edge leaves (`checks/negative-edge-rules`). *Class:* **Fix**. *Migration:* a
  KB holding such a pair keeps it; re-asserting either rule, or the edge, through the
  front door is refused `:not-stratified`.
  [docs/exceptions.md](docs/exceptions.md)

- **Equational rewriting: the critical-pair unifier follows a binding chain to its end,
  and `normalize` keeps an empty list.** A chain `?a → ?b → ?c` read `?b` as unbound and
  lost an identification, so a `:non-confluent` report could name a reduct with a variable
  left free; and `()` inside a term was rebuilt as `(nil)` whenever a rewrite rule was
  active. Stored belief was never affected. *Class:* **Fix**. *Migration:* none.
  [docs/equational.md](docs/equational.md)

- **A frame that names a class is refused before the name is resolved.** Every thaw the
  engine runs over a file — a store's logs and whole-file blobs, a dump's streams — goes
  through one door whose allowlist of class names is empty, so a frame naming one is
  refused `:disallowed-class` rather than loaded and built from. A dump frame is a field
  map and a log frame a positional vector, so nothing this engine writes states a class;
  a name in a file is a name something else wrote. The front door holds the same
  opinion: `check-encodable` probes a leaf's class through that same thaw, so a value
  whose only durable form is Java serialization is refused where it is written rather
  than one restart later. *Class:* **Refusal**: a sentence leaf of a class only
  `java.io.Serializable` round-trips — `java.time.LocalDate` and the other `java.time`
  locals, a `Throwable`, a joda `DateTime` — is refused `:not-encodable` at `assert`,
  and a file carrying such a value (or a record or deftype frame) is refused on the way
  in. *Migration:* write a date as the KB's own calendar term
  ([docs/time.md](docs/time.md)) or as a number or string; a `java.util.Date`,
  `java.time.Instant`, `java.time.Duration`, `java.util.UUID`, `java.net.URI`,
  `java.math.BigDecimal` and every array nippy has a type id for are unaffected. A store
  already holding such a leaf reads back under `taoensso.nippy/*thaw-serializable-allowlist*`
  only by exporting it with a build that predates this. *Breaks:* `assert` /
  `assert-many` / `load-text!` on such a leaf; `open-kb` / `import!` over a file that
  names a class [docs/storage.md](docs/storage.md),
  [docs/defenses.md](docs/defenses.md)

- **An EDN manifest is read under a byte bound.** `meta.edn`, `format.edn`, `report.edn`,
  `index.edn` and a machine's `catalog.edn` are the first thing read about a directory
  nobody has promised anything about — discovery probes every entry of the KB search path
  this way — and were read whole on the strength of a filename. One bounded reader now
  serves all of them, refusing past a megabyte by name; the bound is on the read rather
  than on the file's stated length, since `File.length` answers 0 for a FIFO. A store
  sentinel cut mid-write is refused too (`:unreadable-store`) rather than stamped with
  today's version, while an index's `layout.edn` reads the same damage as `:stale` and
  rebuilds — an index is a cache and records are not. *Class:* **Refusal**: a manifest
  over the bound, and a torn `records/format.edn`, are refused where they were read.
  *Migration:* none for a manifest of the size these hold; a directory refused this way
  is damaged rather than merely large. *Breaks:* `open-kb` on a store whose `format.edn`
  is truncated, `import!` / catalog discovery over an oversized manifest
  [docs/storage.md](docs/storage.md), [docs/defenses.md](docs/defenses.md)

- **A dump's chunk length is bounded before it is allocated.** The chunked stream read
  each chunk off a four-byte length the file states, so a crafted or torn length of two
  billion was a two-gigabyte allocation and a negative one an untyped throw. A length
  outside `[0, 256 MiB]` is refused `:truncated-dump`, naming the length and the bound.
  *Class:* **Fix**. *Migration:* none; the writer never produces a chunk near the bound.
  [docs/storage.md](docs/storage.md)

- **A served read's depth and wall clock may be lowered by a request and not raised.**
  `:max-depth` and `:max-ms` are held under `VAELII_MAX_QUERY_DEPTH` (256) and
  `VAELII_MAX_QUERY_MS` (30000); over either is **400** with `{:type :over-ceiling}`
  carrying the requested figure and the ceiling, and an anytime read naming no clock is
  given the ceiling's. Every op runs under the daemon's single write monitor, so a search
  a caller sized holds every other caller behind it — and 30 seconds is where the
  zero-dep client stops listening. The ceiling is applied in the op table, so the model's
  generated tool surface is held to it as well. *Class:* **Refusal**: a request naming a
  bound past the ceiling was served and is now refused. *Migration:* name a smaller bound,
  or raise the ceiling on the daemon (`0` lifts it). *Breaks:* `POST /op` and the
  `kb_*` tools for `:query`, `:query?`, `:argue`, `:why`, `:why-not`, `:search-tree`,
  `:compare-tacticians`, `:ask-within`, `:prove-within`
  [docs/operations.md](docs/operations.md), [docs/defenses.md](docs/defenses.md)

- **`ask`, `ask?`, `prove` and `provable?` take a bound.** A trailing option map —
  `{:max-ms n}` at the two registry doors (`ask-opt-keys`), `{:max-ms n :max-depth n}` at
  the two backward-chaining ones (`prove-opt-keys`) — bounds a read that until now
  terminated only on the data. A depth prunes, so its answer is complete for that depth; a
  clock suspends, and a clock these doors reach is `:budget-exhausted` rather than the
  prefix it stopped on, since a solution vector and a boolean have nowhere to say the
  answer is partial. `ask-within` / `prove-within` remain the doors that hand the prefix
  back with a `:status`. *Class:* **Additive**. *Migration:* none; every existing call
  shape answers as it did. [docs/api.md](docs/api.md)

- **The daemon holds `:ask`, `:ask?`, `:prove` and `:provable?` to its search ceiling.**
  Every op runs under the single write monitor, and these four had no bound to clamp — so
  a remote caller could hold every other caller behind an unbounded backward search. They
  join `search-bounds`: a `:max-ms` or `:max-depth` over the ceiling is refused
  (`:over-ceiling`, 400) as at `:query`, and a request naming *no* option map is padded
  out to the arity that has one, because absent `:max-ms` there is no clock rather than a
  smaller question. A search that reaches the clock answers 400 `{:type
  :budget-exhausted}`. *Class:* **Refusal**. *Migration:* a remote `:prove` or `:ask` that
  legitimately runs past `VAELII_MAX_QUERY_MS` needs the ceiling raised, or `0` to lift
  it; in process nothing changes, since a call with no option map is unbounded as before.
  *Breaks:* a served `:ask` / `:ask?` / `:prove` / `:provable?` taking longer than
  `VAELII_MAX_QUERY_MS` (30 s by default) now refuses where it ran on.
  [docs/operations.md](docs/operations.md)

- **The browser refuses a public bind with no token, and then requires it.** `lein run -m
  vaelii.web --listen <address>` without `VAELII_API_TOKEN` prints a line and exits **2**,
  where it warned and served; with the token set, every request to a public bind carries
  `Authorization: Bearer <token>` or is answered 401. The daemon already held this rule
  and now shares the fn that states it, so what a server binds decides what it requires
  on both. Loopback is unchanged on both — no token, no header, no 401.
  *Class:* **Refusal**: a browser that started on an address with no token no longer starts.
  *Migration:* set `VAELII_API_TOKEN` (and have the reverse proxy in front present it),
  or drop `--listen` and reach the browser over loopback.
  *Breaks:* `--listen`, `vaelii.web`
  [docs/operations.md](docs/operations.md), [docs/web.md](docs/web.md),
  [docs/defenses.md](docs/defenses.md)

- **A `find-terms` regex is bounded across the whole vocabulary, not only per term.** The
  per-candidate step budget catches a pattern that backtracks; a merely expensive one asked
  over a six-figure vocabulary spent the product of the two — on the daemon while holding
  the single writer, on a public browser bind through an unauthenticated `GET /find`. A
  second budget, a hundred times the first, now bounds the scan, and the refusal is the
  same `:pattern-too-costly` with `:scope :scan`. *Class:* **Refusal**: a pattern that
  reads more than a hundred million characters over one call ran to completion and now
  throws. *Migration:* narrow the pattern, or use `:prefix` / `:substring`, which read
  linearly. *Breaks:* `find-terms` `{:match :regex}`, `/find`, the daemon's `:find-terms`,
  `kb_find_terms` [docs/web.md](docs/web.md)

- **A `VAELII_ALLOWED_HOSTS` entry carrying a port matches the host it names.** The
  request's `Host` is compared with its port stripped and an allowlist entry was not, so
  `kb.example.com:8080` matched nothing and refused every request while the startup line
  reported the allowlist as set. Entries are host names; a port on one is read as the name
  alone, and a blank variable reads as unset. *Class:* **Fix**. *Migration:* none.
  [docs/operations.md](docs/operations.md)

- **A host-path read stays out of the model's tool set.** The reads-only sweep that turns
  daemon ops into model tools screened *mutation* — the `write-ops` roster and the `!`
  backstop — so a read whose argument names a **path on the daemon's host** slipped through:
  `:kb-diff`'s second side is a directory, and `kb_kb_diff` handed a prompt-injected model a
  host-filesystem probe. A `host-path-ops` set is now subtracted alongside `write-ops`, so
  `:kb-diff` is served for a CLI or daemon caller exactly as before but generates no model
  tool. *Class:* **Additive**: no served op changes shape and no public var moves — the
  model's tool set, derived from the op table, loses a read it should never have carried.
  [docs/llm.md](docs/llm.md)

- **A predicate is at most one of the three arity classifications.** CxCore declares
  `unaryPredicate`, `binaryPredicate` and `ternaryPredicate` pairwise `disjoint`, so a
  second classification of one predicate is refused where it is written (`:disjoint`)
  instead of being stored and convicted a step later — the two memberships each derived an
  `(arity ?p n)`, and `(functional arity)` was left arbitrating a contradiction the
  declarations had already made. Pairwise and not a `(siblingDisjoint predicate)` mark:
  `predicate`'s specializations are every classification of a relation there is, and a
  predicate is rightly several of those at once — `arity` is a `binaryPredicate` and an
  `instanceRelationPredicate` — so the mark would separate pairs that must coexist. The
  separation closes under `genl` like any other, so `(functional P)` beside
  `(unaryPredicate P)` is refused too. `kb-quality`'s `:clashes` reading drops the arity
  cycle from both directions: the class-to-arity rules by the disjointness on their
  antecedents, and the arity-to-class rules by a third joint-satisfiability rule-out — one
  term bound to two arities, which `(arity ?p 1)` beside `(arity ?p 2)` says outright and
  `(arity ?p 1)` beside `(equivalenceRelation ?p)` says by reaching `binaryPredicate` up
  `genl`. Nothing shipped is refused; the starter is 1,843 sentexes and the core
  vocabulary 392. *Class:* **Refusal**: a KB that declared one predicate two arity classes
  stored both and reconciled them under truth maintenance, and now the second declaration
  throws. *Migration:* declare one class, or `(variableArity P)` where the predicate really
  reads tuples of more than one length; a KB already holding both keeps them, a
  declaration arriving over stored content being reported by `exposed-clashes` rather than
  thrown at whoever wrote the second half.
  *Breaks:* `assert` / `load-text!` / `lein cli load` / `lein cli assert` on a second
  `unaryPredicate` / `binaryPredicate` / `ternaryPredicate` membership for one predicate
  [docs/taxonomy.md](docs/taxonomy.md), [docs/quality.md](docs/quality.md)

- **Every argument position the shipped contexts declare an arity for is typed, or excused
  by name.** Thirty-two `arg` / `genlArg` declarations join `CxCore` and `CxOrganism`: the
  predicate-property family (`transitive`, `functional`, `symmetric`, …) types its one
  position as a `predicate`, the function-property family as a `function`, `interArg`'s
  four open positions as two integers and two types, `contextArgSubrelation`'s three as a
  function, an integer and a predicate, and the two metatypes' members as types. What no
  argument type can name — the root's `genl` 2, `not`'s sentence, the `agg/*` operator
  slots, koinii's `(sentexHandle H)` mentions — is a roster in `ontology_test`, with the
  reason beside each, and a new gap or a stale excuse fails the suite. Nothing shipped is
  refused; the core vocabulary is 392 sentexes and the starter 1,843. *Class:* **Refusal**:
  a fact naming a non-predicate in a property slot, a non-integer in a position slot or a
  non-type in `interArg`'s type slots stored, and now throws `:arg-type` where it is
  written. *Migration:* none for well-formed content; a KB already holding such a fact
  keeps it, a declaration arriving over stored content being reported by
  `exposed-clashes` rather than thrown. *Breaks:* `assert` / `load-text!` /
  `lein cli assert` / `lein cli load` on `(transitive 42)`, `(interArg P "one" …)` and the
  like [docs/argtypes.md](docs/argtypes.md), [docs/kbs.md](docs/kbs.md)

- **An undeclared predicate's arity is the majority of its facts, not the first row.**
  The LLM inventory falls back to a stored fact for the arity of a predicate no `arity`
  and no `unaryPredicate` / `binaryPredicate` / `ternaryPredicate` membership declares,
  and it named that fact by position off `sentexes-with-functor` — which answers the SET
  of a functor's facts and promises nothing about the order, so a predicate written at
  two arities was reported at whichever one the index enumerated, which is the order the
  facts arrived in. The fallback now reads at most 64 of them and answers the arity most
  of them carry, a tie going to the smaller: a count and a number, both content, so the
  reading holds in every arrival order. `sort_by_content_key_test`'s positional-take scan
  covers the three extent reads (`sentexes-in-context`, `sentexes-with-functor`,
  `sentexes-with-arg`) alongside the match ones, so the next such read fails where it is
  written. *Class:* **Additive**: nothing public moves — the fallback is private to the
  inventory, and the arity that changes is one that had no fixed value to change from.
  [docs/llm.md](docs/llm.md), [docs/defenses.md](docs/defenses.md)

- **A map or a set anywhere in a sentence is refused.** Sentence content is EDN scalars
  and sequentials: `sentex/canon` gives a sequential one spelling and `nm/form-rank` one
  place in the content order, and a map or set gets neither, so two `=` sentences could
  freeze to different bytes and no tie-break could order them. `check-encodable` now
  refuses one under the `:not-encodable` it already uses for a value nippy cannot freeze,
  and the message says to write a sequential (a vector of pairs) or reify the structure
  as a term. *Class:* **Refusal**: a sentence carrying a map or set stored, and now throws
  where it is written. *Migration:* spell the value as a vector of pairs, or mint a term
  for it; a KB already holding one keeps it, stored content not being re-checked.
  *Breaks:* `assert` / `assert-rule` / `edit!` / `load-text!` / `lein cli assert` /
  `lein cli load` on a sentence with a map or set in any position
  [docs/storage.md](docs/storage.md), [docs/canonicalization.md](docs/canonicalization.md)

- **A bulk index load refuses (`:stacked-batch`) rather than overwriting what moved under
  it.** The in-memory backend's bulk-write path accumulates on a transient taken off a
  state atom held per *space*, and installed it with a `reset!` — so anything that
  reached that atom while the batch ran was discarded in silence, a second bulk load
  stacked over the first being the way there on one thread. The install is a
  compare-and-set against the value the batch snapshotted, and the accumulator is closed
  as it installs, so a binding conveyed out of the batch writes to the atom instead of to
  a spent transient. *Class:* **Refusal**. *Migration:* run one bulk load at a time over a
  space; a caller that nested two was already losing the inner one's entries.
  *Breaks:* a nested `with-bulk-writes` over one space now throws where it silently
  dropped the inner batch. [docs/storage.md](docs/storage.md)

- **Three option doors on the operational surface refuse a value they do not read.** A
  `/kbs` load form's choice parameter (a generator `base`, a corpus `profile`) is checked
  against the option's own choices; `lein serve`'s `--listen` refuses a following token
  that is itself a flag rather than binding an interface named `--port`; and the daemon
  client's `client` runs its option map through the same door every engine entry point
  uses, so `{:timeoutms 500}` no longer takes the 30 s default in silence — nor does a
  misspelt `:token` present the environment's credential. *Class:* **Refusal**: each of
  the three took the value and ran at a setting nobody chose. *Migration:* spell the
  option as the page, the flag or `client`'s docstring names it. *Breaks:* `/kbs` with an
  unknown choice value, `lein serve --listen <flag>`, `vaelii.client/client` with a key
  outside `:timeout-ms` / `:token`
  [docs/operations.md](docs/operations.md), [docs/catalog.md](docs/catalog.md)

- **The catalog refuses a misspelt `:belief?` and reads a blank search path as unset.**
  An unrecognised `:belief?` (`:store` for `:stored`) selected the records-only load —
  the one that never opens the justification stream — instead of reaching `import-dump`'s
  `:unknown-option`; and an exported-but-empty `VAELII_KB_PATH` was a search path of no
  directories, so `/kbs` reported a machine with no KBs. *Class:* **Fix**. *Migration:*
  none; a blank variable now means what an unset one does.
  [docs/catalog.md](docs/catalog.md)

- **One read answers "what can I ask about `X`?"** A term's arity, the types binding its
  arguments, its relation properties, its inverse, its place in the hierarchy, its extent
  count and the KB's own comment on it were eleven separate calls, and the risk in taking
  them one at a time was never that one of them was wrong — it was that the *assembly*
  was, and there were two assemblies: the browser's term page and whatever a caller wrote.
  `core/describe` is that assembly, keyed by the term's own `term-role`, so what comes back
  is shaped like what the term is: a predicate carries `:arity`, `:arg-declarations`,
  `:props`, `:inverse`, `:extent-count` and the four grants; a type carries
  `:predicates-for-type` — which predicates' argument declarations admit it — and
  `:instance-count`; an individual its `:types` and the predicates it appears under with a
  count each; a context its two `genlCx` cones and its `:sentex-count`. Every shape carries
  `:comment` and the three closure lines `:genls` / `:specs` / `:disjoint`. **It is
  scoped**: an `arg` declaration, a `modalPredicate` grant and a `comment` are each a policy
  of the context that states them, so they are read up the asking context's `genlCx` cone
  and `describe` at `CxCore` and at `CxWell` are two different, both-correct answers about
  one predicate. And **every list is a window with its size beside it** —
  `{:terms :total :exact? :sorted?}`, or `:rows` for a list of maps — because on an imported
  ontology one type has 110,000 subtypes and a truncated list handed over without its total
  is a false answer. The browser's term page now renders exactly what this returns and
  computes none of it a second time; `:describe` serves it, and `lein cli describe <term>
  [--context C]` is the shell spelling. *Class:* **Additive** — three new public vars, one
  new op, one new CLI command; nothing existing moves, and the term page's three lines read
  the same as before.
  [docs/api.md](docs/api.md), [docs/troubleshooting.md](docs/troubleshooting.md),
  [docs/web.md](docs/web.md)

- **`why-not` can say which rule nearly fired.** `:not-stored` is the emptiest answer the
  door has — nothing is stored, so there is no handle, no support and no defeat to report —
  and it is exactly the answer that arrives when a rule was *supposed* to conclude the goal.
  `(why-not kb sentence context {:nearest n})` runs a bounded backward search and reports,
  under `:nearest`, the n rules that came closest: each as `{:rule :rule-sentence :satisfied
  :missing :bindings}`, ranked by how many antecedents the KB can satisfy and written in the
  rule's own variable names, so `:missing` is the fact nobody asserted. It is **off by
  default** and stays off: `why-not` is cheap enough to call in a loop over a conflict list
  and a backward search per call is not. The bounds are `:max-depth` (3) and `:max-ms`
  (2000), both overridable, and `:nearest-search` says which of them bit — `:complete`,
  `:bounded`, `:timeout`, or `:refused` where the search would not start. The frontier is
  the **node engine's** whatever `*query-engine*` is bound to, which the answer states
  rather than leaving to be inferred: the DFS holds its unfinished proofs on the JVM stack
  and unwinds them as it fails, so a failed DFS leaves nothing to read, while the node
  engine's state is a value that outlives the search. A rule needing more rewrites than
  `:max-depth` allows is therefore not reported, and the bound in the answer is what says
  so. Over the daemon the existing `:why-not` op carries it with no table entry of its own —
  the op table `apply`s the `vaelii.core` var. *Class:* **Additive** — one new arity, three
  new public vars, one new CLI flag; the two existing arities answer exactly what they did.
  The CLI command takes a goal *or* a handle, and the flag belongs to the goal —
  a stored handle is stored, so `:not-stored` is not an answer it can get — so that pairing
  is refused rather than dropped, which is `check-flags!`'s rule one level in.
  [docs/api.md](docs/api.md), [docs/troubleshooting.md](docs/troubleshooting.md)

- **Two KBs can be compared as knowledge rather than as stores.** Two KBs holding identical
  knowledge share not one handle — handles are allocated in assertion order, so a reload
  renumbers everything — which is why a diff of records reports a KB loaded from its own
  export as wholly changed. `core/kb-diff` keys on **content** instead: the canonical
  sentence, its context and its strength, the same key `assert` dedups on. It answers
  `{:added :removed :moved :belief-changed}` — the four ways two KBs differ about one
  sentence — with `:moved` the same sentence at the same strength in a different context and
  `:belief-changed` one stored in both and believed in one, which is what a defeated default
  reads as and what a comparison of stored records cannot see at all. Premises and derived
  sentexes are compared alike, told apart by `:premise?` on every row, since a conclusion
  that stopped following is a difference even though nobody wrote it either time. Either
  side may be a **string** naming a text KB, read with `load-text!` into an in-RAM KB of its
  own, which is what `lein cli diff <a> <b>` is; the `:kb-diff` op takes a path on the
  daemon's host for the reason `:export` takes one. O(|a| + |b|), the smaller side indexed
  and the larger walked as a lazy seq. What it does not compare, said in the docstring so
  nobody reads more into an empty answer: justifications, provenance and handles.
  *Class:* **Additive** — one new public fn, one new op, one new CLI command.
  [docs/api.md](docs/api.md), [docs/operations.md](docs/operations.md)

- **Every refusal the tree raises is one a test provokes and a reader can look up.**
  `troubleshooting.md` closes with the whole `:type` vocabulary — every keyword an
  `ex-data` or a problem map can carry, a line each, with the page that owns the
  mechanism — so a keyword caught in a `catch` is never a dead end. A roster test walks
  `src/` for the vocabulary and `test/` for what asserts it, and fails on a refusal no
  test names or no page documents; the gap it opened is closed, so the suite
  discriminates on `:type` at every refusal it reaches, message text nowhere.
  *Class:* **Additive** — a documentation section and a test; no keyword moves.
  [docs/troubleshooting.md](docs/troubleshooting.md)

- **A refusal message names what it received and what it accepts.** Fifty-odd messages
  said only what class of thing went wrong and left the offending value in `ex-data`, or
  named the value and left the accepted set there — `no such tactician: :foo` without the
  four there are, `level must be 0-7` without the level. Each now carries both, and
  koinii's cursor-feed refusal is one line rather than a string literal broken across two
  source lines with the indentation inside it. No `:type` keyword and no `ex-data` key
  moves, so nothing that discriminates on one is affected. *Class:* **Fix**.
  *Migration:* none; a caller reading a message rather than a `:type` reads different
  prose. [docs/troubleshooting.md](docs/troubleshooting.md)

- **Two refusals name themselves where they threw bare.** A foreign-format manifest that
  does not read as EDN is `:bad-foreign-manifest` rather than the reader's own exception;
  a `VAELII_API_TOKEN` no HTTP header can carry (a trailing newline, a control character)
  is `:unknown-option` naming the variable, where the JDK's message quoted the token
  itself. *Class:* **Fix**. *Migration:* none.
  [docs/foreign.md](docs/foreign.md), [docs/operations.md](docs/operations.md)

- **`:unrecovered-kb` carries one shape at both doors.** The teardown refusal handed back
  `:hazards` as the raw map where `writable-problem` gives a sorted vector of keys, and
  carried no `:operation` / `:repair`; the two now agree, and `:unrecovered-premise`
  names its `:operation` too. *Class:* **Fix**. *Migration:* a caller reading
  `(:hazards ex-data)` off a refused `retract!` / `edit!` reads a vector of keys.
  [docs/storage.md](docs/storage.md)

- **The daemon serves the reads and writes the wire was short of.** Twenty-eight more
  `vaelii.core` fns are ops: abduction and the control that discards it (`:abduce`,
  `:abduce-discard`, filed with the writes — a hypothesis is minted through the whole
  assert pipeline into a scratch context, so it holds the single writer), the four-valued
  `:argue`, the knowledge readings (`:kb-quality`, `:quality-report`, `:vocabulary-audit`,
  `:settle-stats`, `:provenance`, `:add-provenance`), the anytime pair (`:ask-within`,
  `:prove-within`), the cached closures a query cannot reconstruct (`:genl?`,
  `:context-up`, `:context-down`, `:sees?`, `:has-prop?`, `:props`, `:inverse-of`,
  `:representative`, `:same-class?`, `:equiv-class`, `:deprecated?`), the whole-KB
  enumerations (`:handles`, `:contexts-of`, `:canonical-sentex`) and the ones that take
  no KB at all (`:levels`, `:calculi`, `:readable-sentence` and `:quality-report`,
  rostered as `serve/kbless-ops`). Two results are shaped for the wire rather than passed through:
  `:handles` answers a sorted vector, the roster a store hands back having no EDN print
  form, and the anytime pair drops `:resume` — a function over an in-memory tail — for
  **`:resumable`**, a boolean, `core/resume` being in-process only. The five lifecycle
  fns stay off the wire with the reason stated per fn: `import!`, `recover`, `reindex`,
  `clear!`, `close!`. *Class:* **Additive**: every op is new, no served op changes shape,
  and the three new writes are declared in `llm.tools/write-ops` so the model's tool set
  is still reads only.
  [docs/operations.md](docs/operations.md)

- **Every daemon op has a client wrapper, and the op table is what says so.**
  `vaelii.impl.client` carried thirty-three hand-written wrappers against ninety-nine ops
  and spelled two of them `assert!` / `assert-rule!` where `vaelii.core` spells them bare,
  so the promise `docs/operations.md` made — the wrappers mirror the `vaelii.core`
  surface, bare and `!`-marked exactly as it spells them, arity for arity — was true of
  the third of the surface somebody had got to. `lein regen-client`
  (`vaelii.regen-client`) now reads `serve/ops`, resolves each op in `vaelii.core` and
  writes one wrapper per op between two markers in `vaelii.impl.client` and
  `vaelii.client`; a hand-written wrapper in the public shim wins, so prose written for
  one survives a regeneration. Generated at build time rather than macroexpanded from the
  table, because requiring it would put the engine, jetty and reitit on the classpath of a
  namespace whose whole point is not needing them. `client_surface_test` compares both
  files against what the generator would write now — so an op added to the daemon reds the
  suite until the wrapper is written — and asks the claim in both directions: every op has
  a wrapper spelled as `vaelii.core` spells the fn, and every wrapper names an op.
  `vaelii.client`'s `assert` / `assert-rule` / `genls` / `specs` gain the arity each was
  short of. `assert!` and `assert-rule!` stay as **deprecated** aliases.
  *Class:* **Additive**: vars and arities are added, none removed and none changed; the
  two `!` spellings still resolve and still answer, and `test/golden/api-surface.edn`
  moves only by growing.
  [docs/operations.md](docs/operations.md)

- **The engine's content order is public.** `vaelii.core/sort-by-content` orders a
  collection by a key under the engine's own structural comparator — the one its internal
  orders use, which walks the two keys instead of printing them (so no ambient `*print-*`
  var can elide two keys to one, and 9 sorts before 10) and builds the key once per
  element rather than once per comparison. Order independence is a property callers share,
  not only the engine: an application ranking its own answers has the same tie to break,
  and breaking it on a handle — allocated in assertion order — makes the ranking a fact
  about how the KB was loaded. koinii is the first caller; publishing this is what let it
  stop reaching into `vaelii.impl.naming`. *Class:* **Additive**. [docs/api.md](docs/api.md)

- **The content order's last-resort branch stops reporting distinct values as equal.**
  `compare-form` ranks the kinds a sentence is built from and walks two of the same kind;
  everything else — a map, a set, a record — fell to `(compare (str a) (str b))`, and `str`
  on a collection honours the ambient print bounds. So under a REPL's `*print-length* 3`
  two four-entry maps compared **0**: a comparator answering "equal" for values that are
  not, in the one branch whose whole job is to leave no pair uncompared, which is both a
  broken `Comparator` contract and exactly the arrival-order fallback the structural order
  exists to remove. It prints through `print-key` now, which releases the bounds first.
  Unreachable from sentence content, which is why it went unseen; reachable from a caller's
  key, which the newly public `sort-by-content` invites. *Class:* **Additive** — the
  affected pairs previously compared equal or in a print-dependent order, so no caller
  held an order over them that this can break. *Migration:* none.
  [docs/nmtms.md](docs/nmtms.md)

- **A KB writes the text format it is authored in.** `export-text!` writes a KB's premises
  as one `Cx<Name>.txt` per context — the format the shipped ontology under `resources/kb/`
  is written in, the file name naming the context — and `load-text!` reads a file or a
  directory of them back through `assert`. Premises only and at no handles, each keeping its
  `:strength` and each rule its `set/*Rule` wrappers and its `exceptWhen`, so a reload yields
  the same canonical sentexes at the same strengths and the same beliefs. Content-ordered and
  carrying nothing about the run, so the same knowledge always writes the same bytes.
  `(set/monotonic S)` is the one thing the format spells that `assert` does not read.
  *Class:* **Additive** — two new public fns (`vaelii.core/export-text!`,
  `vaelii.core/load-text!`), a new `--format text` on `lein cli export`; no existing
  behaviour changes. *Migration:* none. [docs/api.md](docs/api.md), [docs/kbs.md](docs/kbs.md)

- **`kb-quality` reads the rules against each other.** Two readings beside the five, both
  static analysis of the rule set rather than of what the KB believes. `:subsumption`
  names the stored rules another stored rule already covers — one substitution making the
  covering rule's antecedents a subset of the covered rule's and its consequent the covered
  rule's conclusion, predicate-genl aware in both halves and in opposite directions, with
  the covering rule required to be at least as available (direction, defeasibility,
  `assumption` / `constraint`, no `exceptWhen` the covered rule lacks) and visible from the
  covered rule's context. `:clashes` names the rule pairs whose conclusions would
  contradict each other if both fired — `S` against `(not T)` where `S` entails `T`, two
  type conclusions a disjointness separates, two values for one `functional` slot, one
  tuple concluded both ways under an `asymmetric` predicate — scoped to a context that can
  see both rules, with joint satisfiability decided shallowly off the antecedent sets and
  no fact consulted. A pair one rule already states as an `exceptWhen` is reported under
  `:excepted` rather than hidden, so a reader sees which clashes are handled. Neither is a
  gate and neither retracts anything. *Class:* **Additive**: two new keys on
  `kb-quality`'s map and two new sections in `quality-report`, both written only when the
  key is there, so a stored report from before them still renders; no public var changes
  and `test/golden/api-surface.edn` does not move.
  [docs/quality.md](docs/quality.md)

- **A stored claim that contradicts a known-true inherited claim is reported.** A
  `{:strength :monotonic}` claim carried down `genl` by `transitiveInArg` is not undercut
  by a nearer contrary one — `inherit`'s own docstring calls that "a contradiction to
  report rather than a refinement to defer to" — and nothing reported it: the `:opposed`
  coincidence set holds bodies stored in *both* polarities, and here one side is a claim
  with no handle, so the pair reached neither `conflicts` nor `contradictions` and `ask?`
  answered false at the subkind with no reason a caller could read. `settle` now forms the
  nogood, whose members are the stored claim together with everything the reading rests on
  — the general claim, the declaration, the relation edges, and any `(transitive R)` or
  `(symmetric …)` behind it — so `decide-nogood` weighs it as it weighs any other and the
  weakest member decides: a reading that is known-true throughout defeats a `:default`
  contrary claim and the general claim reaches the subkind, a reading resting on a
  `:default` declaration or edge is a represented dilemma believed on both sides, and a
  clash of known-true claims is an irreducible one. The report carries `:kind :inherited`
  and an `:inherited` map naming the claim nobody stored, the sentex it was read off and
  the `genl` path it travelled, so `why` can explain a report about a sentence the KB does
  not hold. Retracting the general claim, the edge or the declaration withdraws it, and the
  edge arriving last reports the same pair as the edge arriving first.
  *Class:* **Additive**: a report where there was none, and one new key on one new `:kind`
  of clash entry — no public var moves, `test/golden/api-surface.edn` does not move, and a
  KB that declares no argument preservation is told so by one `empty?` on a roster kept at
  the store choke points, so nothing is added to the assert path it pays for.
  [docs/inherit.md](docs/inherit.md), [docs/nmtms.md](docs/nmtms.md)

- **An `exceptWhen` states a strength per half.** An `exceptWhen` asserts two things —
  the rule, and the exception qualifying it — and `assert` takes one `opts`, so its
  `:strength` reached both. That says three of the four rule × exception pairings and
  could not say the fourth: a **known-true exception on a default rule**. `export-text!`
  wrote that one as `(set/monotonic (exceptWhen Q R))`, which a reload read as known-true
  on *both* sides, so the rule came back one defeat class stronger than it went out.
  `(exceptWhen (set/monotonic Q) R)` states the exception's own class; `assert` reads it
  and `check` reports the same `:shape` refusal for a wrapper written round the wrong
  number of queries. The wrapper is peeled before the split, so nothing below the door —
  the naming checks, the alignment, the store — sees a sentence it did not see before.
  The text writer emits whichever of the four spellings reproduces the pair: the outer
  wrapper only where both halves are known-true, the query wrapper where only the
  exception is, and the rule again on a line of its own where only the rule is,
  `mark-premise` resolving a premise asserted twice to the stronger. All four now
  round-trip byte-identically and belief-identically.
  *Class:* **Additive**: a spelling where there was none — a `set/monotonic` in that
  position was refused as a literal before — and the three pairings that could already be
  written are written the same bytes, so only the fourth's export changes, from lossy to
  lossless.
  [docs/exceptions.md](docs/exceptions.md)

- **A fork answers the tally samplers itself and forwards the prefetch hint.** A fork's
  record store now implements `Tallying` — the three samplers prefer the fork's own
  record and never name a handle the merged view dropped, the two tallies are the honest
  merged count — and both overlay decorators forward `Prefetching` to a base that has it,
  so opening or recovering a fork over a durable base no longer enumerates the base to
  answer "is there anything here". *Class:* **Additive**.
  [docs/overlay.md](docs/overlay.md)

- **`{:max-ms nil}` is accepted under an instrumented budget.** A second `s/def` of
  `::max-ms` on the option-map side redefined the anytime budget's own `(s/nilable
  nat-int?)`, so an instrumented `why-not` or `ask-within` refused the unbounded spelling
  both document. One keyword, one spec. *Class:* **Fix**. *Migration:* none.
  [docs/anytime.md](docs/anytime.md)

- **`plan/*enabled*` false drops the cost ranking and keeps the readiness discipline.**
  It short-circuited the whole of `plan-pairs`, so the switch documented as "a pure cost
  decision — it must never change the answer set" also removed the two placements that
  are not cost: a deferred literal behind what binds its arguments, and the recursive
  literal last. Unranked, `[(bigEnough ?n) (hasScore ?x ?n)]` computed the check on
  nothing and answered empty, and a rule whose antecedents were written recursion-first
  lost its deferred pull-forward. `partition-literals` and `ready` now run either way and
  only the generator ranking is behind the switch, which is what the docstring claimed.
  Found by the sweep below on its first run. *Class:* **Fix**. *Migration:* none;
  `plan/*enabled*` is `vaelii.impl` and its true root is unchanged.
  [docs/inference.md](docs/inference.md)

- **The planner's `est-matches` is one-sided everywhere it is read.** `prefix-estimate`
  charged an average — the prefix count over its child count — once the walk reached a
  token the block had already bound, so a literal that fans out could read as matching
  once and `:prune?` rested on it; the estimate now stops at the first non-literal token
  and returns the prefix count, and the narrowing a bound variable buys stays where the
  join model already computes it. Ordering only: every block is emitted exactly once, so
  no answer moved. *Class:* **Fix**. *Migration:* none.
  [docs/indexing.md](docs/indexing.md)

- **A `:put` or `:delete` on an argument-root key inside a `kv-batch` applies on every
  backend.** The in-memory backend holds `[:argument-root pred pos term]` in a counted
  trie rather than as a flat key, and its batch fold answered only the two set ops — so a
  batch a flat-map adapter applied was refused `:unknown-frame` there, one adapter
  disagreeing with the others about what one op means. The fold now routes both to the
  same two functions the protocol methods use, and the `KvBackend` contract spec covers
  the family in both folds. *Class:* **Fix**. *Migration:* none.
  [docs/indexing.md](docs/indexing.md), [docs/storage.md](docs/storage.md)

- **The disk record store's resident state is written under the monitor its files are
  written under.** Three threads touch that store — the writer, the durability daemon and
  a compaction — and the live-id set, the record cache, the compaction delta set and the
  failure flag were each mutated a step outside the kind lock that guarded the file write
  they belong to, so a reader could find an id live whose slot said tombstone, or a
  cleared delta set under a writer folding a handle into it. The handle counter,
  `counters.nippy` and the stamp saying what that blob holds move together too, under a
  monitor of the store's own: a daemon tick straddling a `clear-records!` left a wiped
  store stamped with the pre-wipe high-water mark. *Class:* **Fix**. *Migration:* none.
  [docs/storage.md](docs/storage.md)

- **The two snapshot protocols are pinned extension seams.** `SnapshotSink` and
  `SnapshotSource` are what an out-of-tree image store implements — `vaelii-postgres`'s
  `pg-sink` / `pg-source` and `vaelii-sqlite`'s `sqlite-sink` / `sqlite-source` each
  supply both — so both are frozen in `test/golden/spi-protocols.edn` beside the other
  seams: adding a method to either is Breaking, and a removed or reshaped one shows up in
  a diff rather than at an implementer's call site.
  *Class:* **Additive**: a roster entry and four golden lines, no method moves.
  [docs/storage.md](docs/storage.md)

- **Both readings of an index posting are named, and the raw read is refused.** Every
  `IndexStore` posting is storage — it holds a defeated default, a conclusion whose
  support was withdrawn and a spelling an equality retired — so a read of one carries a
  question, and read straight off the protocol a forgotten belief filter and a deliberate
  as-stored read are the same three characters. `vaelii.impl.reads` asks it in the name of
  the read: `as-stored-…` / `stored-count-…` take the index store, `believed-…` take the
  KB and filter with `jtms/in?`. A door is a wrapper and never a rewrite — one call to the
  protocol method it names, the same laziness and count-aware path — so it adds no index
  operation and `assert_cost_test`'s pinned counts do not move. `lein lint`'s new **E16**
  fails a raw index read anywhere under `src/` but the implementers, whose roster lives in
  that check; `RecordStore` is outside it, a record being the storage itself. Four readers
  that read as stored without saying so now say why: the generator roster behind the
  stratification refusal, the `comment` audit, and `kb-quality`'s two rule extents.
  *Class:* **Additive**: no public var changes and no answer moves — the doors wrap the
  reads their callers already made.
  [docs/nmtms.md](docs/nmtms.md)

- **A global taxonomy closure read says `-global`.** `genls` / `specs` / `genl?` carried
  the unscoped read as their shorter arity, so a caller reached it by leaving the context
  off — and since `visible-ctxs` hands back the global closure itself for any reader that
  sees every asserting context, the two agree on most KBs and differ only once somebody
  restricts an edge. Each is now two vars: the scoped one takes the context, and
  `genls-global` / `specs-global` / `genl?-global` say what they walk. `raw-context-up`
  becomes `context-up-global`, for `genlCx` the scope being the except filter itself.
  `lein lint`'s new **E17** rosters the 35 deliberate global callers as `(file,
  definition)` pairs — the public API's own unscoped arity, the assert-time refusals, the
  forward join, the re-check triggers, settle's candidate discovery, the visibility filter
  that cannot be scoped by what it derives, and the whole-taxonomy report — so a new
  global read is a decision somebody wrote down. *Class:* **Additive**:
  `vaelii.impl.taxonomy` is not a public namespace, `vaelii.core/genls` / `specs` /
  `genl?` keep both arities and both answers, and `test/golden/api-surface.edn` does not
  move.
  [docs/taxonomy.md](docs/taxonomy.md)

- **koinii is an app in the tree, not a corner of the engine.** The coordination layer
  moved from `vaelii.impl.koinii.*` to `vaelii.koinii.*` — `src/vaelii/koinii/`, beside
  `impl/` rather than inside it — because that is what it always was: eight modules built
  on the public API and the thin `vaelii.client`, requiring nothing from the engine's
  internals. It sat under `impl/` only by where it was first written, and the path said
  "internal" about something whose whole design claim is that it needs no privileged
  access. The one place that claim was not true is closed: `adjudication` reached into
  `vaelii.impl.naming` for the content order its two ranked reads (`contested-premises`,
  `standing-rulings`) use, and takes the published `sort-by-content` instead. The move
  changes no behaviour and no koinii function's spelling. *Class:* **Additive** — the six
  public namespaces are unchanged, and `vaelii.impl.*` is free to move without notice, so
  no pinned surface moved with it. Anything requiring the old namespace renames the prefix.
  [docs/koinii.md](docs/koinii.md), [docs/namespaces.md](docs/namespaces.md)

- **A multi-claim reply goes through the same doors a single one does.** `channel/assert`
  refuses three things before it writes — a write aimed at the admin-only `CxRegistry`, a
  `:creator` that disagrees with the handle's agent, and a speech act naming anyone but
  that agent as its speaker — and `reply-many` built its batch and committed it without
  any of them. Both spellings of "say something" now call one `check-write-doors`, applied
  to every sentence before the first write lands, so the batch is settled on identity as
  well as on admissibility. What the gap allowed was not theoretical: `tally` reads a
  voter off the ballot's own sentence, so one agent could cast a second agent's vote and
  carry `resolve-by-majority` into a monotonic ruling; and the registry — the one context
  koinii says the governed may never write (D4) — took `(trustLevel …)` from an
  unregistered principal. *Class:* **Refusal** — a batch that forged a speaker or aimed at
  the registry wrote knowledge attributed to someone who never said it, which no query
  could tell from the real thing. *Migration:* none for an honest caller.
  *Breaks:* `:koinii/speaker-mismatch`, `:koinii/creator-mismatch`, `:koinii/registry-forbidden`
  [docs/koinii.md](docs/koinii.md)

- **An agent context is marked as one, and a join refuses to graft under it.**
  `channel/join` lifts an agent's context under the channel it names and asked nothing
  about that parent, so naming another agent's context grafted one agent's writes under
  another's: every cone read of the host returned the guest's claims as the host's, and
  with `belief/believe-own` in force the host *believed* them. The parent is checked now
  (`:koinii/not-a-channel`), against a fact rather than a shape: `identity/place-agent-context`
  — the one chokepoint `join`, `identity/agent-context`, `speech-acts/speaker-context` and
  the arbiter placement all pass through — writes `(agentContext CxAtlas AgentAtlas)` into
  the agent's own context, which is the context D8 already grants it, so recording the role
  needs no privilege the agent lacks. It has to be written rather than inferred, and that is
  the load-bearing part: `context-for` maps an agent to its context by dropping a prefix, so
  an agent context is spelled exactly like a channel, and the placement edges are the
  ordinary wiring of any nested context. A door reading the lattice's shape would admit or
  refuse the same channel depending on what else had landed — order dependence in an
  admission check. It **fails open** on a context placed before the mark existed; placement
  is idempotent, so the mark lands the next time that agent joins. *Class:* **Refusal** — a
  graft under another agent's context made one agent's claims indistinguishable from
  another's at every reader above it. *Migration:* a deployment that nested channels or
  rolled one up into another is unaffected; only a parent that is an agent's own context, or
  the registry, is refused. *Breaks:* `:koinii/not-a-channel` [docs/koinii.md](docs/koinii.md)

- **The contested-premise flag reads the conclusion the way the asker proves it.**
  `adjudication/contested-premises` resolved its conclusion with exact-context `handle-of`
  while scoping disputes up the `genlCx` cone, so the two halves asked different questions:
  a conclusion provable from the reading context but *stored* below it — which is where
  forward chaining places one derived from an agent's own premise — resolved to nothing and
  the read answered `[]`. Not "no dispute found" but "nothing contested", from the flag a
  high-stakes reader checks before trusting a derived answer, about a conclusion resting on
  a premise two agents were actively disputing. It resolves through the cone now
  (`sentexes-matching` filtered by `sees?`, the scoping `disputes-in` already used) and
  unions the support closures across every sentex the asker can see, so there is no
  tie-break to get wrong and the answer covers whichever derivation replied. The union is
  linear in the number of contexts holding the same sentence — a few microseconds per
  co-asserter, on a per-answer flag. *Class:* **Additive** — no working caller can observe
  it except where the old answer was wrong, which is the one place it changes.
  *Migration:* none; a caller that saw an empty list for a conclusion stored below its
  reading context now sees the contested premises.
  [docs/koinii.md](docs/koinii.md)

- **A reaped subscription spends the same catch-up budget a lag does.** `catchup/sync!`
  bounds re-snapshotting so a consumer that cannot keep up surfaces
  `:koinii/catchup-thrashing` rather than re-reading the whole context forever, and the
  `:unknown-subscription` arm incremented that counter without ever testing it. A daemon
  whose idle window closes between every open and the poll that follows answers that reply
  every time, so `sync!` never returned. Both replies draw on the one counter, because what
  the bound protects is the re-read work and it costs the same whichever condition asked
  for it — two budgets would let a pass alternating between them run to twice the ceiling
  with each half looking well behaved. The refusal names which condition spent the budget
  in a new `:condition` key (`:lagged` / `:unknown-subscription`): different faults,
  different fixes, one bound. *Class:* **Refusal** — the arm returned by not returning.
  *Migration:* a caller matching on `:koinii/catchup-thrashing` still matches; `:condition`
  is additive. *Breaks:* `:koinii/catchup-thrashing` [docs/koinii.md](docs/koinii.md)

- **A malformed marker is answered, not thrown.** `deref/dereference` resolves a payload
  that arrived over a transport from a peer, and its whole contract is that the marker is
  never trusted — only resolved against what the seat itself holds. A malformed one reached
  `v/handle-of` unchecked and came back out as the *engine's* `:shape`, so a garbage or
  hostile peer crashed the receiving seat's resolve path instead of being told "I do not
  hold that". The payload is gated first, and the engine's own request-shape refusals are
  translated rather than escaping: the answer is `{:resolved? false :reason :malformed
  :problem …}`, where `:problem` names the part — `:not-a-map`, `:locator`, `:no-sentence`,
  `:no-context`, or the engine keyword verbatim. The sentence itself is deliberately not
  validated against the current KB: a record stored before a declaration arrived would fail
  that check while the seat genuinely holds and believes it, and refusing to dereference a
  record the seat has is worse than the throw. `resolve-by-locator` had the quieter half of
  the same hole — a non-locator string answered `:not-received`, telling a garbage peer it
  was merely out of sync — and now decides before building its index, so an unparseable
  string costs no walk. *Class:* **Refusal**. *Migration:* a caller matching `:not-received`
  on a malformed marker sees `:malformed`; a well-formed marker for a sentence the seat does
  not hold still answers `:not-received`. A locator mangled in its `sha256:` tag now reads
  `:malformed` where it read `:locator-mismatch` — the digest never parsed, and reporting a
  mismatch implied a comparison that never happened. [docs/koinii.md](docs/koinii.md)

  *Breaks:* `dereference`, `resolve-by-locator`

- **A koinii registry read refuses two rows rather than naming one by position.**
  `set-trust!`, `trust-of` and `display-name-of` read through one gate that throws
  `:koinii/registry-not-functional`, naming every handle, when more than one believed row
  stands. `trustLevel` and `displayNameOf` are `functional`, so a second row is refused at
  assert; the gate states the invariant every registry read rests on instead of resting
  on the order retrieval enumerated a set in. *Class:* **Refusal**: a registry that ever
  held two rows was silently halved by whichever came first, and the overwrite retracted
  that one. *Migration:* none for a well-formed registry; one holding two rows names them
  in the refusal. [docs/koinii.md](docs/koinii.md)

  *Breaks:* `set-trust!`, `trust-of`, `display-name-of`

- **koinii: a dispute is named by every handle in its clash.** `dispute-term` read a
  nogood as a pair, so the three-member clash an `antiTransitive` chain forms collapsed
  onto the term of its two lowest handles — and the `:notified` / `:stale` marks keyed
  on that term retired one dispute when another was marked. *Class:* **Fix**.
  *Migration:* none for two-member disputes (the term is unchanged); a three-member one
  gets a term of its own.
  [docs/koinii.md](docs/koinii.md)

- **A catch-up poll that fails untyped is refused as `:koinii/feed-error`, a word the
  rosters can see.** The default was computed rather than written — a `:type` whose value
  was a form — so the two refusal rosters, which read the sources for a keyword literal
  inside an `ex-info`, counted the keyword as belonging to no vocabulary at all: neither
  held to having a test nor to having a row a caller can look it up in. The default is a
  literal now and the transport's own `:type` is laid over it, so the observable refusal
  is unchanged and the word is on the surface. *Class:* **Fix**. *Migration:* none.
  [docs/troubleshooting.md](docs/troubleshooting.md)

- **A documentation example that is a whole program is run by the suite.** A fenced
  `clojure` block carrying `run` in its info string is evaluated by
  `doc_examples_test`, in a scratch namespace with `v` and `starter` aliased and stores
  of its own, and a comment following a form whose text begins with `=>` is checked
  against what that form returned. Nothing else evaluates a doc block — the doc lint
  reads the pages as text and asks only whether a block balances — so an example naming
  a fn the engine does not have reads as current for as long as nobody pastes it. The
  marker is opt-in because almost every block in `docs/` is a fragment, not a program.
  *Class:* **Additive** — a fence marker and a test; no engine surface moves.
  [CONTRIBUTING.md](CONTRIBUTING.md)

- **The OpenCyc counts in the documentation are one cited reading rather than five
  independent ones.** [docs/kbs.md](docs/kbs.md) states the load it measures — the
  `units/5022` conversion at the `:ontology` profile, on the JVM's default heap — and
  every other page cites that reading instead of quoting a count of its own, so the
  type count is one figure with a source named rather than four that disagree. Where a
  figure has no source anywhere in the tree it is dropped and the argument it supported
  is kept. *Class:* **Fix** — documentation only.
  [docs/kbs.md](docs/kbs.md), [docs/quality.md](docs/quality.md)

- **The suite scans itself for assertions that cannot fail.**
  `vacuous_assertion_test` reads the test sources for four shapes — an equality whose
  two operands are the same text, an `is` on a literal, a disjunction over a value and
  its negation, and a bound that holds for every count — and fails naming each. Four
  such assertions are fixed with it, including a scenario-enumeration prefix compared
  with itself where the claim was that it survives a reordering of the same facts.
  *Class:* **Fix** — a test that reported a pass it had not earned now reports what it
  checks. [CONTRIBUTING.md](CONTRIBUTING.md)

- **`lein lint` fails on a git conflict marker in a tracked file.** A merge resolved by hand
  can leave a marker behind — most easily the diff3 base line, seven pipes and a commit hash
  — and nothing scanned for one, so a leaked marker (and the dev hash the base line carries,
  which the project keeps out of tracked text) rode a green `lein gate` and `lein
  release-gate` into a squash. `scripts/lint-conflict-markers.sh` greps the tree for the
  open, base and close markers — never the bare separator, which at a line start is a
  Markdown heading rule — as the tenth `lein lint` check. *Class:* **Additive**: a gate that
  fails only on content no tree should hold.

- **The release's class check reads all four classes.** `lein check-siblings` refuses an
  entry whose `*Class:*` word it cannot place, because a word nothing recognises is read
  as Additive by everything downstream and the class is what decides the release number.
  **Fix** is the fourth class CONTRIBUTING §3.8 names and the check places it: like
  Additive it owes neither a `*Breaks:*` line nor a `*Migration:*` line, since a Fix
  retires no name a sibling could be grepped for. Breaking and Refusal owe both, and a
  misspelt class — `Braeking` — is refused. *Class:* **Additive**: one release step reads
  one more word.

- **`lein bench-subgoal` measures whether a cross-query subgoal table would be hit, and
  it is not.** `matches-visible` answers survive a query in a clock-stamped per-KB cache
  and `solve-goal` answers do not; the harness counts every registry dispatch over the
  fables' question set, the shipped worked examples, a rule-expanding
  `query`/`prove`/`escalate` pass, one render of the inference debugger and a koinii
  conversation, keyed the way such a table would have to key them, then replays the
  sequence with a prototype table switched on and off in one JVM. Over the sequence asked
  once, 15.2% of solves repeat inside a call and 2.7% across calls; the replay reads
  1.05x on one pass and 1.01x once a single assert falls between passes, because the
  change clock is global and one mutation retires every entry. The reading and the reason
  are in the inference page as an absence. *Class:* **Additive**: a new `bench-*` alias
  and its namespace, nothing public moves and no golden shifts.
  [docs/inference.md](docs/inference.md)

- **`VAELII_PLAN=0` runs the whole suite with the cost ranking off, and the matrix
  runs what a change owes rather than everything.** Reordering a conjunction is a cost
  decision that must never change the answer *set* — the claim `VAELII_HIER` makes for
  retrieval and `VAELII_QUERY_STRATEGY` for goal ordering — so it is checked the way those
  are: a sixth sweep, failing-set-identical and assertion-count-identical against a plain
  `lein test`, where `plan_test` afforded twelve randomized trials. Put to the suite the
  claim did not hold unqualified: four tests pin the ranking back (`tu/pinning`,
  `tu/with-pinned`) rather than stand aside, two of them because the ranking is what
  supplies an answer — a registered evaluatable's placement, and where the event calculus
  stops. docs/inference.md carries both with their witnesses, so what the sweep does not
  cover is written down rather than silent. The third such case is the entry above, which
  is fixed rather than pinned — a pin is the second choice, for where the alternative
  genuinely has no answer to give. Alongside it, `test-matrix.sh` takes the group
  words `backends` / `sweeps` / `routine` / `full`; a bare run is the **routine** roster,
  twelve of the fourteen, with the two durable-records-with-a-derived-index pairs that
  repeat one claim standing down and named on every header and verdict; `--owed` runs
  only the configurations the changed files owe, from the map in
  `scripts/lib/suite-configs.sh`, printing the classification per file; and `-n` prints
  that set without running it. *Class:* **Additive**: one test-harness switch and four
  script arguments, no door moved. [docs/inference.md](docs/inference.md),
  [docs/operations.md](docs/operations.md), [docs/storage.md](docs/storage.md)

- **The contracts that need two JVMs are tested with two JVMs.** Four claims the engine
  makes about a *process boundary* had no test that crossed one: the single-writer lock
  refusing a second writer (`tryLock` **throws** inside one JVM and returns nil across
  two, so the only reachable single-process branch was the other one, and the real
  diagnosis was pinned as a string), the OS dropping that lock when a writer is killed,
  a KB opened cold over a directory another process wrote (two KBs over one directory
  *share* the durable store in-process, and every process-global cache survives a
  `close-dir!`, so an in-process "restart" cannot see a durable value that was really
  RAM), and a daemon and a CLI contending for one directory. `vaelii.multi-jvm` forks
  `java -cp` on the test JVM's own `java.class.path` and handshakes on a marker line;
  `vaelii.multi-jvm-test` holds the four, and a source scan fails the *default* suite if
  a forking test is added without the mark. *Class:* **Additive**: a test mark, a
  selector and an alias; no engine door moved.
  [docs/storage.md](docs/storage.md), [docs/operations.md](docs/operations.md)

- **`^:multi-jvm` is opt-in, and `:all` no longer adopts whatever mark is added next.**
  A third mark joins `^:slow` and `^:llm`, deferred for forking a process rather than
  for cost or for dialing out, and it is the first that **no** selector reaches by
  accident: `lein test`, `lein test :all` and `lein gate` all pass over it, and `lein
  test-multi-jvm` and `deep.yml`'s job are what run it. `:all` was
  `(complement :llm)` — a complement of one mark silently adopts the next one added,
  which is how a forked JVM would have landed in the fast gate — and names both marks
  now. *Class:* **Additive**: one selector, one alias, one CI job.
  [docs/operations.md](docs/operations.md)

- **A bare keyword is not a test selector, and `lein test :llm some.ns` ran the whole
  suite.** Leiningen passes the tokens after a selector *to* it, so `:llm` as its own
  selector fn was `(:llm var-meta "some.ns")` — a lookup with a **default** — and every
  test whose metadata lacked the key matched on the namespace name. The suite ran in
  full, reported green, and looked like the one namespace had been slow. Every selector
  is a `(fn [m & _] …)` now, which is what the comment beside them already prescribed for
  the arity reason. *Class:* **Fix**. *Migration:* none; `lein test :llm` alone was
  always correct. [docs/operations.md](docs/operations.md)

- **The matrix dashboard alternates a command line with a bar, and stops walking down
  the screen.** Every row carried its bar inline, and the aggregate row carried the
  absolute log directory as well — 107 columns, which wraps on any terminal narrower
  than that. A wrapped row is two screen rows where `BLOCK` counted one, so the
  `\033[<n>A` that repaints the frame moved up one row short every second and the
  dashboard left a trail of itself. Now a bar shares its line with nothing: a running
  configuration shows **the command that runs just that configuration** and its log file
  after the `#`, then its bar on the next line. Widths are measured rather than assumed
  — bars are sized from the text beside them, `…` elides a path at a separator and keeps
  its tail, and `BLOCK` is counted from the rows actually painted — and a frame too tall
  for the terminal falls back to the compact one-line rows rather than painting a broken
  one. The size those widths are measured against is now the **terminal's**, asked of
  `/dev/tty`: `tput` reads it off its own stdout, and every one of these scripts is
  reached through lein-shell, which pipes — so a matrix under `lein` had been laying
  itself out for terminfo's default 80 by 24 whatever the window actually was. The mark
  rows `test-backends` and `test-sweeps` print widen with it. *Class:* **Fix**.
  *Migration:* none; `SUITE_PROGRESS=lines` still forces the scrolling form.
  [docs/operations.md](docs/operations.md)

- **The exhaustive truncation sweep runs once rather than once per configuration, and
  in a couple of minutes where scratch space is cheap.** The every-offset sweep in
  `vaelii.truncation-fuzz-test` was `^:slow`, so `lein test-matrix :all` ran it in every
  row — and `subjects` names its own four durable backends and never asks for the one
  the row is testing, so fourteen rows walked the same 9,717 offsets for one answer. It
  now carries `^:fuzz`, which **no** selector reaches: `lein test-fuzz` and `deep.yml`'s
  job run it, and the sampled twin still runs at `:default` so the harness cannot rot
  between them. Read that as a real drop in how often the sweep runs, not only in what
  it costs: it was every `:all` run and thirteen deep rows, and it is now one weekly job
  that blocks nothing.
  Measured, the cost was never the bytes and never the recovery: 92% of a probe is the
  open-and-close pair, an *empty* directory with nothing to truncate costs the same
  60 ms as a real probe, and the same probe against RAM-backed storage costs 9 — the
  sweep was paying one device cache flush per offset. `VAELII_TEST_TMPDIR` names the
  scratch directory and CI points it at `/dev/shm`: ~10 minutes to under two, over the
  same offsets, asserting the same things. It stays **serial**, which is a finding
  rather than an omission — `F_FULLFSYNC` serializes at the device (four workers on APFS
  measured 0.96× one), and where concurrency does pay, 2.7× on a RAM disk, a sharded
  sweep makes a green run print at `:error`. What it provokes is benign and already
  handled: `durability.clj` documents the window a close under a queued auto-compaction
  opens, its registry check is the early skip, and the record store throws on its closed
  idx before a temp or a marker is written. Nothing is written and nothing is lost — the
  defect is only that the catch-all reports that outcome at `:error` beside real
  failures. So the last 30% is waiting on a log reclassification, not on a lock.
  *Class:* **Additive**: a fourth test mark, a selector, an alias and one test-only
  switch; no engine door moved and no offset was dropped.
  [CONTRIBUTING.md](CONTRIBUTING.md), [docs/operations.md](docs/operations.md)

## 0.12.0 — 2026-08-23 — "query contexts, bulk loading, and a literal's type"

- **`resultIsa` and `resultGenl` are `result` and `genlResult`.** The argument-constraint
  family lost its `*Isa` spellings when `argIsa` became `arg` and `argGenl` became
  `genlArg`; the result family, which mirrors it one level over, kept them. It reads
  `result` / `genlResult` now — the bare name for the instance claim and the `genl`-prefixed
  one for the subtype claim, the same pair `arg` and `genlArg` make. The two comments also
  stop saying "the output of the **reifiable** ?function": both readings hold for both
  kinds of function, and the reifiability mark decides only *where the type is held* — a
  reifiable function's application mints a constant and carries `(?type K)` on it, an
  unreifiable one is typed from the declaration at check time. *Class:* **Breaking** for a
  KB or a tool that names either predicate. *Migration:* rename every occurrence —
  `resultIsa` → `result`, `resultGenl` → `genlResult`. The old names are gone rather than
  deprecated, and nothing reports one: an undeclared predicate stores clean, so a
  declaration still naming `resultIsa` constrains nothing and says nothing about it.
  [docs/nat.md](docs/nat.md)

  *Breaks:* `resultIsa`, `resultGenl`

- **The four function marks classify what they mark, and the reifiability criterion is
  written down.** `reifiableFunction`, `unreifiableFunction`, `quotingFunction` and
  `contextDenotingFunction` each say what happens to a function's *applications* and
  never said the term was a `function` — so `function` was a type the shipped KB put
  nothing in, and `(disjoint function predicate)` reached the three declarations naming a
  function-valued argument and not one term. Each mark now carries
  `(genl <mark> function)`, the shape every algebraic property mark already had
  (`(genl functional binaryPredicate)`). What that buys immediately: `(predicate FatherFn)`
  is refused as a disjointness rather than admitted; `(result parentOf T)` is refused,
  a predicate not being a function; and `(arg QuantityFn 1 number)` is refused instead of
  stored and left inert — the arg family constrains predicates, nothing reads it for a
  function's own argument positions, and the KB says so at the door. The two reifiability
  comments also state the criterion they are chosen by, which was recorded nowhere:
  **boundedness of the application space.** Reification stores one constant per distinct
  application and keeps it, so it is safe exactly when the applications are bounded —
  `(FatherFn Muffet)` is one per animal. A measure function is not and never is:
  `(QuantityFn 5 Meter)`, `(QuantityFn 5.001 Meter)` and every magnitude between run over
  the reals, which is why `QuantityFn` and `QuantityIntervalFn` are `unreifiableFunction`
  and stay structural for a prover to compute. *Class:* **Refusal** for a KB that marks
  one term both a function and a predicate, or that declares an `arg` / `genlArg` /
  `quotedArg` on a function. *Migration:* such a declaration constrained nothing before
  and constrains nothing now — drop it. A term genuinely holding both marks was already
  two things at once; keep the one its applications behave like.
  [docs/nat.md](docs/nat.md)

  *Breaks:* `reifiableFunction`, `unreifiableFunction`, `quotingFunction`, `contextDenotingFunction`

- **The faster reading of an unnamed context agreed with the reference in five fewer ways
  than it claimed.** `CxInference` — and a variable context, which is every short arity —
  answers by one of two strategies that must not differ, and a review of the pair found
  that they did. A three-literal join that outgrew its row budget **threw**: the bail
  crossed three nested reduces wrapped for two, so the goals-reduce took the bare sentinel
  as its next partial-solution set and reduced over a keyword. A literal that stopped being
  index-only once the join bound it — `(t ?a)` is answered by the stored-fact prover,
  `(t Ind)` also by the argument-type one — was answered with less, because the domain gate
  was asked of the goal as written and the placement pass reads only the index. A goal
  naming a **merged** term was answered for the wrong reader or the wrong binding: goals
  are rewritten by the merges *their* reader sees, so a context above a `sameAs` asks a
  different question, and one unscoped pass cannot have built its answers — that read goes
  to the fan now. A `CxEverything` walk **left its closure behind** for the next ordinary
  read, the reach cache having been keyed without the belief mode; the three sites that
  build that key are one `closure-key` function now, since they have to agree — the
  per-search-step neighbour memo is deliberately not one of them, its belief mode being
  constant for its whole life, and keying it would put a dynamic deref in the walk's
  innermost loop. And a rule
  whose consequent was `(ist CxNothing S)` **stored into it** — the chainer being the one
  door that places without asserting, and `nm/context?` saying yes to all three query
  contexts by design. *Class:* **Refusal** for that last one — such a firing drops its
  conclusion and is recorded like any other dropped one — and a **Fix** for the four
  above it. *Migration:* none —
  every case answered wrongly, threw, or wrote where nothing may be written.
  [docs/contexts.md](docs/contexts.md)

  *Breaks:* `ist`

- **A records read stays lazy, and a proof's witness is one of its bindings.** Two more
  from the same review, both of them ways the new reading changed something it was not
  meant to touch. `sentexes-matching` promises a seq that fetches what it is asked for, and
  making the default context the joint reading turned it into a **realized vector** — every
  reader asked before the caller saw element one, so `(take 5 …)` paid for the term's whole
  neighbourhood across every context. Nothing there needs that: a records read has no
  witness to maximize, so unlike a bindings read there is no point at which it must have
  seen every reader before it can answer at all. It is driven one reader at a time again,
  and a `take` stops at the reader that supplied the last element it wanted. The `readers`
  seed is still paid up front — which contexts can answer is not knowable lazily — and the
  docstring says so now rather than promising otherwise. Separately, a `{:proof? true}`
  answer is `{:bindings … :proof …}`, and the witness was attached **beside** those two
  rather than among the bindings: invisible to `(:bindings answer)`, which is where a
  caller looks for a binding, and with the check that stops an already-bound `?ctx` being
  overwritten reading a key that is never there. A variable witness goes inside `:bindings`
  now; `CxInference`'s `:context` stays beside them, being a side channel by construction.
  *Class:* **Fix**. *Migration:* a caller that had found the witness at the top level of a
  `:proof?` answer reads it from `:bindings` with every other binding; nothing else moves,
  and a bare-bindings answer is unchanged. The grouping `:proof?` gets is left as it is and
  documented instead — two proofs of one binding keep a witness each, which is the reading
  a proof asks for. [docs/api.md](docs/api.md)

  *Breaks:* `:proof?`

- **Three reads that could not answer the question answered empty instead.** Each is a
  door taking something it cannot honour and returning nothing rather than saying so, which
  is the failure the query-context door exists to prevent, found in three places it had not
  reached. A goal spelling **`?ctx`** was captured: retrieval unifies the sentex's context
  slot against that symbol, so a goal variable spelled the same way was unified with the
  context rather than with the argument it stands in — `(p ?ctx ?b)` came back `{?ctx CxA,
  ?b Y}`, the first argument's binding silently replaced, and the witness check that would
  have caught the mismatch reads a binding already gone. Naming the context variable
  something else was never a workaround; the marker is fixed. A **compound context that
  does not reify** was read at: `(CxTimeFn ?t)` is not ground and `(CxBogusFn Q)` is not
  declared, so neither names a context, and a read at something that names no context finds
  nothing — looking exactly like a true negative. The write side already refused both; the
  read side takes more shapes, a variable and a query context among them, and so had no
  check at all rather than a wider one. And the two **network reads** answered a structure,
  so a query context came back `{:nodes [] :consistent? true}` — not merely empty but
  positively reassuring, an unsatisfiable KB and a way of reading rendered identically.
  *Class:* **Refusal**, all three. *Migration:* rename a goal variable spelled `?ctx`, or
  name a context to read in — at a named context there is no marker to collide with and
  `(p ?ctx ?b)` answers correctly, unchanged; give a context-denoting application its
  declaration and its ground arguments; and name a real context to the network reads.
  [docs/contexts.md](docs/contexts.md)

  *Breaks:* `?ctx` `qualitative-network` `possible-relations`


- **A literal argument is typed by what it is, and `arg` now says so.** `(arg P n dog)`
  admitted `(P "Bob")` and `(P 5)` without complaint: the definitional checks exempted
  every non-symbol, on the stated grounds that a type membership cannot be *asserted* of a
  literal. True, and beside the point — `checks/literal-type` reads a literal's EDN kind,
  and those kinds sit in the `genl` lattice precisely so the comparison can be made. A
  string is a `string`, a `string` is not a `dog`. The openness moves rather than
  disappearing: it attaches to the **declared type**, so a `t` outside the hierarchy still
  exempts and a **symbol** is open-world exactly as before, and a **compound** is the one
  leaf shape no *kind* answers for — its function's declaration is what answers it, which
  the entry below reads and [docs/defenses.md](docs/defenses.md) argues out. CxCore gains
  `keyword`, `boolean` and `character` beside `string`, `number`, `integer` and `symbol`,
  one per leaf kind a sentence can carry, so no kind is waved through for want of a name;
  `quotedArg` types against all seven. *Class:* **Refusal** for a sentence putting a
  literal in a position typed against something its kind does not reach. *Migration:* none
  for a stored KB — `recover` replays content rather than re-checking it — but such a
  sentence is refused on re-assert. Widen the declaration to a type the kind reaches
  (`intangible` covers every literal), or drop it.
  [docs/argtypes.md](docs/argtypes.md)

  *Breaks:* `:arg-type`, `:quoted-arg-type`

- **A result declaration binds the applications its function never mints.** `result`
  and `genlResult` typed only what a **mint** materialized, so they worked for a
  `reifiableFunction` — whose application reifies to a constant carrying `(T K)` before
  the checks see it — and did nothing whatever for an `unreifiableFunction`, whose
  application stays a compound all the way through. `(result QuantityFn measure)`
  stored clean, read back identically to a working declaration, and let
  `(needsDog (QuantityFn 5 Meter))` through under
  `(arg needsDog 1 dog)`, while the identical declaration on a reifiable function refused
  the identical claim: one declaration, two verdicts, decided by whether its function
  happened to mint. `checks/args-problem` and `genls-problem` read it at check time now —
  `arg` against `result` (what an application **is**), `genlArg` against `genlResult`
  (what it is a **kind of**), never crossed. Open-world one level out from the symbol
  reading: a function declaring no result exempts every application of it, exactly as an
  unclassified symbol exempts itself, and a declared result the asking context cannot
  place under `thing` exempts too. Context-scoped like every definitional check, so a
  declaration a context cannot see does not refuse it — where the **mint** keeps reading
  globally, materializing into `CxUniverse` where every reader sees the result. A
  declared result stays a claim about the **function**: no per-application type is
  computed and nothing is minted. `disjoint-problem` still skips a compound — its
  `:opposing-handle` is the conflicting membership's own handle, and a declaration about a
  whole function is not one. *Class:* **Refusal** for a sentence putting a function
  application in a position typed against something the function's declared result does
  not reach. *Migration:* none for a stored KB — `recover` replays content rather than
  re-checking it — but such a sentence is refused on re-assert. Widen the declaration to a
  type the result reaches, drop the `result` / `genlResult`, or write the argument as a
  term. [docs/nat.md](docs/nat.md)

  *Breaks:* `result`, `genlResult`, `unreifiableFunction`, `:arg-type`, `:arg-genl`

- **An attitude is opaque: the asker's merges stop at the proposition.** `(believes
  Oedipus (marriedTo Oedipus Jocasta))` plus a `(sameAs Jocasta MotherOfOedipus)` the
  *asker* holds answered `(believes Oedipus (marriedTo Oedipus MotherOfOedipus))` **true**
  — an entailment nobody has, since the agent does not hold the identity — while a merge
  the *agent* holds licensed nothing at all. A `modalPredicate`'s proposition is a mention
  now, held opaque to identity congruence in the one walk migration and query share, and
  the projection normalizes it against the agent's own partition instead. The agent slot, a
  non-sentence argument and an ungranted predicate all stay transparent, and a `rewriteOf`
  spelling rename still reaches into the quotation. *Class:* **Breaking** — a caller
  relying on the old answer was relying on an unsoundness. *Migration:* to get the
  substitution, assert the identity in the agent's context, where it is the agent's belief;
  a `genlCx` edge from the agent to the context holding the merge does the same for every
  merge that context states. *Breaks:* `believes` `modalPredicate`
  [docs/belief.md](docs/belief.md)

- **One vocabulary for the literal types, and `character_string` is retired.** The KB
  carried two unconnected hierarchies for the same values: `string` / `number` / `integer`
  / `symbol` in CxCore, which `quotedArg` types a term against, and `character_string` in
  CxAbstract, which `arg` typed a referent against — with `integer` the only term anybody
  had noticed sat in both. The distinction they were standing in for is real, but it is
  carried by *which declaration you write*: `arg` reads what an argument denotes and
  `quotedArg` reads the term written there, and a string literal denotes itself, so both
  ask one set. A second spelling bought nothing and cost a trap —
  `(quotedArg P n character_string)` stored clean and convicted nothing, `quotedArg`
  reading a type outside the syntactic lattice open-world, with no report anywhere. So
  `character_string` is gone; CxCore's four literal types carry comments of their own and
  CxAbstract places two of them, `(genl string intangible)` and `(genl number intangible)`,
  with `(disjoint string predicate)` and `(disjoint number predicate)` replacing the two
  narrower pairs. `symbol` deliberately gets neither: a symbol does not denote itself, so
  a name is exactly how a predicate is written and the disjointness would be false.
  `(arg comment 2 …)` also stops being a forward reference from CxCore into an upper
  theory. *Class:* **Breaking** for a KB that names `character_string` — in a declaration,
  a rule, or a stored membership. *Migration:* rename every occurrence of
  `character_string` to `string`. The old name is gone rather than deprecated.
  [docs/argtypes.md](docs/argtypes.md)

  *Breaks:* `character_string`

- **A rule's shared variables are held to the argument constraints of every position
  they stand in.** `args-problem` reads a ground argument and every argument of a rule is
  a variable, so a rule feeding a text-valued binding into a type-valued slot stored
  clean and was convicted a conclusion at a time, by a complaint naming the conclusion
  and never the rule. `checks/check-variable-constraints!` runs on both storage doors and
  in `check`, and refuses the new `:arg-variable` when two constraints on one variable
  demand disjoint types; a position counts as type-level when a `genlArg` names it or
  when its predicate is a `typeRelationPredicate`, which is what constrains `genl`'s
  second argument. CxAbstract separates the literal types from `predicate` — text and a
  number are each a thing no relation is — so `(implies (comment ?x ?string) (genl ?x
  ?string))` is refused rather than stored.
  CxCore gains `(disjoint function predicate)`, which its `function` comment has always
  stated in prose and the KB never held, so `(implies (result ?f ?t) (genl ?f ?t))`
  is refused too. A rule a **mint** stamps out — a generator's fill, a `defn*` fact's
  companion rule — is held to the same check and dropped with an `:arg-variable` entry
  in `violations` rather than thrown, the derivation path's discipline.
  *Class:* **Fix.** *Migration:* a KB holding such a rule keeps it; a rule
  re-asserted through the front door is refused, and the refusal names the variable.
  [docs/taxonomy.md](docs/taxonomy.md)

- **A torn justification stream tears the import.** Only the sentex stream was checked
  against its manifest count, so a truncated `justifications.nippy.stream` read as a
  clean EOF and lost belief with no witness; both streams are counted now, and every
  non-terminal exit closes the frame stream it was reading. *Class:* **Fix.**
  *Migration:* none. [docs/operations.md](docs/operations.md)

- **An unsupported `:compression` is refused at the sink.** `wrap-output` wrote plain
  nippy under a manifest naming the codec; it now throws `:unsupported-compression`,
  mirroring the read side. And a compaction copy that moves fewer bytes than the
  original holds throws `:short-transfer` instead of installing a truncated file.
  *Class:* **Fix.** *Migration:* none. [docs/operations.md](docs/operations.md)

- **A generated corpus is the same corpus however it is read.** The generator deduped
  facts on the sentence alone, so `:contexts` above 1 spread the plan over more contexts
  without the KB holding more sentexes — and its three lazy streams shared one `Random`,
  so realization order changed the corpus. Deduplication keys the `[sentence context]`
  pair and each stream owns a seeded generator; a corpus generated under either fix
  differs from one generated before it. *Class:* **Fix.** *Migration:* regenerate any
  saved generated corpus a comparison depends on.

- **The ASP backend frees what a failed solve leaves.** A native clingo `Control` leaked
  when block loading threw, and program temp files parked in the JVM-lifetime
  delete-on-exit hook; both are cleaned on the failure path itself now. *Class:* **Fix.**
  *Migration:* none. [docs/asp.md](docs/asp.md)

- **The STP closure cache keys the tolerance its verdicts were read to.** The closed
  network is cached on the network *value*, which is sound across queries because the
  network is derived from the believed facts — but both of `close`'s verdicts are read to
  `*quantity-tolerance*`, a dynamic var a caller may rebind for a coarser or finer policy,
  and the magnitudes are on the grid before the cycle check is made, so the network alone
  does not record which band it was decided in. A read under a rebound tolerance was
  answered with the verdict reached under the ambient one. The tolerance rides in the key:
  one number, constant for a whole query loop. And the six shipped algebras are held to
  their laws — converse involution, composition closure, the identity, the converse
  interchange, Peirce's law, distributivity over union — which 509 of 512 single-cell
  mutations of the RCC-8 table fail. *Class:* **Fix.** *Migration:* none.
  [docs/stp.md](docs/stp.md), [docs/qcn.md](docs/qcn.md)

- **A firing that subsumed under a negation names the edge it climbed, and an edge
  arriving after the facts reaches it.** The two things a subsumption match owes beyond
  the match — a `genl` witness on the justification (`chain/subsumption-links`) and a
  re-seeding of the facts a late edge newly makes matchable
  (`special/subsumption-seeds`) — both read a bare functor, which is `not` for every
  negation there is. So a conclusion derived through the contravariant fan outlived the
  edge it rested on, and the same three sentences derived it in one arrival order and not
  the other. Links now pair on the antecedent **key** (`rules/antecedent-key`) and read
  the direction off its polarity; the seeds read a negated antecedent's new facts up
  `super`'s `genl` closure, gated on some rule actually reading a negation under `sub`.
  *Class:* **Fix.** *Migration:* none. [docs/inference.md](docs/inference.md)

- **A portfolio races the tacticians it names.** Re-pointing an already-normalized
  strategy at another tactician by `assoc` kept the first one's signs — `tactics/strategy`
  lets an explicit sign win over the tactician's, which is what "name a tactician and bend
  one term" needs — so every racer ran the base ordering under a different name and the
  bet had nothing to win. `tactics/with-tactician` is the swap that says which side wins.
  Answer sets are unchanged, which is why no completeness sweep could see it.
  *Class:* **Fix.** *Migration:* none. [docs/inference.md](docs/inference.md)

- **An inferred argument type is read from the asking context.** `ArgTypeProver` types a
  term from how it is used, and read the usages globally while reading the declarations
  scoped — so a reader that could not see `(eats Muffet Bone1)` still learned from it that
  `Bone1` is food. Both halves are scoped now. *Class:* **Fix** — a context answers fewer
  type goals, and each one it drops rested on a fact it cannot see.
  *Migration:* none. [docs/contexts.md](docs/contexts.md)

- **`prove-within` carries `:max-term-growth`.** The bound is on the budget roster, so
  `check-budget!` admitted it — and the door then built a bounds map of its own that did
  not name it, so a caller raising the DFS's term-growth ceiling was answered under the
  shipped one with nothing to say the raise had not been read. It reaches the prover
  through `budget/prove-bounds` now, which is the translation the roster was written
  beside for exactly this reason. *Class:* **Fix** — a budget key that was accepted and
  ignored now takes effect; a caller that never named it is unaffected, the shipped
  ceiling being what an unnamed one already meant. *Migration:* none.
  [docs/anytime.md](docs/anytime.md), [docs/inference.md](docs/inference.md)

- **Subsumption runs under a negation, the other way.** `(genl dog animal)` has always put
  a stored `(dog Muffet)` under the pattern `(animal ?x)`; the same edge now puts a stored
  `(not (animal Muffet))` under the pattern `(not (dog ?x))`, because `¬animal ⊑ ¬dog` is
  the contrapositive of `dog ⊑ animal`. It reaches every site the positive fan reaches: the
  trigger match, retrieval, both chainers through `res/subsuming-unify`, and which rules an
  arriving negation triggers. A negative literal fans its **body's** functor over `genls`
  where a positive one fans over `specs` (`res/super-predicates` beside
  `res/sub-predicates`, one definition each so the reference matcher and the rete alpha
  matcher cannot drift), and the two directions stay exclusive: `(not (dog Muffet))` still
  says nothing about `(not (animal ?x))`, since a non-dog may be any other animal. No
  taxonomy state and no index key carries it — every negated conclusion was already filed
  under one `not` bucket, and the negated *antecedent* key is unchanged. The trigger side
  is where the cost would have landed, so it enumerates from the live `:rule-antecedents`
  roster rather than from the spec closure: an arriving `(not (thing X))` would otherwise
  probe the rule index once per type in the KB, and a KB whose rules read no negation pays
  a map read and probes the rule index not at all. *Class:* **Additive** — a query that
  answered nothing now answers, and nothing stored changes shape; a KB with a rule on a
  negated antecedent does derive conclusions it did not, which is the point.
  *Migration:* none. [docs/inference.md](docs/inference.md),
  [docs/exceptions.md](docs/exceptions.md)

- **A negated `exceptWhen` conjunct is re-checked in both directions.** The filter that
  decides which of a rule's firings a trigger could have reached compares the trigger's
  predicate against the conjunct predicate's `specs` closure; under a negation the
  conjunct is *also* answered contravariantly, by a negative fact on a `genls` of its
  predicate, so a negated conjunct now takes the union of the two. Without it a firing
  whose exception an arriving negation newly blocks is filtered out of its own re-check
  and the conclusion stays believed: with `winged ⊑ appendaged` and an exception
  `(not (winged ?x))`, asserting `(not (appendaged Opus))` left the conclusion standing.
  Over-approximating is the safe direction throughout that filter — an extra candidate is
  a re-check that changes nothing, a missing one is a lost withdrawal. *Class:* **Fix.**
  [docs/exceptions.md](docs/exceptions.md)

- **The exposure sweep debits its budget once, and its empty gate runs first.**
  `exposed-clashes` walked every stored sentex to collect the terms it would probe and
  only then asked whether the KB separates any two types at all — a whole-store read taken
  to be told there is nothing to say, and the one whole-store walk in that namespace. The
  three set-emptiness reads come first. And `clash-candidates` carried the revisit and the
  touched halves forward with their overlap intact, so a declaration reached twice was
  paid for twice against one exposure budget and could be filed as cut short over content
  the first pass had already swept; `touched` drops what `revisit` already names, a
  membership test apiece. *Class:* **Fix** — a cost one, and a budget that reaches as far
  as it is sized to. *Migration:* none. [docs/nmtms.md](docs/nmtms.md)

- **`argue` explains a side a rule derived, not only a side the store holds.** A verdict
  reached by rule expansion was reported as provable and left unexplained: `:for-why` and
  `:against-why` read the JTMS, which has nothing to say about a conclusion no sentex
  holds, so an adjudicating caller saw evidence for a stored side and silence for the
  other — in the `:contradiction` case, silence for exactly the half under dispute. The
  search's own derivation now comes back beside them under **`:for-derivation`** /
  **`:against-derivation`**: `query`'s `{:proof? true}` tree, the same value that door
  returns. Two keys rather than two shapes of one, because the two explanations read
  differently (`:goal` / `:via` / `:because` against `:sentence` / `:informant` /
  `:support`) and answer different questions — a belief record against a search trace. A
  derivation needs a positive `:max-depth` and a ground sentence, and is a **fallback**:
  where the JTMS answers, the search is not run. *Class:* **Additive** — no existing key
  changes shape or drops, and a side carries at most one of the two.
  *Migration:* none. [docs/api.md](docs/api.md), [docs/inference.md](docs/inference.md)


- **Not naming a context no longer means the union.** A **variable** context — `?ctx`, the
  default of every short arity, or any name you choose — is the *joint* reading: the answer
  must hold from some one reader's `genlCx` cone, and that reader is unified into the
  variable. A conjunctive read therefore refuses to join a fact in `CxA` to a fact in `CxB`
  when no context sees both, which is an answer no reader of the KB has. The union is
  `CxEverything`, asked for by name. **One exception:** a goal whose every literal is
  *computed* rather than matched (`different`, `evaluate`, `unknown`) rests on no stored
  fact, so there is no witness to pick and it is read whole-KB; a *mixed* goal needs none,
  its matched literals deciding which readers can answer. Both halves are argued in
  [docs/defenses.md](docs/defenses.md). *Class:* **Breaking** for a conjunctive read that
  relied on the union, and for any caller comparing whole answer maps from a read that
  passes a variable context (the witness is now among the bindings). *Migration:* pass
  `CxEverything` for the union, or a concrete context to scope the read.
  *Breaks:* `?ctx`
  [docs/contexts.md](docs/contexts.md)

- **Three query contexts: `CxEverything`, `CxInference`, `CxNothing`.** `Cx…` symbols that
  name a *way of reading* rather than a place, filling the one row of
  [docs/from-cyc.md](docs/from-cyc.md) that had no spelling here. `CxEverything` reads the
  store as stored, belief ignored — the cheapest question the engine takes, and the only
  one that sees a defeated default. `CxInference` keeps only what a single reader's
  `genlCx` cone sees over the **whole derivation**, where the default `?ctx` is existential
  *per literal* and so will join two facts no one context sees; the reader that covered it
  comes back as `:context`. `CxNothing` sees no fact at all, leaving the provers.
  All three resolve at the read door and reach no further; asserting into one is refused,
  as is any `genlCx` edge naming one. The doors that resolve one are `query`, `ask`,
  `prove` and `sentexes-matching`, with the `?` variants that delegate to them; every
  other read refuses `:unsupported-context` and names those four, rather than handing the
  symbol to the engine as an ordinary concrete context nothing is asserted in and
  answering **empty** — a wrong answer that looks like a right one. An `(ist Ctx S)` goal
  rescues such a call, the named context winning as it always does. *Class:* **Additive**
  — nothing about an existing read moves, `?ctx` included. *Migration:* none.
  [docs/contexts.md](docs/contexts.md)


- **`CxInference` is answered two ways, and the bounded one is the default.**
  `vantage/*strategy*` says which: `:fan` (the reference) enumerates the readers and asks
  each one the ordinary scoped question, and `:post-hoc` asks once unscoped, carrying what
  each answer rested on, and places it afterwards. The two owe the same answer set, which
  `vantage_differential_test` holds them to over generated lattices, so the choice is pure
  cost. `:post-hoc` is the default because it is **bounded** rather than faster: it prunes
  a partial solution whose ingredients already have no common descendant, and gives up past
  `lattice contexts × *rows-per-reader*` rows — 20 by default — after which the fan answers
  whatever was abandoned. Which of the two wins is a fact about the data rather than about
  the lattice, and [docs/defenses.md](docs/defenses.md) carries the measurements that say
  so. Neither is an option on a read door: they are a var to rebind in a benchmark or a
  differential test, as `res/*hierarchical-retrieval*` already is. *Class:* **Additive** —
  the answers do not depend on the strategy, only what they cost does. *Migration:* none.
  [docs/contexts.md](docs/contexts.md)

- **A placement is held to what a reader could have answered.** Post-hoc asks once
  unscoped, so it sees the KB with every reader-scoped filter off and has to put them back
  by reasoning about the *placement* rather than about the read — and it was putting back
  none of them. Four divergences from the fan, each found by asking for one. The `genl`
  edges a match subsumed through are an ingredient of the answer, so a reader that sees
  `(pup_t Rex)` and not `(genl pup_t hound_t)` does not answer `(hound_t ?x)` — the same
  call the forward chainer makes for subsumption support, because the two have to reach
  one verdict. The exceptions: `matches-visible` at `?ctx` runs where the hidden set is
  empty by construction, so a placement landed in the very context that excepts one of its
  facts. The retired spellings: supersession is per reader, so a placement below an
  equality merge sees both a fact and the twin migrated there. And the witness rule:
  maximality is a property of a **binding**, so two derivations of one binding may not
  keep two witnesses — which hid behind the `?ctx` `match-one` unifies into every binding,
  making one binding two keys until the placement projects onto the goal's own variables.
  Post-hoc's domain is also asked of the prover registry rather than read off the
  literal's shape, which does not say: `(gp0 ?a ?b)` and `(genl aa_t ?x)` are one shape
  and only the second walks a closure. *Class:* **Fix** — the two strategies agree, which
  is what makes the default a cost decision. *Migration:* none.
  [docs/contexts.md](docs/contexts.md)


- **The enumerations promise a `java.util.Set`, and a store may compress it.**
  `sentex-ids`, `justification-ids` and `premise-ids` now say what a caller may do with the
  answer — `contains?`, `count`, `seq`, `sort`, `=` against another set — rather than that
  it is an `IPersistentSet`, so a caller wanting `conj` / `disj` / `clojure.set` converts
  with `(set …)` at the site that wants them. The shape is what costs at scale, and
  `vaelii.impl.roster` — a `Roaring64Bitmap` behind a `java.util.Set` — is the alternative
  a store may answer instead: 0.13–0.26 bytes a handle against a `PersistentHashSet`'s
  48–75, which is 4.5–7.0 GB at 100M records held while `recover` walks the premises
  ([docs/defenses.md](docs/defenses.md)). The engine's own stores still answer Clojure
  sets, which is the `:disk` backend's ceiling and now a number in the doc instead of an
  assumption. *Class:* **Additive** — every store the engine ships answers exactly what it
  answered; the contract now says what a store *may* answer.
  [docs/storage.md](docs/storage.md)

- **`Tallying`: how many records, and is there one at all, without building the roster.**
  `open-kb` asked both by building the whole live-handle set and reading `count` / `first`
  off it — free on a store whose enumeration is a read of its own state, the entire table
  on the wire for one whose enumeration is a query, and asked twice on a `:pg-disk` open
  before the KB has answered anything. A store that can answer more cheaply implements the
  new optional protocol (`sentex-tally`, `justification-tally`, and three `a-…-id`
  samplers); the nine call sites go through `capabilities/count-sentexes`,
  `count-justifications`, `some-sentex-id`, `some-justification-id` and `some-premise-id`,
  which **fall back to the enumeration** — so a store without the capability reads exactly
  as it did. Over Postgres records each is now one row. *Class:* **Additive** — a new
  optional protocol beside `Prefetching`; nothing an existing store does changes.
  [docs/storage.md](docs/storage.md)


- **`BulkLoading`: an `import!` writes its records through a sink a store can answer in
  bulk.** Without one, each frame of a dump is its own `put-sentex` — a map assoc on the
  RAM store, a round trip on one across a socket — which left the fastest ingest path a
  records backend has (`COPY`, in the Postgres adapter) reachable only by an application
  that bypassed the KB. The third optional protocol beside `Prefetching` and `Tallying` is
  `open-sentex-sink` / `open-justification-sink`, each answering a `RecordSink` the three
  import paths write their stream to; `capabilities/sentex-sink` and `justification-sink`
  **fall back to `put-sentex` per record**, so a store without the capability loads exactly
  as it did. It is a sink rather than a batched put, and a record is not readable until the
  sink closes, for the reason [docs/defenses.md](docs/defenses.md) gives. Through `import!`
  on a 30k-record dump, `{:belief? false}`: `:pg-memory` 2,784 → **17,882 records/s** and
  `:sqlite` 7,444 → **16,572**, against `:disk` at 6,790 — a server-backed load is now
  faster than the local disk backend, and what remains is the engine's own per-frame work
  rather than the store. *Class:* **Additive** — a new optional protocol; every store the
  engine ships implements nothing and takes the loop.
  [docs/storage.md](docs/storage.md)

- **`BulkAnnotating`: the premise marks and the provenance are written many at once too.**
  The two per-handle writes that follow a record are made by the import path in a loop,
  and neither can ride the record write — which strength a handle ends at is decided only
  once the whole sentex stream is read, and the provenance stream is read after the
  records. On a store where a write is a round trip that is `n` round trips each: 20,000
  on a 10,000-record belief import, against 657 ms for the records themselves.
  `mark-premise-batch` / `put-provenance-batch` are the seam and
  `capabilities/mark-premises` / `put-all-provenance` the door, falling back to the loop.
  Bare, not `!`: both add and take nothing away, and the per-handle twins beside them
  (`mark-premise` / `put-provenance`) are bare for the same reason.
  A separate protocol from `BulkLoading`, since a store may load records in bulk without
  being able to bulk-update rows already there. Over Postgres, `{:belief? :stored}` on a
  10k dump: **2,288 → 5,969 records/s**, one statement for every mark and one per 1,000
  provenance maps. The batch marks `RETURNING` the ids they touched, so the phantom-premise
  guard and the strength cache stay exactly as strict as the one-row form.
  *Class:* **Additive.** [docs/storage.md](docs/storage.md)

- **The `:disk` record store bulk-loads too.** A record at a time there is two syscalls on
  an unbuffered `RandomAccessFile` — the log append and the 24-byte idx slot — plus a lock
  apiece. `f/append-records-sized!` packs a batch's frames into one write and
  `f/write-slots!` writes one positional range per run of consecutive handles, which is a
  single range for handles minted in order or preserved from a dump. Records-only import
  into `:disk-memory`: **14,987 → 18,986 records/s** (+27%, medians of three interleaved
  runs). A bulk write also *evicts* rather
  than fills the hot-record cache, since a load is a stream nobody is reading back.
  (`:disk` proper gains little, because with the durable index its bulk load is dominated
  by the index writes rather than the records.) *Class:* **Additive**, with one new
  refusal type: `:bad-batch`, for a `:batch` that is not a positive number of records.
  [docs/storage.md](docs/storage.md)

- **`*prefetch-candidates*` refuses a value that is not a chunk, at the `binding`.** The
  setting is `false` or a positive integer, and a var whose off-value is `false` invites
  `true` as the on-value — which is truthy, so it passed every gate on the query path and
  failed in the chunk arithmetic instead, a `ClassCastException` raised from inside a lazy
  seq several frames into the walk, naming neither the var nor what was bound to it. A
  validator on the var throws from `binding` itself, by name. *Class:* **Fix.**
  *Migration:* a `binding` of `nil`, `0` or `true` now throws where it previously ran
  unhinted or failed mid-query; bind `false` or a chunk size (256 is the measured
  plateau). [docs/storage.md](docs/storage.md)

- **`recover` stops re-reading records the roster already answered for.** `rebuild-tms`
  tested whether a justification's consequence and every antecedent were stored by
  *fetching* each one; a store rosters a handle only once the record is there, so
  membership in the live-handle set already answers that, and the fetch now runs only for
  a handle the roster does not name — which is the case it exists for. On a 9,002-record
  store that is 27,004 record fetches down to 9,004, on **every** backend. *Class:* **Fix**
  (a cost one, and no behaviour moves: a justification resting on a record the store lost
  is still left out of the network).

- **The recovery walks take the prefetch hint too.** `reindex` over the records and
  `recover` over the justifications both fetch every handle they enumerate, so they hint a
  chunk ahead — **ungated**, unlike the query path, because a walk that consumes
  everything never over-fetches what a stopping consumer would.  (It can still be a poor
  trade: a hint larger than the store's own cache evicts what it just installed, which is
  why the hint keeps exactly one chunk in flight and the store caps each batch at its
  capacity.) `Prefetching` gains
  `prefetch-justifications!` for the second of them. Over Postgres records this takes
  `reindex`+`recover` on that store from 1,656 ms to 740 ms, against 506 ms for the same
  KB entirely in RAM. *Class:* **Additive** — a second op on an optional protocol added in
  this same unreleased version; nothing implements it outside the Postgres adapter.
  [docs/storage.md](docs/storage.md)

- **`:pg-disk` names its directory, and the directory names its database.** The durable
  index lives on the host and the records live on a server, joined by nothing but the opts
  map — so `:dir` is now required for `:pg-disk` (a derived default is one two KBs over two
  databases would share), and the index directory is stamped with the database identity,
  an open over a different one being refused with `:type :stale-index-records`. The
  coverage check cannot stand in for it: that compares record counts, which two unrelated
  stores of the same size match. *Class:* **Refusal** — `{:backend :pg-disk}` with no
  `:dir` had no correct meaning, and the backend is new in this release, so no caller is
  carrying one. *Migration:* name the directory.
  *Breaks:* `:pg-disk`, `:dir`, `:stale-index-records`
  [docs/storage.md](docs/storage.md)

- **A fork's own records cannot be `:pg`.** An overlay keeps tombstones and released
  premise marks beside its records and that bookkeeping is written for `:memory` and
  `:disk`, so the pairing was already refused — but by `mount/meta-kv`, after `open-kb` had
  built the fork's own record store (a live pool) and its index half (which takes the
  directory's exclusive lock). A throw there returns no KB, so neither was closeable and
  the directory was unopenable for the life of the JVM. Refused at the door instead. A
  `:pg` KB can still be the frozen base. *Class:* **Fix.**

- **One database keys one index, however it is spelled.** `:pg` given as a JDBC URL and as
  the `:dbtype`/`:host`/`:dbname` triple are the same store and now key alike, as are a
  stated `:port 5432` and an omitted one; `:pg` naming no database at all — a present nil,
  an empty map, an opaque `DataSource` — is refused rather than defaulted. Keying on the
  literal opts map split one database into two index spaces, and two KBs then minted two
  handles for one sentence. *Class:* **Fix.** [docs/storage.md](docs/storage.md)

- **`:sqlite` and `:disk` records in one directory no longer share an index.**
  `derived-index-space` keyed both on the path alone, so a `:sqlite` KB and a `:disk-memory`
  KB over one directory were handed a single RAM index over records neither held. The key
  now carries the axis as well as the path. *Class:* **Fix.**

- **A prefetch hint for a record store whose fetch is not local.** `Prefetching` is an
  optional capability beside `RecordStore` — one op, `prefetch-sentexes!` — that a
  retrieval path calls with the handles it is about to walk, a chunk at a time. It is a
  **hint and never an answer**: it returns nothing, every record still arrives through
  `get-sentex`, and a store that ignores it answers identically, so it cannot move a
  result on any backend. `resolution/*prefetch-candidates*` is the chunk size and is
  **false**, so nothing is hinted unless asked; none of the engine's own stores implement
  the capability, so the setting is inert over them. Over Postgres records on a corpus
  whose working set does not fit the store's cache (`:cache-capacity 1000` against a 40k
  corpus) it is 12.6 ms/query against 4.0 at a 256-handle chunk. *Class:* **Additive** — a new optional protocol and one setting that
  defaults off; nothing changes for a KB that leaves it alone.
  [docs/storage.md](docs/storage.md)

- **Postgres records: `:pg-memory` and `:pg-disk`.** `open-kb` accepts `{:backend
  :pg-memory :pg <db-spec>}` — the records in a database an operator already runs, through
  the Apache-2.0 `com.vaelii/postgres` adapter (`vaelii.postgres.record-store`), resolved
  lazily exactly as `:sqlite` is, so the SSPL engine still carries no JDBC dependency.
  `:pg-disk` pairs the same records with the durable `:disk` index, which is **local** to
  the host running the writer and does not travel with the KB. The `:pg` opt names the
  database (a next.jdbc db-spec or a JDBC URL, with an optional `:schema`) and is
  required: nothing derives a default server. What a server buys — `COPY` at 95.8k
  records/s against the per-record door's 4.1k/s, an operator's backup and replication, a
  store bigger than one disk — and what it does **not** buy, which is a shared KB, are
  both in the doc. *Class:* **Additive** — new backend names and one new option; a KB
  naming neither is unchanged. The durable `:disk` index now pairs with `:pg` records as
  well as `:disk`, where it refuses RAM ones and `:sqlite` as before.
  [docs/storage.md](docs/storage.md)

- **Five refusals the daemon answered 500 for are the caller's mistake.**
  `serve/client-error-types` is a hand roster, and a refusal born at one door and never
  added to it counts as a backend fault at every proxy between the caller and the daemon.
  `:irreflexive` and `:anti-symmetric` are the two relation-property refusals that were
  not beside the four already on it; `:unsupported-context` is a query context handed to
  a read that does not resolve one; `:unsupported-variant` and `:unsupported-compression`
  name a dump this build does not write. All five answer **400** now, with the same
  `:type` on the wire as before. *Class:* **Fix.** *Migration:* a client discriminating on
  the status rather than on `:type` sees five 500s become 400s.
  [docs/operations.md](docs/operations.md)

- **A tool argument the chosen signature cannot read is refused, not dropped.** The tool
  surface dispatches on the longest signature the model's input satisfies, and the shapes
  nest — `query` takes `(goal)`, `(goal, context)`, `(goal, context, opts)` — so a call
  giving a goal and `opts` with no context selected the first and ran the read facts-only
  with the depth discarded, which is indistinguishable from a goal no rule can reach.
  *Class:* **Fix.** *Migration:* none. [docs/llm.md](docs/llm.md)

- **A feed subscription with a context and no goal is refused.** `core/watch`'s whole-feed
  arity takes no context, so the daemon registered an unscoped listener while its registry
  stored the context and `:watchers` reported it back — naming a scope it was not
  applying. `:not-watchable`, the mirror of the contextless goal. *Class:* **Fix.**
  *Migration:* none. [docs/feed.md](docs/feed.md)

- **`preview` and `edit-with-consequences!` refuse a cap that is not a positive integer.**
  Both guarded `:max-results` with `pos-int?`, so a string or a zero read as *no cap* and
  the diff came back whole with `:bounded?` false — the silent default the opts roster
  beside it refuses a typo for. `check-limit!` now runs at both doors, as it already did
  at `find-terms`, `kb-quality` and `qualitative-scenarios`. *Class:* **Fix.**
  *Migration:* none. [docs/preview.md](docs/preview.md)

- **The proposal panel's apply refuses a target this process does not hold.** The panel,
  the turn and the preview all say a proposal needs the KB in process; the apply is the
  one that writes, and it was the exception — `report-only-problems` is a KB read, so on a
  remote target it was skipped and the line it holds back would have been stored on the
  strength of a field the browser sent. *Class:* **Fix.** *Migration:* none.
  [docs/web.md](docs/web.md)

- **`register-modal-predicate!` loses its `!`.** It asserts one `(modalPredicate pred)`
  marker, which `retract!` takes back, so it never belonged on a roster that means "the KB
  cannot undo this". *Class:* **Breaking.** *Migration:* call
  `register-modal-predicate` — same arities, same return, the `!` spelling is gone.
  *Breaks:* `register-modal-predicate!`
  [docs/belief.md](docs/belief.md), [docs/api.md](docs/api.md)

- **The dense TMS's handle-ceiling refusal carries a `:type`.** It named the ceiling and
  the `{:tms :reference}` remedy but no type, so a supervisor discriminating on the
  refusal vocabulary could not tell it from any other `ex-info`. It is
  `:type :handle-ceiling` now, `:remedy` unchanged. *Class:* **Additive.**
  *Migration:* none. [docs/density.md](docs/density.md)

- **The rounding grid follows `*quantity-tolerance*`.** A computed magnitude was snapped
  to nine decimal places whatever tolerance was bound, so rebinding the var moved every
  comparison and left the grid where it was — two magnitudes the comparisons called equal
  rendered as two different figures. The scale is derived from the bound tolerance.
  *Class:* **Fix.** *Migration:* none. [docs/quantity.md](docs/quantity.md)

- **A confluence report names only overlaps a term can reach.** The critical-pair detector
  descended into functor position, which `normalize` never reduces at, so two rules could
  be reported as non-confluent over a term no normal form passes through.
  *Class:* **Fix** — a warning is withdrawn, none is added.
  *Migration:* none. [docs/equational.md](docs/equational.md)

- **An unrepaired reified-NAT collision is swept against one expression.** A constant
  mapped to two expressions had its orphanhood decided against either of them and its
  bookkeeping computed from whichever the retrieval yielded first, so a sweep could retract
  one expression's records on the other's verdict. Both readers take the content-least
  expression. *Class:* **Fix.** *Migration:* none. [docs/nat.md](docs/nat.md)

- **A koinii commit id is a function of belief, not of storage.** `commit-id`,
  `state-root` and `inclusion-proof` folded every stored record, so a seat that had
  defeated a default computed a different id from a seat that never heard of it — two
  seats agreeing on every belief reading as though they disagreed about the knowledge. All
  three enumerate the believed records now, and `inclusion-proof` on an unbelieved
  record's locator is nil. *Class:* **Breaking** — every id a seat computes moves, and a
  defeat moves it as a retraction does. *Migration:* re-derive any stored commit id or
  state root; ids taken before this are not comparable with ids taken after.
  *Breaks:* `commit-id`, `state-root`, `inclusion-proof`
  [docs/koinii.md](docs/koinii.md)

- **A koinii write is stamped by the identity it is made through.** `channel/assert` let a
  caller's `:creator` win over the agent handle's, against its own contract and against the
  ownership check `belief/disregard` enforces; `deref/publish!` let a caller's
  `:compression` override the `:none` that makes a published commit byte-stable. Both are
  refused now — `:koinii/creator-mismatch` and `:koinii/compression-pinned` — rather than
  one silently honoured and the other silently dropped. *Class:* **Breaking.**
  *Migration:* drop the `:creator` from a `channel/assert` call (it was already the
  agent's), and take a compressed dump with `export!` directly, which makes no
  byte-stability claim.
  *Breaks:* `:koinii/creator-mismatch`, `:koinii/compression-pinned`, `publish!`
  [docs/koinii.md](docs/koinii.md)

- **The koinii adjudication reads follow belief.** `standing-rulings` and `rule`'s
  arbiter-is-party check enumerated an agent's context unfiltered, so a defeated ruling was
  withdrawn as stale — and destroyed — while a defeated claim still convicted its holder of
  being a party to the dispute. Both filter belief. `contested-premises` returns its
  handles in content order rather than in the hash order of the support set.
  *Class:* **Fix.** *Migration:* none. [docs/koinii.md](docs/koinii.md)

- **A catch-up poll that fails is a failure whatever it threw.** Only an `ex-info` with a
  `:type` was read as an error, so anything else fell through to the drained-to-head arm:
  `sync!` persisted `{:cursor nil}` and handed back the stale view as though the stream
  were current — silent loss, which is the one failure catch-up exists to prevent. Any
  exception is now reported with the original as its cause, and a poll answering no cursor
  is refused rather than stored. `sync!` also takes the consumer's own monitor, since its
  body is a read-modify-write over the cursor and the view. *Class:* **Fix.**
  *Migration:* none. [docs/koinii.md](docs/koinii.md)

- **Exactly one of several concurrent `unwatch`es of one token says it removed something.**
  `feed/unregister!` read the listener list and then swapped, so two callers both saw the
  listener and both answered true — two callers each believing they own a teardown that
  happened once. One `swap-vals!`, and the answer is read off the CAS that did the removal.
  *Class:* **Fix.** *Migration:* none. [docs/feed.md](docs/feed.md)

- **An LLM error body rides bounded in the message and whole in the data.** A non-200
  joined the entire response into the exception message, so a proxy answering a megabyte of
  HTML put a megabyte in every log line the failure reached. The message takes
  `http/excerpt`'s bound, as `http/decode`'s `:excerpt` already did, and the full text is
  under `:body` in the ex-data. `under-read-deadline` also catches `Throwable` rather than
  `Exception`: an `Error` out of a body read — a hostile body overflowing the stack — no
  longer escapes the `:llm-timeout` rewrite. *Class:* **Fix.** *Migration:* a caller that
  parsed the failing body out of the message reads `:body` instead.
  [docs/llm.md](docs/llm.md)

- **A generated corpus counts its context edges, and draws direction and defeasibility
  separately.** `plan`'s `:units` — what a progress bar divides by — added the number of
  contexts where `load-into` asserts one edge more than that (the schema context's own
  edge under `CxCore`), so a bar over two or more contexts never reached its end. And
  `:direction` and `:defeasible?` were two thresholds on the same rule index, so at any
  settings where `:defeasible` ≤ `:forward` every defeasible rule was also a forward one
  and no settings at all produced a defeasible *backward* rule — a shape the corpus could
  not exercise however the knobs were turned. Two draws now, from the rule stream's own
  seeded generator. *Class:* **Fix.** *Migration:* regenerate any saved generated corpus a
  comparison depends on. [docs/catalog.md](docs/catalog.md)

- **A compaction drops a handle whose frame the log cannot give back.** A slot can outlive
  its frame — what a truncated tail leaves under a slot the truncation did not reach — and
  the rewrite re-froze the `nil` it read, putting the handle back as a *live* record
  fetching to nothing: an id `sentex-ids` names and `get-sentex` has no answer for. It is
  tombstoned instead and taken out of the live set, the premise set and the record cache,
  with a `:warn` naming the handle. *Class:* **Fix.** *Migration:* none.
  [docs/storage.md](docs/storage.md)

- **The durability tick costs nothing on a store nobody wrote to.** `counters.nippy` was
  rewritten every tick — a temp, an fsync of it, an `ATOMIC_MOVE` and a directory fsync,
  every three seconds for the life of the process — whether or not the handle counter had
  moved. It is written when it changed. The compaction probe beside it is floored by
  `vaelii.disk.compact-min-interval-ms` as well: asking a record store for its dead ratio
  scans every `.idx` in full under the kind lock, and the stamp was taken only where a
  compaction *fired* — so a store that never crosses the threshold paid that scan every
  three seconds for the life of the process. The stamp is taken before the ratio is read
  and again when a rewrite finishes, so the interval floors the probe and the rewrite
  alike. *Class:* **Fix.** *Migration:* none. [docs/storage.md](docs/storage.md)

- **The durability daemon installs one ticker and forgets no backend.** The scheduler, the
  compaction executor and the shutdown hook were check-then-act inits, so two first
  `register!`s racing installed two tickers over one registry — every registrant fsynced
  twice a tick, with only one of the two reachable by `stop!`. All three (and `stop!`) now
  take one monitor. And `submit-compaction!` marks a backend in flight *before* the submit,
  so a submit the executor refused left the mark standing and barred that backend from
  auto-compaction for the life of the process; the refusal clears it. *Class:* **Fix.**
  *Migration:* none. [docs/storage.md](docs/storage.md)

- **The disk lock tells a second JVM from a second copy of itself, and keeps what it could
  not give back.** `tryLock` *throws* when the calling JVM already holds an overlapping
  lock, so that branch was reporting "locked by another JVM" for a second classloader copy
  of this namespace — and reading the holder off the file, which named our own pid as the
  intruder. It is diagnosed as ours now (`:same-jvm? true`). `held?` and `release!` follow
  the `held` entry rather than re-reading `vaelii.disk.lock`, which could be toggled
  between the acquire and the release and leave the OS lock stranded. And a release that
  fails keeps its entry rather than reporting the directory free while the JVM still holds
  it: re-acquisition is refused with `:type :unreleased`, naming this JVM.
  *Class:* **Fix.** *Migration:* none. [docs/storage.md](docs/storage.md)

- **An `:xz` dump allocates a dictionary the size of a chunk.** Each chunk is its own
  compression window — that is what makes one independently readable — so the encoder is
  per chunk, and it was taking LZMA2's preset-6 8 MiB dictionary against a default
  10,000-frame chunk of about 1 MB. Sized to the chunk it writes the same bytes (identical
  from 8 MiB down to 1 MiB, measured over a 34k-sentex dump) for 24 MB of encoder working
  set rather than 93. `:xz` is also read through the imported `XZInputStream` rather than
  reflectively, leaving `:zstd` the only codec whose readability depends on the classpath.
  *Class:* **Fix.** *Migration:* none. [docs/namespaces.md](docs/namespaces.md)

- **A remote `why` re-asks a truncated proof deeper.** `client/why` takes `core/why`'s
  `opts` — `{:max-depth n}` — at a third arity; the served op already accepted it, so only
  the client wrapper was missing and a `{:truncated? true}` branch was unreachable over the
  wire. *Class:* **Additive.** [docs/api.md](docs/api.md)

- **Which justifications a rule exception blocks is a served read.**
  `core/blocked-justifications` answers the network's blocked set,
  `:blocked-justifications` serves it, and `client` and the access facade reach it — so an
  attached browser draws a blocked justification as blocked rather than as supporting,
  blocking being the one justification property belief alone does not report.
  *Class:* **Additive.** [docs/exceptions.md](docs/exceptions.md)

- **The neighbour sets a closure walk builds are counted.** `:closure-neighbours` was
  registered with `:counters nil`, so a miss — one neighbour set built against the store —
  went unrecorded and the page that shows cache hit rates carried a blank where that row's
  should be. `observe/note-neighbours!` counts them in the literal cache's arrangement and
  for its reason: process-wide `AtomicLong`s, because they measure the mechanism and not a
  store. A read taken with no memo bound counts as a miss, a compute being a compute
  whatever scope it happens in. Seven tests were reaching the same number by redefining
  `res/matches-visible` and guessing which of its calls were the walk's; six now read the
  counter. *Class:* **Additive.** *Migration:* none.
  [docs/caches.md](docs/caches.md), [docs/web.md](docs/web.md)

- **Three CLI commands print their answer sorted.** `match`, `query` and `ask` answer sets,
  and an unsorted print was whichever order the retrieval enumerated — so two loads of one
  KB printed the same knowledge differently and a `diff` of two runs read as a change in
  the KB. They are ordered by content key, alongside `types` and `contexts`. `prove` keeps
  DFS order, which is a reading of the search rather than an artifact. *Class:* **Fix.**
  *Migration:* a script depending on the previous output order of `match` / `query` / `ask`
  reads a different one. [docs/operations.md](docs/operations.md)

- **The log level survives a reload of the namespace that holds it.** The dial lived in a
  plain `def`'d atom, so re-evaluating `vaelii.impl.logging` handed the process back a
  level reading nil — whatever an operator had set, undone by a reload nobody asked to
  change the level. Under cloverage that is not hypothetical: it re-evaluates every
  namespace to instrument it, so the suite lost the `:error` floor its injections install
  and the coverage run wrote 1.5M lines of debug output. A `defonce`, as `caches/registry`
  and the memory spaces already are. *Class:* **Fix.** *Migration:* none.
  [docs/operations.md](docs/operations.md)

- **The browser refuses a request parameter it cannot read.** `?max-derivations=`, `?d=`,
  `?calc=` and the assert form's `strength` each took a default, a different calculus, or
  `:monotonic` in silence — `max-derivations` most consequentially, its absence being what
  asks for an unbounded fixpoint. Each answers **400** naming the parameter, the value and
  what would have been legal, and `?d=` is held to the range its own form declares.
  *Class:* **Fix.** *Migration:* a bookmarked URL carrying an unreadable value answers 400
  rather than a page. [docs/web.md](docs/web.md)

- **A cancelled job's interrupt cannot reach a thread it has released.** `jobs/cancel!`
  decided from one read of the registry, so a job settling in between had the interrupt land
  on the pool thread it had already gone back to. The thread is fenced by the job's own
  monitor, and a canceller interrupted while it waits restores its flag rather than throwing
  out of the web handler. *Class:* **Fix.** *Migration:* none. [docs/web.md](docs/web.md)

- **The profiler UI starts once under a race as well as under a reload.** The claim is a
  `compare-and-set!` rather than a read followed by a start, so two callers cannot both pass
  the test and race for the port. *Class:* **Fix.** *Migration:* none.
  [docs/web.md](docs/web.md)

- **A term graph draws the same neighbours whatever else was asserted first.** The ego-edge
  scan took a fixed window off a set of handles, so the picture was a sample by hash of the
  handle values. It is ordered by handle first, which makes the window the term's earliest
  mentions, and the caption says that is what it is. *Class:* **Fix.** *Migration:* none.
  [docs/web.md](docs/web.md)

- **A post-join antecedent that answers two ways concludes nothing.** An aggregate, or a
  computed literal reading one, was evaluated per placement by taking the registry's first
  solution — so a literal with several solutions placed a different fact depending on which
  came first, and which comes first is a function of how the facts were stored. The
  disagreement is declined and filed as `:post-join-ambiguous` in `violations`, the rule
  the engine already takes for a reading stated twice over. *Class:* **Fix.**
  *Migration:* none — a KB whose post-join literals are the built-in computations cannot
  reach it. [docs/aggregate.md](docs/aggregate.md)

- **An aggregate over measures renders in one unit whatever order they arrived in.** The
  reduction read its base unit off whichever measure the extent yielded first, so a KB
  whose units of one dimension declare different bases answered in different units in
  different load orders. The content-least unit decides. *Class:* **Fix.**
  *Migration:* none. [docs/quantity.md](docs/quantity.md)

- **A capped backward proof answers the same whichever order the rules arrived.** Candidate
  rules came off the consequent index in handle order, and both executors truncate on that
  list — `prove-within`'s `:max-results` and the node engine's frontier — so a bounded query
  returned different answers for the same knowledge. The candidates are ordered by
  `[sentence context]`, and the node frontier breaks a cost tie on the node's own content
  rather than on the id its traversal minted. *Class:* **Fix.** *Migration:* none, unless a
  caller had pinned which single answer a capped `prove` returned.
  [docs/nmtms.md](docs/nmtms.md)

- **`nm/name-key` and `nm/by-print-key`, and no ordering key is a bare `str`.** `str` on a
  collection honours the ambient print bounds exactly as `pr-str` does, so a sentence, a
  NAT, a context NAT or a binding map keyed with it collapses under a REPL's
  `*print-length*` and the tie falls back to arrival order. Fifty-one ordering keys move to
  the guarded printer and six to the scalar key, and `sort_by_content_key_test` now scans
  for the shape. *Class:* **Additive.** *Migration:* none.
  [docs/nmtms.md](docs/nmtms.md)

- **Two scaling claims are gated.** `lein perf` gains `qcn-network-residency` (a repeated
  qualitative consultation is flat in the stored extent of the calculus it is not about)
  and `inherit-reach-memo` (8x the claims reaching one term costs under 12x per ask), each
  with a counted companion in the suite. *Class:* **Additive.** *Migration:* none.
  [docs/qcn.md](docs/qcn.md)

- **`/levels` refuses a query context rather than failing on one.** `CxEverything`,
  `CxInference` and `CxNothing` typed into the page's own context box reached a read that
  does not resolve one, and the browser has no exception middleware to make a page of the
  refusal — so Jetty answered 500. `/levels` and `/levels/rows` check the context first and
  answer the same 400 page every other unreadable parameter gets, naming the context and
  the three that are not places. *Class:* **Refusal.** *Migration:* none — no page produces
  such a URL, and a hand-written one gets a page instead of an error.
  *Breaks:* `/levels`, `/levels/rows`
  [docs/web.md](docs/web.md)

- **A continuation offset is capped, so a hand-edited one cannot overflow the arithmetic.**
  `?offset=` was read unbounded and `/find/rows` adds its page cap to it before asking the
  term roster, so `Long/MAX_VALUE` raised `ArithmeticException` out of the handler as a 500.
  `->offset` ceilings at a billion rows — past anything a sentinel writes, so no cursor is
  truncated — and it covers all six continuation routes at once. *Class:* **Fix.**
  *Migration:* none. [docs/web.md](docs/web.md)

- **A CSS width is written with a dot whatever the machine's locale.** The load progress bar
  and the heap meter composed `width:` with `format "%.1f"`, which renders in the default
  locale — so on a comma-decimal one the declaration read `width:12,5%`, which is not a CSS
  number: the browser dropped it and the bar drew at whatever width the stylesheet gave it,
  with nothing on the page to say so. Both go through one `Locale/ROOT` helper. Display
  numbers are untouched and still read in the reader's own convention. *Class:* **Fix.**
  *Migration:* none. [docs/web.md](docs/web.md)

- **`POST /propose/level` is guarded exactly as the row it reposts.** The list's originals
  ride two repeated fields and are zipped, and the route checked neither what it read nor
  how many of each arrived — so a sentence that did not read reached the verdict pass, and a
  post carrying more `from`s than `ctx`s re-rendered the shorter and dropped the rest with
  nothing to say a line had gone missing. Both are refused now, in `/propose/line`'s own
  words. *Class:* **Refusal.** *Migration:* none.
  *Breaks:* `/propose/level`
  [docs/web.md](docs/web.md)

- **Cancelling a job that has already finished answers false.** `jobs/cancel!` answered true
  for any id the registry still held, and it holds a settled job's report for an hour — so a
  stop clicked the moment a run finished reported a cancellation over a load that was
  complete or a dump already written. It answers whether there was a *run* to stop, and
  `/jobs/cancel` says so. *Class:* **Fix.** *Migration:* a caller reading the answer as
  "the registry still holds this id" now reads a settled job as absent — ask `jobs/job` for
  that question instead. [docs/web.md](docs/web.md)

- **A koinii ballot is declared, so it cascades with the claim it was cast on.**
  `votesFor` / `votesAgainst` were the two response acts `CxSpeechActs` never declared:
  no `comment`, no arity, no `arg`, and — the one that mattered — no
  `targetFollowingPredicate`. So retracting a disputed claim swept its answers,
  endorsements, disputes and justifications and left the ballots standing on a claim that
  no longer existed, with `tally` still counting them. Both now carry the same family
  every other response act does. *Class:* **Fix.** *Migration:* none — a KB that loads
  `CxSpeechActs` picks the marks up on the next load; ballots already stored on a claim
  that has since gone are orphans no cascade will reach, and are found by matching
  `(votesFor ?a (sentexHandle ?h))` against the handles the store still holds.
  [docs/koinii.md](docs/koinii.md)

- **Cross-seat dereference follows belief, as the commit id already did.**
  `commit-id`, `state-root` and `inclusion-proof` enumerate the records a seat
  *believes*; `dereference` and `resolve-by-locator` walked storage, so a defeated default
  resolved to a full answer for which the same seat could produce no inclusion proof — one
  seat, two stories about what it holds. Both read the believed handles now.
  `dereference`, which is handed the sentence, reports the new `:not-believed` for a
  record it stores but does not hold; a bare locator cannot tell that from never having
  received it, so `resolve-by-locator` reports `:not-received` for both.
  *Class:* **Breaking** for a caller resolving an unbelieved record. *Migration:* read the store
  directly (`handle-of` / `sentex`) where storage rather than belief is the question; a
  caller discriminating on `:reason` gains one value to match.
  *Breaks:* `dereference` `resolve-by-locator` [docs/koinii.md](docs/koinii.md)

- **Two koinii channel doors stop nil-punning their argument.** `channel/dispute` and
  `speech-acts/dispute` read the target's sentence to build the rebuttal, so a handle
  naming no record stored the literal `(not nil)` plus a `disputes` edge on nothing — a
  challenge to a claim that does not exist, indistinguishable in the KB from one that
  does. Both refuse it (`:koinii/no-such-handle`), as `deref/marker` does.
  `channel/vote` fell out of a defaulted `case` as a bare `IllegalArgumentException`;
  it refuses by name (`:koinii/no-such-stance`), carrying the two directions there are.
  *Class:* **Refusal.** *Migration:* none.
  *Breaks:* `channel/dispute`, `speech-acts/dispute`, `channel/vote`,
  `:koinii/no-such-handle`, `:koinii/no-such-stance`
  [docs/koinii.md](docs/koinii.md)

- **A wire subscription that dies says so, and a dropped event is not silent.** With no
  `:on-error`, a poll failure ended the loop and left the subscription reading live — a
  dead reader nobody could detect and so nobody resubscribed; with no `:on-lagged`, the
  ring's dropped count vanished. Every exit from the poll loop resets the subscription's
  new `:running` atom, and each unset seam logs instead of dropping: `:error` for the
  failure, `:warn` for the lag. *Class:* **Additive.** *Migration:* none — a supplied
  handler still replaces the line. [docs/koinii.md](docs/koinii.md)

- **A refused arbiter ruling ends no dispute episode.** `adjudication/rule` cleared the
  dispute's notified/stale marks *before* asserting the ruling, so an inadmissible `upheld`
  threw out of `edit!` leaving the dispute reopened and un-notified with nothing ruled on
  it — the driver then re-announcing a clash whose ruling never happened. The marks are
  cleared once the ruling has landed. `adjudication/sweep-stale` also stops running a
  whole-KB `contradictions` + `conflicts` scan per open dispute: every entry `disputes-in`
  hands back is live by construction, so the skip reads the stored `:stale` mark.
  *Class:* **Fix.** *Migration:* none. [docs/koinii.md](docs/koinii.md)

- **A model host that never answers costs seconds, not the turn's whole budget.** Both HTTP
  backends handed `:timeout-ms` to `connectTimeout`, so a host that accepted no connection
  held the calling thread for the five minutes an Ollama turn is allowed, or the ten a
  Messages API turn is — a hang wearing a timeout's clothes. The connect deadline is now a
  fixed `http/connect-timeout-ms`, and `:timeout-ms` bounds the answer as documented. The
  Ollama probes also share one held `HttpClient` rather than building a pool per call, which
  `available?` did on every `/propose` the browser posted. *Class:* **Fix.** *Migration:*
  none — a caller that wanted a long connect deadline never had a way to ask for one.
  [docs/llm.md](docs/llm.md)

- **A sentence carrying an escaped non-ASCII character reads back with that character.**
  The incremental scanner reads s-expressions out of the raw response, so escapes arrive
  intact — and a host that writes `café` produced `cafu00e9` in the stored sentence:
  not a parse failure, which is the problem, but a sentence that read cleanly and said
  something else. `session/unescape` reads the four hex digits, and `\b` / `\f` with them.
  *Class:* **Fix.** *Migration:* none. [docs/llm.md](docs/llm.md)

- **A judged run's token counts add across batches instead of throwing.** A provider names
  every count it knows and leaves the rest nil, so summing two batches' usage raised a
  `NullPointerException` out of `oracle/judge` — reachable only past the first batch, which
  is why a small run never saw it. Absent counts are dropped rather than counted as zero.
  *Class:* **Fix.** *Migration:* a `:usage` map now omits a key no host reported, where a
  single-batch run once carried it as nil. [docs/commonsense.md](docs/commonsense.md)

- **A tool failure with no message is named by its class.** The `Throwable` arm exists for
  the `StackOverflowError` a deeply nested argument raises, and that error carries no
  message — so the refusal handed the model an empty string, which reads as a tool that
  answered emptily rather than as an argument to fix. *Class:* **Fix.** *Migration:* none.
  [docs/llm.md](docs/llm.md)

- **The vocabulary inventory says how many lines it left out.** The trim stopped on a nil
  entry as though the list had ended, reporting nothing dropped — and a cut nobody is shown
  reads as the whole of the vocabulary. *Class:* **Fix.** *Migration:* none.
  [docs/llm.md](docs/llm.md)

- **A test that reaches a model without the `^:llm` mark now fails the suite's own scan.**
  The mark ⟺ gate check is satisfied by a test carrying *neither*, so an unmarked, ungated
  test that built an Ollama provider and ran a turn dialled out under a plain `lein test`.
  The scan reads what a test calls as well as what it declares. *Class:* **Additive.**
  *Migration:* a test that genuinely reaches a host carries the mark and the gate; one that
  exercises a probe offline pins the var it reaches through. [docs/llm.md](docs/llm.md)

### Performance

Six changes to what a read or a write costs. None of them moves an answer; the one that
moves a counted read says so.

- **A literal with no symmetric sub-predicate pays for one answer, not a mirror's two.**
  Giving the mirror its second answer (0.11.0, below) gave every candidate the machinery
  for two — a `lazy-mapcat` over a per-candidate answer vector run through a transducer
  chain whose `remove` probes a `[handle bindings]` pair against a set holding bare
  handles, so on the non-symmetric path it allocates a tuple that cannot hit. `sym?` is
  already read once per call, so that shape keeps the chunked `keep` and the handle-keyed
  dedup it had, and the pairing stays where a mirror really can answer twice. The
  retrievals are identical, which is what `:reads`, `:goals` and `:sift`
  (`vaelii.impl.profile`) hold across it; a 5 000-node braid probe allocates 0.80× what it
  did. *Class:* neither label. [docs/indexing.md](docs/indexing.md)

- **A closure walk is a scan, so it neither reads the literal cache nor fills it.** `reach`
  visits a node once, so a walk asks each neighbour literal once and leaves no repeat for a
  solution cache to serve — one hit in 4 998 lookups, measured — while its one insertion
  per node clears the whole 4 096-entry cache part-way through, evicting the metadata
  literals a rule-heavy query does re-ask. The neighbour probes pass `matches-visible` a
  false `cached?`, so the exemption reaches the probe and not everything under the walk,
  and no `binding` marks the toggle thread-bound for the rest of the process. A walk keeps
  its repetition where it is: the closure in `:closure-answers`, the neighbour sets a join
  re-walks in the search step's memo. This one **does** move a counted read — a former
  cache hit fetched no records and now costs the probe it skipped — so `:reads` rises by
  the hits it no longer takes, while the answers do not move. The braid probe allocates
  0.73× against the entry above and asks 1.45× against the release before both.
  *Class:* neither label. [docs/caches.md](docs/caches.md)

- **The reader set stops meet-closing the lattice against itself.** `readers` ran
  `meet-closure` over the whole context lattice plus the candidate seed — O(pairs), each
  pair a maximal-common-descendant search — and over the lattice's own nodes it cannot add
  a member: a common descendant is drawn from the context-down closures, so it is a node
  already, and the closure was handing back the set it was given. It runs only over a seed
  the lattice does not already contain, which is the one case the seed exists for: an
  edgeless context holding a fact the goal could match. `readers` drops 1.83 → 0.07 ms at
  three contexts and 9.56 → 0.22 at twenty-four, and the fan with it (10.37 → 8.37, 32.88
  → 24.48). What is left of the fan's cost is the fan — |readers| scoped queries — and a
  reader is dear in proportion to how deep its `genlCx` up-cone is, not how wide the
  lattice is. *Class:* neither label. [docs/contexts.md](docs/contexts.md)

- **The join budget stops charging for the read it was meant to guard.** Sizing the bail
  off `readers` put that call — O(the goal's match set), because besides the lattice it
  hunts for contexts outside it — back on the default path, which is the one path that
  never needs it: post-hoc places from the ingredients it matched and enumerates no
  readers at all. It is sized off the lattice instead, which is a row count for a cost
  decision and not an estimate of anything. And the first literal is not metered: the
  budget guards the multiplication, and the first stage multiplies nothing — its rows are
  the answer set's own floor — so a single-literal read of eight thousand facts abandoned
  a pass it was winning and fanned over eighteen readers, the one shape post-hoc cannot
  lose. *Class:* neither label. [docs/contexts.md](docs/contexts.md)

- **The belief flag is read once a retrieval path, not once a candidate.** `believed?` put
  a dynamic deref in the innermost loop retrieval has — once per *candidate handle*, of
  which a broad literal has thousands — which `lein perf` caught as negation-arbitration
  going 11.47× to 12.73× against a 12.00× bound. Each path reads it into a local at the
  top and the per-candidate cost is an `or` against a boolean. Safe to hoist because the
  value cannot change under a path: the door binds it around the whole read, and a blind
  seq re-establishes it per realization step. *Class:* neither label.
  [docs/belief.md](docs/belief.md)

- **Two constants stop being recomputed on the hottest write paths.** `registered-calculi`
  rebuilt its answer per call — an `instance?` test per prover in the default registry of
  eighteen, plus a fresh vector, to tell a KB that registered no calculus nil again — and
  it is asked once per asserted sentence and once per antecedent literal, so a 10M-fact
  bulk load computed the same nil 10M times. It is memoized on the registry vector's
  *identity*, registration being opt-in and setup-time, and identity keys avoid the
  hashCode walk that is the cost being removed. `add-just!` walked `(concat antecedents
  out)` under a `doseq`, allocating a lazy seq per derived justification to express
  nothing but "iterate both"; two `run!` walks instead. Measured paired against the
  unpatched tree, order alternated per pair: 1.020× on a 1M-fact DAG load (4/4 pairs) and
  ~1.3% median on a four-rule join to a 38,772-fact fixpoint. *Class:* neither label.
  [docs/qcn.md](docs/qcn.md), [docs/nmtms.md](docs/nmtms.md)

## 0.11.0 — 2026-08-22 — "contradiction solving, arrival order, and the durable log"


- **`antiTransitive` convicts the chain it forbids.** The mark shipped classified and
  disjoint from `transitive`, with the conviction declared and not enforced: `(P a b)` and
  `(P b c)` believed left `(P a c)` admitted in silence. The three are **one nogood**, the
  first whose members are three rather than two — a known-true chain refuses the direct
  step at the door (`:type :anti-transitive`), a chain with one defeasible step has that
  step defeated, and three equal defaults are a three-sided dilemma `contradictions`
  reports and the engine declines to decide. The mark descends the predicate hierarchy
  like the other constraint marks, so it convicts a `fatherOf` chain under
  `(antiTransitive parentOf)`; it does not imply `irreflexive`, and a step reached only by
  argument preservation is not enumerated. *Class:* **Breaking** — a KB that declared the
  mark and stored a chain is now told about it, and `:nogood` / `:handles` / `:sides` on a
  clash report can hold three members where a reader may have assumed two. *Migration:*
  drop the mark, or state the chain's exception, where the declaration was documentation
  rather than a constraint.
  *Breaks:* `antiTransitive`, `:anti-transitive`, `:opposing-handles`, `contradictions`,
  `conflicts`, `check`
  [docs/nmtms.md](docs/nmtms.md), [docs/taxonomy.md](docs/taxonomy.md)

- **Register a computed predicate or function in one line.** `add-evaluatable` wraps a
  plain Clojure fn as an evaluatable prover — a *check* over ground arguments (a truthy
  return is the predicate holding, like `lessThan`) or a *result-binding* function
  (`:result` names the output slot a value binds, like `evaluate`) — so a calculated
  relation no longer needs a hand-written five-method `Prover`. The fn is a value the
  caller supplies, never `eval` of KB data. It answers a direct `ask` / `query` goal and,
  the node engine's leaf being the registry, joins and discharges a rule antecedent under a
  `:max-depth`, reading as a leaf of a `{:proof? true}` derivation. *Class:* **Additive** —
  one new public fn (`vaelii.core/add-evaluatable`); no existing behaviour changes and
  nothing to migrate. [docs/inference.md](docs/inference.md), [docs/api.md](docs/api.md)

- **Definitional collection relations: membership tied to a defining condition.**
  `(defnNecessary Coll C)` / `(defnSufficient Coll C)` / `(defnIff Coll C)` tie a
  collection's membership to a condition on the member `?x` — necessary (member ⇒
  condition), sufficient (condition ⇒ member), or both. Each expands at assert into an
  ordinary forward rule (`(implies (Coll ?x) C)` and/or `(implies C (Coll ?x))`),
  materialized as a derived rule sentex justified by the `defn*` fact alone — so the
  entailment inherits rule indexing, forward chaining, placement, retraction and
  belief-following for free, exactly as a generator's minted rule does. Open-world only:
  nothing closes the collection's complement, so a thing the condition is silent about is
  neither concluded a member nor a non-member. *Class:* **Additive** — new `CxCore`
  vocabulary and one derivation off it; a KB using neither predicate is unchanged.
  [docs/defns.md](docs/defns.md)

- **Sibling disjointness: a collection's specializations separate themselves.**
  `(siblingDisjoint C)` marks a collection so any two of its `genl`-specializations
  share no instance, *unless one is a `genl` of the other* — Cyc's
  `siblingDisjointCollectionType` shape, without hand-asserting every pair. It is the
  `disjointMetatype` clique keyed off the `genl` closure rather than a recorded member
  set: only the mark is cached, `disjoint?` reads the separated pairs off `specs`, and
  it raises contradictions through the same JTMS/ASP path as `disjoint` — refused where
  written, reported as an exposed clash where only a descendant context can see it.
  Covering (whether the specializations exhaust `C`) is out of scope. *Class:*
  **Additive** — new vocabulary and one taxonomy cache; a KB naming no `siblingDisjoint`
  behaves exactly as before. [docs/taxonomy.md](docs/taxonomy.md),
  [docs/glossary.md](docs/glossary.md)
- **An escape hatch for a pair that must overlap.** `(siblingDisjointException X Y)`
  exempts the one pair `X`, `Y` that a `siblingDisjoint` mark or a `disjointMetatype`
  would otherwise force disjoint — a Braille reading is both a `reading` and a
  `touch_perception` — without disturbing either type's disjointness from the parent's
  other specializations. Pair-local and non-leaking to subtypes, keyed like `disjoint`,
  belief-following, and read over the whole KB rather than the reader's cone (an exemption
  removes a clash, so a scoped one would be non-monotone). *Class:* **Additive** — new
  vocabulary and one taxonomy cache; a KB naming no `siblingDisjointException` behaves
  exactly as before. [docs/taxonomy.md](docs/taxonomy.md),
  [docs/from-cyc.md](docs/from-cyc.md)

- **Why a sentex is believed, or is not, as a map instead of a bisection.** `belief-status`
  reports one handle from one context with the stages held apart — stored, raw JTMS `in?`,
  the `except` cascade visible from the asking context, assertion-context inheritance — and
  the two terminal answers `:believed?` and `:visible?` computed off them, so a read that
  came back empty names the gate that closed it. The `:exceptions` forest is ordered by
  assertion context and content and nests a meta-exception under `:excepted-by`, so the
  same knowledge prints the same report whatever order it arrived in. `believed?` is the
  boolean beside it — JTMS IN after the visible cascade, deliberately *not* gated on the
  asker inheriting the sentex's assertion context, which is the separate `:visible?` the
  map reports. Both refuse a malformed handle with `:bad-handle`, as `in?` does. The hot
  boolean path and the diagnostic forest read one visible-exception index, so they cannot
  disagree about scope. *Class:* **Additive** — two new public fns; nothing existing moves.
  [docs/api.md](docs/api.md), [docs/exceptions.md](docs/exceptions.md)

### One handle per canonical sentence

- **A bulk run's authority memo follows the handle cache's generation.** The memo that
  lets a forward-chaining run read a miss as absence outlived the cache it rests on: the
  cache empties whenever the canon stamp moves — a rule concluding `(symmetric P)` moves
  it mid-fixpoint — and every conclusion stored before the move was stored again after
  it, two handles for one sentence. The cache carries a generation now, and the memo
  drops its verdicts when it steps. *Class:* Fix; a KB that derived a declaration
  mid-chain held duplicate records. [docs/canonicalization.md](docs/canonicalization.md),
  [docs/inference.md](docs/inference.md)

- **A non-ground sentence resolves to the handle whose stored sentence it equals.** A
  pattern keys the trie α-renamed, so the lookup answered every stored sentex of the same
  shape and the first was taken: two `exceptWhen` exceptions on one rule naming different
  rule variables collapsed into one — and the sick bird flew — as did
  `(defnSufficient C (kin ?x ?y))` beside `(defnSufficient C (kin ?y ?x))`. Candidates
  are now selected by stored sentence, one record read each, paid only by a non-ground
  atomic. *Class:* Fix; an exception that was silently dropped is now stored.
  [docs/exceptions.md](docs/exceptions.md), [docs/canonicalization.md](docs/canonicalization.md)

### The same knowledge in any order

- **An asymmetric twin stored in the vantage is a partner, not the sentence itself.**
  `asymmetry-problems` decided *self* by the context it was asked **from** rather than by
  the sentence's own, so a stored `(P a a)` asked from a vantage that sees more than its
  own context threw away the twin stored in that vantage as though it were itself: the
  same self tuple written in a general context and again in one that sees it was a
  reported dilemma when the specific side arrived last and silence when the general side
  did. The checks take the sentence's `home` context now; the door, where the two are one,
  is unchanged. *Class:* Fix on order independence. [docs/nmtms.md](docs/nmtms.md)

- **Metatype membership records on the mark's storage, not its belief.** `(M T)` asserted
  while `(disjointMetatype M)` was defeated was never recorded, so reviving the mark
  separated nothing — where the same four facts in the other order separated the pair —
  and a member retracted while the mark was OUT leaked its cache entry for the life of
  the KB. *Class:* Fix on order independence. [docs/taxonomy.md](docs/taxonomy.md)

- **A firing bound to a merged term is always an exception candidate.** The re-check
  narrowing compares stored bindings by argument shape while the re-evaluation rewrites
  them to the context's elected representative, so a firing bound to a retired spelling
  was never re-checked: the conclusion stood when the exception arrived after the merge
  and was swept when it arrived before. *Class:* Fix on order independence.
  [docs/exceptions.md](docs/exceptions.md), [docs/equality.md](docs/equality.md)

- **A cycle-closing `genlCx` edge condenses the relation in place.** The assert that
  closes a context cycle chains before it settles, so a firing it seeded read the
  pre-merge component and placed its conclusion on whichever member it saw, while the
  same firing re-derived after the settle landed on the term-min representative — two
  sentexes for one claim in contexts that see each other. The cyclic arm runs
  `repair-depths` now. *Class:* Fix on order independence.
  [docs/taxonomy.md](docs/taxonomy.md), [docs/contexts.md](docs/contexts.md)

- **A symmetric fact reaches a rule the same way at either position.** A symmetric fact is
  stored in one orientation and *means* both: the join probes both argument orders, and
  the trigger unified the arriving datum as written — so the combination needing the
  mirror was enumerated by nobody, and the same four sentences derived the conclusion or
  not depending on which arrived last. A `(symmetric P)` declaration arriving *after* the
  facts re-joins in full every forward rule with an antecedent over `P`, the route a
  preserved predicate already took. All 24 orderings of {declaration, rule, two facts}
  agree; 12 did not. *Class:* Fix on order independence.
  [docs/inference.md](docs/inference.md), [docs/inherit.md](docs/inherit.md)

- **A symmetric fact answers twice when the pattern asks twice.** All three retrieval
  paths deduped the mirror probe by *handle*. For a palindrome that is right; but a
  pattern whose arguments are both variables binds one stored fact twice and differently,
  and the second binding was read as a repeat and dropped. It bit only where such a
  literal **leads** the join — a plan decision — so the same knowledge answered or not
  depending on which literal was cheapest: 48 of 120 orderings, `prove` failing in exactly
  those. Every path keys the dedup on the handle *and* the bindings — including the `rete`
  sweep's alpha matcher, which reimplements the probe rather than reusing it, and owes the
  identical set the reference path returns. *Class:* Fix on order independence.
  [docs/indexing.md](docs/indexing.md), [docs/inference.md](docs/inference.md)

- **A block condition is one question, asked under one spelling.** An `exceptWhen`
  conjunct and an `(unknown S)` inner query were evaluated as written, while the firing's
  bindings were rewritten to the class representative at re-check and not at derive time —
  and the conjunct's own constants were never rewritten at all. The goal named a spelling
  the KB no longer answers under, and the honest empty read as *not excepted* — and, for
  `unknown`, as *absent*, which draws a conclusion rather than failing to withdraw one.
  Over 24 arrival orders: 6 diverged on a retired binding, 12 on a retired constant, and
  an `unknown` over either was wrong in all 24. *Class:* Fix on order independence.
  [docs/exceptions.md](docs/exceptions.md), [docs/naf.md](docs/naf.md)

- **The derivation path reaches every integrate arm the rebuild does.** A forward-derived
  sentex ran only the closure arms, so a rule-derived `(except (sentexHandle H))` queued
  no firing for the sweep and a rule-derived `(M T)` for a disjoint metatype separated
  nothing — until a restart replayed the store and disagreed with the running KB.
  *Class:* Fix; the live KB and the recovered one answer alike.
  [docs/taxonomy.md](docs/taxonomy.md), [docs/exceptions.md](docs/exceptions.md)

### Storage and the durable log


- **A dedup probe reads the exact leaf, not a match of it.** `find-sentex-handle` asked
  `p/lookup` for the sentex's own trie key, and a key carrying a variable — which every
  non-ground key does, since keys are α-renamed — is a *wildcard* there: it fanned over
  every stored sentex of that shape and read the record of each to tell them apart, at a
  positional read and a nippy thaw apiece on a paged store (2,779 µs a call against 13, at
  800 candidates). `p/leaf-at` reads the node the path names and nothing else, which is
  the whole candidate set: anything at another leaf is another sentence. *Class:*
  **Breaking** — one method added to the `IndexStore` seam, so an out-of-tree index
  implements `leaf-at`; it is the leaf handles at an exact path, which every trie already
  holds. *Migration:* implement `leaf-at`; the shipped backends all carry it.
  *Breaks:* `leaf-at`, `IndexStore`, `find-sentex-handle`
  [docs/indexing.md](docs/indexing.md), [docs/storage.md](docs/storage.md)

- **An append is all or nothing.** A write that failed partway through a frame left a
  length prefix promising bytes that never followed, and the next dirty open walked from
  it into the middle of a later frame, truncated there, and tombstoned every slot past
  that point — records fsynced by later ticks. The log is set back to its pre-write
  length before the failure travels, and a WAL batch packs into one buffer and one write.
  *Class:* Fix; a durable store could lose committed records to a partial write.
  [docs/storage.md](docs/storage.md)

- **A compaction that fails past its commit point retries, then refuses.** Once the
  commit marker is written the temps are the truth and the live log is truncated before
  the copy, so a failure there left it half-copied while the session kept reading it. The
  install is retried under the kind lock; a second failure flips the kind into a failed
  state where every read and write refuses with `:compaction-failed` until the store is
  reopened. *Class:* **Additive** — one new refusal `:type`.
  [docs/storage.md](docs/storage.md)

- **The durable token dictionary is keyed as the in-RAM one is.** The token log's forward
  map keyed on Java `.equals`, the `TokenDict` it reloads into on `hasheq` — under which
  `2` and `(int 2)` are one token — so an integral pair minted a second durable id and
  every later open read `:torn-snapshot`. *Class:* Fix; an index snapshot over numeric
  arguments now reloads. [docs/storage.md](docs/storage.md), [docs/indexing.md](docs/indexing.md)

- **...and a log that already holds such a pair is repaired, not rediagnosed forever.**
  Keying the map fixed what gets written; a log written before it still held both frames,
  and every open reloaded one entry short, threw `:torn-snapshot` naming the wrong cause,
  rebuilt the index from the records, and snapshotted it against the same unrepairable
  log — so the next open paid for it again. The open that meets one drops the commit
  marker, rewrites the log without the duplicate, and declines as `:duplicate-tokens`,
  naming what happened. *Class:* Fix; one open repairs it and the next maps its image.
  [docs/storage.md](docs/storage.md)

- **A stray unindex touches nothing.** Removal decremented every counter on the path
  without looking, so one unindex of a handle that was never at the leaf took a live
  sibling's nodes out of the trie. Both the flat and columnar backends probe the leaf
  first. *Class:* Fix; a double retraction could unindex a believed sentex.
  [docs/indexing.md](docs/indexing.md)

- **A durable fork gates and rebuilds its own half through the merged mount.** A fork's
  own index half is its delta over the base — copy-on-write counters, tombstones,
  removal records — not an index of its own records, but the coverage gate held it to one
  and so rebuilt on every remount, dropping every removal (a retracted inherited fact
  reappeared) and shadowing the base's counters. Both gates read the merged mount now, as
  a plain disk KB does. *Class:* Fix; a remounted fork answered with facts it had
  retracted. [docs/overlay.md](docs/overlay.md)

- **A bulk load's transient takes only its own backend's writes.** The binding was a bare
  per-thread volatile, so while a load ran over one backend every other memory-backend
  write on that thread landed in its transient — invisible to its own backend, then
  persisted into the wrong map. *Class:* Fix; concurrent KBs on one thread no longer
  cross. [docs/storage.md](docs/storage.md)

- **A frame reader releases its file when the consumer stops early.** The chunked and
  windowed readers closed only at EOF, so a refused snapshot frame or an aborted import
  leaked the handle; a failure inside the seq closes before the throw travels, a Cleaner
  closes a dropped seq, and `close-frames!` closes on request. *Class:* Fix.
  [docs/storage.md](docs/storage.md)

- **A divergent unindex says so, and a counter is a cardinality.** The leaf gate that made
  a stray unindex a no-op also made a genuine index/record divergence indistinguishable
  from one — and the caller deletes the record either way, so the trie would keep handing
  out a handle whose record is gone. It logs `::unindex-absent` now. Beside it,
  `kv-decrement` is floored at zero: every counter the index writes is a cardinality and
  `plan/prefix-estimate` divides by them. *Class:* Breaking for an out-of-tree
  `KvBackend`, which now fails `kv_backend_test` if it lets one go negative.
  *Migration:* floor `kv-decrement` at zero in an out-of-tree `KvBackend`; the shipped
  backends already do.
  *Breaks:* `kv-decrement` [docs/indexing.md](docs/indexing.md)

- **Record fetches are counted, beside the index reads.** A probe that narrows to one
  index read and then pages a record per candidate scores well on the tally that existed
  and badly on the one that did not — which is how a probe reading 2779 µs where it now
  reads 13 shipped. `vaelii.impl.profile` carries `:fetches` by kind. *Class:* **Additive**
  — one new snapshot key. [docs/storage.md](docs/storage.md), [docs/profile.md](docs/profile.md)

### Inference

- **A term-growing subgoal is cut at a ceiling over the query's depth.** `prove`,
  `provable?`, level 7 and `explain-levels` did not terminate on a rule that nests a
  function application around a head variable — `(implies (p (SuccFn ?x)) (p ?x))` —
  because the loop guard keys on the goal and every expansion asks one nobody has asked.
  A subgoal nesting compound terms more than `:max-term-growth` (default 8) deeper than
  the query is cut as a repeated key is. *Class:* Breaking; a search that ran forever now
  stops. *Migration:* raise `:max-term-growth` for a proof that genuinely builds terms.
  *Breaks:* `:max-term-growth`, `prove`, `provable?`, `explain-levels`
  [docs/inference.md](docs/inference.md), [docs/levels.md](docs/levels.md)

- **A variable-functor goal expands every rule, not none.** `(?p Tom ?y)` answered stored
  facts through the argument roots and silently expanded no rule at all, because the
  consequent probe looked the variable up as a predicate. Candidates now come off the
  rule roster, with the functor bound per rule. *Class:* Fix; an open-predicate query
  returns derived answers. [docs/inference.md](docs/inference.md),
  [docs/indexing.md](docs/indexing.md)

- **A deadline stops the node engine at the next expansion, not the next answer.** One
  pull of the search seq steps until a node yields, so a wide unproductive frontier ran
  whole before the budget was seen — 25–40 ms for a 2 ms budget. The session is driven
  under the budget now, with the same partial-result contract. *Class:* Fix on the
  anytime contract. [docs/anytime.md](docs/anytime.md)

### Contradiction solving

- **A solve that returned no answer set is not read as defeat-everything.** Every reader
  maps an absent atom to *defeated*, so an interrupted or unknown result defeated every
  contested assumption and labeled every choice head false. `edge-solver` degrades to the
  local solver and logs it; `kept-of`, `enumerate-optima` and `classify-program` refuse
  with `:solver-failed`. `:unsat` keeps its reading. *Class:* Breaking; a caller reading
  a solve that did not finish now meets a refusal instead of a silent verdict.
  *Migration:* catch `:solver-failed` where a solve may be interrupted, or lift the time
  limit with `VAELII_ASP_TIME_LIMIT=0`.
  *Breaks:* `:solver-failed`, `:interrupted`, `kept-of`, `enumerate-optima`,
  `classify-program`
  [docs/asp.md](docs/asp.md), [docs/solving.md](docs/solving.md)

- **Every solve is bounded by a time limit.** A hard program wedged the single writer:
  neither backend carried one. `VAELII_ASP_TIME_LIMIT` (default 60 s, `0` lifts it)
  reaches clasp as `--time-limit` and in-process clingo as an async solve cancelled when
  the budget is spent, both reporting the new `:interrupted` status; the clingo handle is
  closed in a `finally`. *Class:* **Additive** — one setting and one status; a solve that
  finished inside a minute is unchanged. [docs/asp.md](docs/asp.md),
  [docs/operations.md](docs/operations.md)

- **The solve sweep takes a context's extent, not everything about it.** `clear-context!`
  retracted every sentex *mentioning* a solve context from any context, so a user's own
  `genlCx` edge into a classification context was retracted by `classify`. The sweep
  takes the extent plus the placement edges the solve itself minted.
  *Class:* Fix. [docs/labeling.md](docs/labeling.md)

- **One ruling per arbiter per dispute.** `resolve-by-majority` re-ruled without looking
  at what stood, so a house that swung got a second known-true ruling beside the first —
  a clash no ruling could settle. A standing ruling for the other side is retracted
  first, and the majority path withdraws its own when the count dissolves into a tie.
  *Class:* Fix, plus one new public read (`standing-rulings`) and a `:withdrawn` key on
  the result. [docs/koinii.md](docs/koinii.md)

- **...and a ruling is found again for every dispute it settles.** Canonical dedup gives
  one sentex per sentence and context, so an arbiter upholding one claim against two
  opponents stamps a single handle twice — and the `:adjudication` tag held one dispute
  id, the later. The earlier dispute then read no standing ruling, skipped the guard
  above, and took a second monotonic ruling beside the first; two orders of the same
  operations gave different belief sets. The tag holds a set, the id is compared sorted,
  the retract-and-replace is one `edit!`, and an arbiter who is a **party** is refused
  (`:arbiter-is-party`) — a ruling lands in the arbiter's own context, so for a party it
  restamped their own claim or deleted it. *Class:* Breaking on one impl read
  (`who-ruled` answers `:dispute-ids`), Additive for the refusal.
  *Migration:* read `who-ruled`'s `:dispute-ids` as a set where a single id was expected,
  and name an arbiter who is not a party to the dispute.
  *Breaks:* `who-ruled`, `:dispute-ids`, `:arbiter-is-party`
  [docs/koinii.md](docs/koinii.md)

- **The edge solver refuses rather than degrades when a backend is present.** An
  interrupted or failed solve decided nothing, then fell back to the local solver — whose
  answer *differs*, and is documented as differing. So belief depended on whether a solve
  finished: one settle round timing out and the next not produced a belief set neither
  solver would give. It now decides nothing and says so. *Class:* Breaking; a caller
  reading `{:defeat :violated}` also gets `:error`.
  *Migration:* handle `:error` where the degraded local answer was relied on, or lift the
  bound with `VAELII_ASP_TIME_LIMIT=0` so the solve finishes.
  *Breaks:* `:error`, `edge-solver`, `:solver-failed`
  [docs/asp.md](docs/asp.md)

- **A backend failure is a result, not an exception through a settle.** Nothing caught
  `:solver-failed` or `:solver-unavailable`, so a native failure unwound
  `resolve-contradictions` after a round had already defeated things: a half-arbitrated
  KB, stale `:conflicts`, and `reset-touched!` never run. The settle now finishes with the
  contested pair standing and logs what it did. *Class:* Fix. [docs/asp.md](docs/asp.md)

- **An infeasible program has no labeling, in every mode.** `kept-of` kept `#{}` for
  `:unsat`, but `:one` and `:sat` wrapped it as one optimum and reported `:count 1` with a
  full labeling of a world violating every hard constraint — while `:all` correctly
  reported none. *Class:* Breaking; the two modes documented as feasible at scale now
  report `:count 0 :reason :unsatisfiable`. *Migration:* read `:count` rather than
  treating a returned labeling as evidence the program was feasible.
  *Breaks:* `:unsatisfiable`
  [docs/solving.md](docs/solving.md)

- **A negated choice literal binds its own variables.** A hard constraint whose variable
  occurs only under a negated choice head grounded to nothing at all —
  `(set/hardConstraint (implies (not (pick ?c)) (mustPick ?c)))` contributed no nogood and
  the labeling violated it, with no refusal and no warning. This is the at-least-one idiom
  the encoding's own docstring gives. *Class:* Fix. [docs/solving.md](docs/solving.md)

- **A run that cannot replace the last one refuses instead of writing beside it.** A
  labeling context whose ownership marker was retracted, or one written into, made the
  replace-on-rerun sweep a no-op — so the next run accreted a second grounding beside the
  first and `classify` aggregated both, which is what the namespace says must never
  happen. *Class:* Additive — one new refusal `:type` (`:labeling-run-blocked`).
  [docs/solving.md](docs/solving.md), [docs/troubleshooting.md](docs/troubleshooting.md)

- **The `:violated` reading is content-ordered.** The contradiction sort key omitted the
  sentence, so two nogoods tying on members, priority and hardness interned in arrival
  order and the report came back permuted. The program text was identical either way, so
  belief was never at risk — only the reading. *Class:* Fix. [docs/asp.md](docs/asp.md)

- **`VAELII_ASP_TIME_LIMIT` bounds one solve, and an operation makes several.** Both the
  setting's docstring and the operations row framed it as the single writer's exposure. A
  classification is two solves, `do/labeling` three, and a settle one per defeat round —
  each with the whole budget. The docs tabulate the multipliers and a test pins the counts
  so the table cannot drift. *Class:* neither label; what changed is what the KB says
  about itself. [docs/asp.md](docs/asp.md), [docs/operations.md](docs/operations.md)

### Equality, taxonomy and dates

- **`kbo>` decides an equal-weight pair that differs at a constant.** The equal-weight
  branch took the first argument of both sides unconditionally, so
  `(equals (UnitFn Meter ?n) (UnitFn Metre ?n))` reached the lexicographic step on two
  atoms and `assert` threw; on the derivation path it aborted the chaining fixpoint. The
  comparison now runs on roots and recurses only where both sides are compounds.
  *Class:* Fix; a schematic equation that threw is now oriented.
  [docs/equational.md](docs/equational.md)

- **`del-equality!` drops the retracted handle from the partition's `:out`.** An equality
  retracted while defeated left its handle in the OUT set for the life of the KB.
  *Class:* Fix. [docs/equality.md](docs/equality.md)

- **A datetime bounds its date and time halves separately.** Only the total field count
  was checked, so `"2000T13:00"` read as a thirteenth month and a day zero, and
  `subinterval?` nested intervals the strings never named. Every field is now range-
  checked behind a full date. *Class:* Refusal; a string that parsed into nonsense is
  refused. [docs/time.md](docs/time.md)

### The API, the web and jobs

- **`query` refuses an option it does not read.** The roster was open, so `{:max-deph 3}`
  or `{:proof true}` answered facts-only with nothing to say a rule was never expanded.
  `query-opt-keys` is public, as `assert-opt-keys` is, and covers the door's dial and the
  engine's reads. *Class:* Breaking; a key `query` ignored is now `:unknown-option`.
  *Migration:* spell the rostered key.
  *Breaks:* `:unknown-option`, `query-opt-keys`, `query`, `query?`
  [docs/api.md](docs/api.md)

- **A write door judges and writes one KB, resolved once per request.** The holder was
  dereferenced up to four times per write, and `/kbs/activate` takes no monitor — so a
  switch landing between the refusal and the write put an edit on a KB whose loader is
  this process's writer, breaking the single-writer contract from the browser.
  *Class:* Fix. [docs/web.md](docs/web.md)

- **`reset-registry!` waits for a cancelled job to stop before forgetting it.** An
  unsettled chain job lost its entry — and with it the writer claim — while its thread
  kept writing. Every job is cancelled, waited on for up to 30 s, and any that will not
  settle is kept and logged. *Class:* Fix. [docs/operations.md](docs/operations.md)

- **One export at a time is checked and claimed as one step.** The read of `exporting?`
  sat outside the monitor, so two requests arriving together both started, and a repeat
  source's entry key was computed outside it too. *Class:* Fix.
  [docs/catalog.md](docs/catalog.md)

- **`::context` admits a context-denoting application.** The doors take a ground
  `(CxTimeFn …)` and reify it, but the spec was `symbol?`, so under `instrument` a write
  into a time-indexed context was refused before the door saw it. *Class:* Fix under
  `instrument` only. [docs/context-nat.md](docs/context-nat.md)

- **`serve`'s `-main` passes the thread-pool size, as `start` does.** The command-line
  daemon ran on Jetty's default, so the pinned `max-parked << http-threads` relationship
  held for the tests only. *Class:* Fix. [docs/operations.md](docs/operations.md)

- **A refusal names the KB it judged, not the active one.** The write doors resolve the
  holder once and hand that KB to both the refusal and the write, precisely because
  `/kbs/activate` re-points it at any moment — and then all three refusal arms printed the
  active entry's name, which is the one KB the page can be sure it did *not* judge.
  *Class:* Fix. [docs/web.md](docs/web.md)

- **`argue` holds `query`'s roster at its own door, and each debugger door rosters what it
  reads.** `argue` called `query` only when `:max-depth` was present and `ask` otherwise,
  so the misspelling the roster exists to catch was still silent there — turning a
  derivable fact into a false `:unknown`, which `argue`'s own docstring names as the thing
  to prevent. And the two debugger doors took the union roster while overwriting
  `:strategy` and `:proof?` themselves, so a caller's strategy was accepted and discarded.
  *Class:* Breaking; a key these doors ignored is now `:unknown-option`.
  *Migration:* spell the rostered key, and stop passing `:strategy` or `:proof?` to the
  debugger doors, which set both themselves.
  *Breaks:* `argue`, `search-tree`, `compare-tacticians`, `:unknown-option`
  [docs/api.md](docs/api.md)

### Efficiency

None of these change an answer; each is pinned by a test that fails on the old cost.

- **The forward join takes its argument lead only where there is a fan to collapse.** A
  functor with no sub-predicates has none, and `res/match-pattern`'s own fast path answers
  it in one probe — where the lead paid three volatiles, a pattern memo and an extra count
  probe for nothing. Two index reads per firing on the commonest join shape.
  [docs/inference.md](docs/inference.md)

- **The supersession refresh takes the region the finish already read.** `settle-finish`
  reads the relabelled region once into a delay so its consumers do not each pay for it —
  on the dense network a read boxes the whole bitmap, KB-sized on a rebuild — and this one
  consumer read it again, ungated, so a KB that had never merged anything materialized the
  region to reconcile an empty superseded set. [docs/nmtms.md](docs/nmtms.md)

- **A clingo drain keeps the models its mode reads.** Every model was retained though the
  classify modes read only the last: 618 accumulated on a 400-node colouring at a two
  second budget, and with the limit lifted it is unbounded. [docs/asp.md](docs/asp.md)

- **An export drains the writes it must and holds nothing after.** The route wrapped the
  whole walk in the write monitor, against its own comment, so unloading any KB during a
  multi-minute dump parked a Jetty worker for the dump's length — and `/kbs/unload` is the
  one write route the refusal does not turn back first. [docs/web.md](docs/web.md)

- **Four new counted gates, because a ratio cannot see a constant.** `lein perf` asserts
  growth and the `*_cost_test` files assert exact integers; between them sat three classes
  nothing could see, each of which shipped a defect this release fixes. Now pinned: what
  one firing costs at the trigger position, what a probe costs in *record* fetches, that a
  bounded read allocates for the answer rather than for the request, and how many times a
  settle materializes its region. A fifth prices the durable write path, counted and as a
  ratio — a path `lein perf` had no check for at all.
  [docs/profile.md](docs/profile.md)

- **One `except` no longer turns `context-down` into N filtered walks.** The active branch
  filtered every descendant through an unmemoized reachability walk whenever the whole-KB
  roster held any `except` at all: on a 1500-context lattice, 2 µs → 46 ms after one
  unrelated `(except (sentexHandle h))`, paid per `genlCx` write, per multi-context
  placement and per prover scope. The filter is gated per relation, the filtered answer
  memoized on the visibility generation. [docs/taxonomy.md](docs/taxonomy.md)

- **A settle reads its relabelled region once per pass.** `touched` was materialized six
  to twelve times per settle, each read copying the dense network's whole bitmap into a
  boxed set — the KB's size on a rebuild, on the path that network exists to make fit.
  Region members' records are read once per settle rather than per defeat round, and the
  except scans sit behind a non-empty except roster. [docs/nmtms.md](docs/nmtms.md)

- **A negated antecedent is keyed by its body's predicate.** All of them filed under the
  one key `not`, so each arriving negation ran the rule view over every position of every
  rule negated anywhere. [docs/indexing.md](docs/indexing.md)

- **A bound-argument antecedent joins through the argument lead.** A join to confirm a
  single membership walked the trie once per member of the antecedent's sub-predicate
  closure — 364 on the starter, six figures under a `thing`-rooted antecedent — where the
  backward path answers it with one slot read. [docs/indexing.md](docs/indexing.md)

- **A candidate rule's view is built once an antecedent unifies**, not for every candidate
  of every datum; the preservation gate and the symmetry test are read once per chaining
  run, invalidated when a firing places a declaration. [docs/inference.md](docs/inference.md)

- **`explain` costs its report off the ranking's memoized reads**, where it re-costed
  every literal with raw index reads — and the node engine pays `explain` per enqueued
  child. [docs/inference.md](docs/inference.md)

- **`find-terms` with a `:limit` selects its n smallest** instead of sorting every hit;
  the browser's search box asks for 201 of the vocabulary per keystroke. The answer is
  the stable sort's prefix, ties included. [docs/api.md](docs/api.md)

- **The web view holds the type set by reference**, read only when a page asks — it copied
  ~125k symbols per request, `/jobs` and `/caches` included. [docs/web.md](docs/web.md)

- **An LLM tool result is printed into a bounded writer**, not `pr-str`'d whole and then
  cut: a broad read realizes a few dozen records to show 4,000 characters, where it
  printed megabytes to keep four kilobytes. [docs/llm.md](docs/llm.md)

## 0.10.0 — 2026-08-20 — "more than one agent over one knowledge base"


- **Koinii: several agents coordinate over one shared knowledge base.** A new layer,
  `vaelii.impl.koinii.*`, lets independent agents assert, reply, dispute and resolve over a
  **common** store — agents *are* contexts, moves *are* sentexes, and the change feed is the
  medium, so coordination is a small vocabulary in the KB itself rather than a transport
  bolted on the side. It runs in two shapes: one single-writer daemon several clients share,
  or independently-replicated seats that reconcile through content-addressed moves. The
  modules are `identity` (a SHA-256 / multihash content locator, a canonical encoder and a
  Merkle commit tree), `channel` (subscribe / reply over the change feed), `dispute`,
  `adjudication` (notify-plus-arbiter, majority-vote resolution and honest ties), `catchup`
  (a CDC snapshot-and-tail), plus `deref`, `belief` and `speech_acts`. Nothing in
  `vaelii.core` loads it, every module rests on the public core API exactly as
  `vaelii.impl.argue` does, and the starter never walks it, so a KB pays for koinii only
  when a deployment loads a koinii context. *Class:* **Additive** — a new optional layer
  and two shipped contexts (`resources/kb/koinii/`); no existing behaviour changes.
  [docs/koinii.md](docs/koinii.md), [docs/feed.md](docs/feed.md)

- **Belief projection: what an agent holds true.** `(believes Agent P)` is answered by
  proving `P` inside `Agent`'s own context rather than the asker's, so two agents may hold
  contradictory beliefs without the KB contradicting itself — the context lattice already
  does the work, and this adds one convention and one prover over it, with no new belief
  primitive and no change to the JTMS, taxonomy or index. An agent symbol names its context
  by a fixed bijection (`Alice ↦ CxAgentAlice`), now public as `context-of-agent` /
  `agent-of-context`. `modalPredicate` and `register-modal-predicate!` open the same
  projection to `knows` / `desires` / `intends`. It is deliberately not a modal *logic*:
  no K/T/4/5 schema, and a nested `(believes A (believes B P))` projects only where the
  grant is visible. *Class:* **Additive** — new vocabulary and two public reads; nothing
  existing changes. [docs/belief.md](docs/belief.md)

- **A context can be a reified function application, and its `genlCx` edges compute
  themselves.** A `Cx*Fn` application reifies to a `cx/` **context** — a constant a sentex
  is stored in and a `genlCx` node — where an object-denoting NAT still reifies to a `nat/`
  *term* refused as a context. `(contextDenotingFunction CxTimeFn)` declares the family, and
  a declared argument ordering makes one such context a computed **spec** of another with
  nobody asserting the edge: `(CxTimeFn CxMonad (DatetimeFn "2000-01"))` is inside
  `(CxTimeFn CxMonad (DatetimeFn "2000"))`, so a fact in the year is visible from the month.
  The first dimension is `DatetimeFn`, a structural (unreifiable) ISO-8601 interval whose
  containment is field nesting, computed by a pure bounded comparison the structural-`genlCx`
  producer runs inside the settle/relabel loop. *Class:* **Additive** — a new context shape
  and vocabulary; object NATs are refused as contexts exactly as before.
  [docs/context-nat.md](docs/context-nat.md), [docs/nat.md](docs/nat.md)

- **Mention-opacity: a quoting function reads its argument by spelling.** A
  `quotingFunction` carries a `:quoting` property, and inside such a term an argument is a
  **mention**, not a use: it is opaque to rewrite, reification and reduction, and congruent
  only up to spelling — two mentions are the same iff they are spelled the same, never
  because equality or a rewrite would fold them. The `why-not` displacement map is
  mention-aware to match. A companion `Unquote` / `Quasiquote` metalinguistic constructor
  (`vaelii.impl.quasiquote`) marks the holes a quasiquoted term splices back in.
  *Class:* **Additive** — a new predicate property and constructor; a term naming neither
  reads exactly as before. [docs/glossary.md](docs/glossary.md), [docs/argtypes.md](docs/argtypes.md)

- **`quotedArg` types an argument as a term against a syntactic type.** The mention twin of
  `arg`: where `arg` types what an argument *denotes*, `(quotedArg pred n type)` types the
  argument **as a term** — its EDN kind (`string`, `number` with `integer` below it,
  `symbol`) checked through `genl` against a syntactic type. `(quotedArg nameOfGuy 1 string)`
  refuses `(nameOfGuy 5)` and admits `(nameOfGuy "Bob")` with `:type :quoted-arg-type`. It is
  checked, never entailed, and open-world about an untypeable kind and about a declared type
  outside the syntactic lattice, so an imported Cyc quoted-type never false-convicts. The new
  syntactic types `string` / `number` / `integer` / `symbol` join the `genl` lattice, and the
  check sits behind the same O(1) count gate as `interArg` (+1 functor-root read per assert).
  *Class:* **Additive** — one new refusal `:type` a caller may now meet and inert vocabulary
  now read; no existing declaration changes behaviour.
  [docs/argtypes.md](docs/argtypes.md), [docs/glossary.md](docs/glossary.md)

- **The argument-constraint family is renamed to a shorter, regular scheme.** `argIsa →
  arg`, `argGenl → genlArg`, `interArgIsa → interArg`. `arg` is core grammar — self-
  referential (`(arg arg 1 predicate)`) and the predicate every typed relation declares its
  argument types with — so the rename sweeps the engine, the shipped ontology, the docs and
  the tests together. The tokens are case-distinct camelCase, so internal kebab-case helpers
  are untouched, and the semantics are identical. *Class:* **Breaking** — three shipped KB
  predicate names changed, so a KB text, rule or `isa?` naming an old spelling answers
  nothing. *Breaks:* `argIsa`, `argGenl`, `interArgIsa`. *Migration:* rename all three in
  your KB text — `argIsa → arg`, `argGenl → genlArg`, `interArgIsa → interArg`; nothing else
  changes. [docs/argtypes.md](docs/argtypes.md), [docs/inherit.md](docs/inherit.md)


- **A sentence carrying a non-serializable value is refused at every door.** A value nippy
  cannot freeze and thaw — a function, an atom, a non-serializable object — stored in the
  `:memory` backend and then threw at write time on the first `:disk` backend, so the same
  assert succeeded or failed by backend. `checks/check-encodable` refuses it up front at
  every persisting door (`assert`, hence `assert-rule` / `assert-many` /
  `bulk-assert-facts!`, and `assert-inert`) with `:type :not-encodable`, and `check`
  predicts it. The vocabulary and literals — symbols, keywords, strings, numbers, chars,
  booleans, `nil`, and any vector/map/set of them — clear without a freeze (~56 ns/assert,
  zero index reads); a leaf outside that set goes through the freeze/thaw pair the disk
  backends run and is refused if either throws. *Class:* **Refusal** — accepting the value
  stored a sentence no `:disk` KB could recover, so no working caller is broken.
  *Breaks:* `:not-encodable`. *Migration:* replace the non-serializable leaf with data.
  [docs/storage.md](docs/storage.md)

- **New public reads for handles and un-stored canonical form, and `argue` is public.**
  `handles` returns every live sentex handle in the KB — the whole-KB counterpart to the
  context- and query-scoped readers. `sentex-handle` / `sentex-handle?` / `handle-id` build
  and read the `(sentexHandle <id>)` term a meta-sentex predicates about another sentex with,
  and round-trip. `canonical-sentex` returns the canonical sentex for a sentence in a context
  **without storing it** — the un-stored counterpart of `sentex`, built through the store's
  own constructor so symmetric arguments sort and comparisons fold. And `argue`, the four-
  valued epistemic status of a ground assertion, is now a `vaelii.core` public rather than an
  `impl` read. *Class:* **Additive** — five public reads; nothing existing changes.
  [docs/api.md](docs/api.md)

- **The fast gate drops perf; `release-gate` keeps it.** `lein gate` is now lint + test
  only — fast enough before every commit — and prints "perf owed" when a hot-path change
  lands without a perf run. `lein release-gate` is lint + test + perf (~5m), for a tag or a
  perf-sensitive land; CI and `assert_cost_test` also cover the perf floor.
  *Class:* **Additive** — a build-command split; no engine behaviour changes.

## 0.9.0 — 2026-08-17 — "the truth-maintenance network defaults to dense"


- **The dense truth-maintenance network is the default.** `open-kb`'s `:tms` defaults to
  `:dense` (bitmaps + primitive-keyed maps) rather than `:reference` (the persistent-map
  network). `jtms_dense_oracle_test` proves the two belief-identical op by op, so no
  answer, match or ordering changes; what changes is resident RAM — measured flat per node
  from 20k to 1M, ~3.8× less at corpus scale (~9.1 → ~2.35 GB on an 11.5M-sentex corpus, a
  ~21% whole-KB cut), which an engine built for one large node holding 100M should take by
  default. Wall is unchanged. *Class:* **Breaking** — a documented default changes, and
  `catalog/footprint`'s `:tms` estimate drops 467 → ~101 B/sentex to match. No answer,
  match or ordering moves — only the representation and the footprint number.
  *Breaks:* the `:tms` default. *Migration:* pin `:tms :reference` to keep the
  persistent-map network and the old footprint figure.
  [docs/density.md](docs/density.md), [docs/nmtms.md](docs/nmtms.md)

- **The dense network gives a concurrent reader a consistent view.** A reader thread beside
  the writer — the web browser over a REPL's KB, the shape the single-writer contract calls
  supported — now sees belief either fully before or fully after a relabel, never a
  partially-applied one, matching the reference. The dense network coordinates through a
  `StampedLock`: writers take the exclusive stamp, the hot point reads (`in?`) run
  optimistically and validate, iterating reads take a shared stamp. Lock-free in the steady
  state, and the dense probe stays ~9× faster than the reference's hash-set lookup even so
  (≈19 ns against ≈180 ns per `in?`). *Class:* Additive — no answer, match or API changes;
  a race that could tear or fault a read on the new default now cannot. `jtms_concurrency_test`.
  [docs/density.md](docs/density.md), [docs/storage.md](docs/storage.md)


- **Four relation properties, enforced.** `irreflexive` refuses a self tuple `(P a a)` at
  the door (`:type` `:irreflexive`), the strict counterpart of `reflexive` and stronger
  than `asymmetric`, which admits the self tuple. `antiSymmetric` resolves by *merging*: a
  believed converse `(P b a)` beside `(P a b)` derives `(equals a b)` and unifies the two
  arguments, the antisymmetric twin of what `functional` does with two symbol values, over
  the same three arrival directions; a converse no equality could reconcile (two numbers)
  refuses instead (`:type` `:anti-symmetric`). `equivalenceRelation` needs no engine code:
  three shipped forward rules derive `symmetric`, `transitive` and `reflexive`, each
  enforced in turn. `antiTransitive` is **declared and its chain conviction deferred** —
  `(P a b) ∧ (P b c) ⇒ ¬(P a c)` is a three-party nogood the settle machinery forms only
  pairwise — so what is enforced is its classification and `(disjoint transitive
  antiTransitive)`. Each property is one predicate on the collapsed model, `(genl X
  binaryPredicate)` with no derived twin, and the lattice sits on the bare marks;
  `(disjoint symmetric antiSymmetric)` is skipped, `equals` being both. *Class:*
  **Additive** — two new refusal `:type` keywords a caller may now meet, and vocabulary
  that was inert before is now read; no existing declaration changes behaviour.
  [docs/taxonomy.md](docs/taxonomy.md), [docs/nmtms.md](docs/nmtms.md)


- **A subsumption rests on its strongest route, not its shortest.** When a fact reaches a
  rule antecedent of a different functor across the `genl` closure, the conclusion is
  capped at the defeat class of the path the match climbed — chosen breadth-first, the
  *fewest* edges, so a conclusion read `:default` whenever the shortest route ran through a
  defeasible edge and a longer all-`:monotonic` route existed. The walk takes the **widest
  bottleneck**: the route whose floor is highest, tie-broken by depth then content, which
  `kb/reach-strength` reads directly. *Class:* **Breaking** — `defeat-class` of a
  conclusion reached across a taxonomy that offers two routes at different strengths can
  rise from `:default` to `:monotonic`; no answer *set* changes. *Breaks:* `defeat-class`.
  *Migration:* re-read `defeat-class` on such conclusions; the shortest-path placement
  witness is unchanged. [docs/taxonomy.md](docs/taxonomy.md),
  [docs/defenses.md](docs/defenses.md)


- **An algebraic property is one predicate, not a mark and a twin.** The derived predicate
  types `symmetricPredicate` / `asymmetricPredicate` / `transitivePredicate` /
  `reflexivePredicate` / `functionalPredicate` are removed, along with the
  `PredicateTypeProver` and the CxCore rules that materialized them. Each **mark** carries
  the classification itself: through `(genl symmetric binaryPredicate)` in CxCore it *is* a
  `binaryPredicate` subtype, so `(symmetric siblingOf)` makes `isa? siblingOf symmetric`
  and `isa? siblingOf binaryPredicate` hold, and `ask (symmetric ?p)` enumerates by
  ordinary retrieval. `(transitive genl)` is stored and queryable but held out of the
  `:transitive` property machinery, `genl` / `genlCx` being the taxonomy's own closure
  relations. *Class:* **Breaking** — a query, rule or `isa?` naming a `…Predicate` type now
  answers nothing; and because the surviving mark is a `decontextualizedPredicate`, its
  membership is read KB-wide rather than only in the context that once derived the twin.
  *Breaks:* `symmetricPredicate`, `asymmetricPredicate`, `transitivePredicate`,
  `reflexivePredicate`, `functionalPredicate`. *Migration:* replace `(…Predicate P)` with
  the bare mark, which answers the same membership.
  [docs/taxonomy.md](docs/taxonomy.md)

- **A rule may conclude a variable predicate.** `(implies (holds ?p ?x ?y) (?p ?x ?y))`
  now asserts, fires, and answers backward, where it was refused `:not-indexable`. The
  split is by position: a variable functor in the **consequent** is bound by a concrete
  antecedent (range restriction guarantees it), so the rule fires forward with the
  predicate ground and its consequent is filed under one catch-all bucket that "what could
  conclude P?" unions in; a variable functor in an **antecedent** stays refused, because it
  names no predicate for an arriving fact to trigger and would join over whatever is stored
  when a concrete antecedent beside it arrives. The refusal message now says which side it
  is, and a var-consequent rule carrying an `unknown` / `exceptWhen` / aggregate antecedent
  is refused `:not-stratified` — it could conclude the very predicate whose absence it rests
  on. *Class:* **Additive**; no rule that asserted before is refused, and one class of rule
  refused before now runs. [docs/indexing.md](docs/indexing.md)

- **The search a query would run, as data — and a debugger over it.** Two new public
  reads open the node engine's search. `search-tree` returns the tree a bounded backward
  search actually builds for a goal — every node the frontier reached, not only the path
  that answered, each with the itemized estimate that ordered it, the rewrite that
  produced it, and the answers off it. `compare-tacticians` runs the same goal under each
  tactician and returns their work and answer *sets*, so a caller can verify that every
  complete ordering finds the same answers rather than trust it. Both bound their own work
  (a node budget and a wall-clock) and return serializable data, so the browser's new
  `/inference` page — the run beside `/levels`' plan — holds no session and works under
  `--attach`. *Class:* **Additive** — two public reads and one route; nothing existing
  changes. [docs/web.md](docs/web.md), [docs/inference.md](docs/inference.md)

- **Which of my rules actually do anything — the chaining funnel.** A new public read
  `chain-report` gives the per-rule breakdown behind `chain-stats`: for every forward rule,
  how many firings it **placed**, how many it **refused** and why (`exception` / `naf` /
  `post-join` / `hidden`), or whether it stayed **silent** because no antecedent set ever
  completed. It reads `O(rules)` off the standing refusal ledger (re-decided against current
  belief) and the justification graph, so it reflects the KB as it is now and needs no
  per-run instrumentation — the counters a live funnel might have kept would only restate
  what the ledger already holds. The browser's new `/funnel` page ranks the rules by what
  is wrong (no-placement first, refusals descending), folds in the `violations` each filed,
  and runs forward chaining as a job that lands back on itself. *Class:* **Additive** — one
  public read and one route; nothing existing changes.
  [docs/web.md](docs/web.md), [docs/exceptions.md](docs/exceptions.md)


- **A rule is asked before it fires, and a definitional read is taken from where it is
  asked.** One blind spot ran through several paths: a stored-but-OUT rule still fired, or
  a read answered from a vantage that could not see the declaration it rested on. The two
  re-join paths (`rejoin-qualitative`, `rejoin-preserving`) ask `rule-believed?` as the
  trigger path always did, so a defeated rule reached off the storage-posted antecedent
  index neither fires nor files a `violations` entry against a rule the KB does not hold. A
  `watch` subsumes through the `genl` edges its own context sees rather than every edge; a
  functional-merge clash and ASP's auto-clash detectors read functionality, disjointness
  and same-class from the solving vantage; and `why-not` names the supersession the fact's
  own context elected rather than one a global rewrite returned. A refusal also keeps the
  depth bound its run set — live-session only, since a recovered KB rebuilds refusals at
  the default exactly as it resets derivation depths.
  [docs/inference.md](docs/inference.md), [docs/contexts.md](docs/contexts.md),
  [docs/exceptions.md](docs/exceptions.md)

- **A dotted-rest pattern retrieves the facts it matches.** A query or match whose
  sentence ends in a rest-splice — `(parentOf . ?args)`, `(?pred . ?args)` — returned
  `#{}`: its canonical trie path carries the `.` marker as a token no stored fact has, and
  no candidate branch diverted it. `res/candidate-handles` now routes a dotted pattern to
  the arity-spanning roots — a concrete functor (with any leading ground argument) reads
  its functor-scoped roots, an open functor with a leading argument the predicate-agnostic
  slot roster, and a fully-open `(?pred . ?args)` the whole fact extent — each a superset
  the existing `unify` filters to the exact set. *Class:* **Additive** — a pattern shape
  that silently matched nothing now matches; no other shape changes.
  [docs/indexing.md](docs/indexing.md)

- **A clean cold open can skip the contradiction scan.** With `vaelii.belief.snapshot` set
  (a system property, off by default), a full `recover` of a writable `:disk` KB leaves a small
  belief certificate beside the records (`<dir>/belief/`) recording whether the close found the
  store clean, and the next cold open reads it, checks that the record store's slot fingerprint
  still matches, and — if the certificate says the store closed clean — skips the closing
  settle's definitional-clash scan, whose cost is the count of standing clashes and runs to
  minutes at corpus scale, rederiving byte-identical belief. The certificate never *supplies*
  belief: it records only whether a clean close found no clash, so a moved record, a torn stamp
  or an unclean close makes the open ignore it and run the full scan it always did. With the
  property unset, `recover` computes nothing extra and is the recover it always was. *Class:* **Additive** — one opt-in switch; nothing existing changes.
  [docs/storage.md](docs/storage.md), [docs/operations.md](docs/operations.md)

- **A third durable records backend, `:sqlite`.** `open-kb` accepts `{:records :sqlite}` (the
  sugar `:sqlite`), a single-file `<dir>/records.sqlite` store the Apache-2.0
  `com.vaelii/sqlite` adapter provides — resolved lazily, so the engine carries no JDBC
  dependency and a KB that never asks for it loads none. Off the classpath, the backend
  refuses by name with the coordinate to add — the adapter is released separately, after
  this core version. `:memory` and `:disk` are unchanged, and a
  durable `:disk` index over `:sqlite` records is refused exactly as it is over `:memory`.
  *Class:* **Additive** — a new backend keyword; no existing pairing changes.
  [docs/storage.md](docs/storage.md)


- **`person` is a social agent, and `human` is the biological type.** The shipped ontology
  splits the two: `human` is `(genl human mammal)` and `(genl human person)`, while
  `person` is `(genl person physical_object)` — an entity with social agency that need not
  be alive. So `(isa X person)` no longer entails `mammal` or `animal`, which is what lets
  the social predicates (`friendOf`, `knows`, `marriedTo`) constrain their arguments to
  `person` and still admit a non-biological agent, while the biological ones (`parentOf`,
  `birthYearOf`, `fatherOf`, `motherOf`) constrain to `animal` and refuse a `person` who is
  not one. *Class:* **Breaking** — a shipped taxonomy edge changed, so a query, rule or
  `isa?` that read a `person` as a `mammal`/`animal` answers differently. *Breaks:* the
  `person` membership entailment; the biological predicates now refuse a non-`animal`
  `person`. *Migration:* type biological individuals `(isa X human)` where you relied on
  `(isa X person)` implying `mammal` or `animal`; leave non-biological agents as `person`.
  [docs/commonsense.md](docs/commonsense.md)

- **`argPreserving` is renamed `transitiveInArg`.** The meta-predicate that declares an
  argument position preserved down a `genl` edge, and its inverse, are renamed across the
  shipped ontology, engine and docs: `argPreserving → transitiveInArg`, `argPreservingInverse
  → transitiveInArgInverse`. The semantics are identical; the spelling names what the property
  is — a predicate transitive in one argument — rather than a side effect of it. *Class:*
  **Breaking** — a shipped KB predicate name changed. *Breaks:* `argPreserving`,
  `argPreservingInverse`. *Migration:* rename both in your KB text; nothing else changes.
  [docs/inherit.md](docs/inherit.md)

- **`argIsa` / `argGenl` / `interArgIsa` answer up the `genl` cone.** `(ask (argIsa petMammal 1
  animal))` now answers when `(argIsa petMammal 1 mammal)` is stored and `(genl mammal animal)`
  holds: the predicate position descends and each type position ascends — a stored declaration
  on a super-predicate answers a sub-predicate query, and one on a sub-type a super-type query,
  matching what `check` already enforces. A bounded prover walks it on demand and materializes nothing, so
  `sentexes-matching` still shows only the stored declarations. `arity` is deliberately
  excluded — a sub-predicate may carry its own signature. Closes #20. *Class:* **Additive** —
  a query that answered nothing now answers; nothing stored or existing changes.
  [docs/argtypes.md](docs/argtypes.md), [docs/inherit.md](docs/inherit.md)

## 0.8.0 — 2026-08-14 — "predicates inherit down the hierarchy"

`arity`, `functional`, `asymmetric` and the three argument
constraints descend the predicate hierarchy now — at the door and on every retroactive
pass — so a claim spelled with a sub-predicate is held to what its supers declare, and
the six arrival orders of {declaration, fact, edge} reach one set of beliefs. Beside it
two structural gaps close: a KB whose derived state was never built refuses writes rather
than accepting them unchecked, and a firing rests on the `genlCx` edges its placement was
read over, so retracting one takes the conclusion back.

**Twenty entries are Breaking**, which is what makes this a minor rather than a point
release. Eight Refusal entries batch here rather than each forcing its own, which is what
§3.8 of `CONTRIBUTING.md` designates a minor for. Every Breaking and every Refusal entry
carries its *Migration* line, and every entry links the page that carries the mechanism —
an entry here says what moved and what to write instead, and the doc says how it works.

**Triage, for a 0.7.0 caller.** This is the index to what touches something you have
written.

| If your code… | Then |
|---|---|
| asserts a sub-predicate fact under a super's `argIsa` / `argGenl` / `interArgIsa` | refused `:arg-type`; widen the declaration, move it down, or drop the `genl` edge |
| declares an `arity` that disagrees with its super's | refused whichever sentence arrives second; give the two one arity, mark either end `variableArity`, or drop the edge |
| relies on `(functional P)` or `(asymmetric P)` binding P's exact functor alone | both convict a sub-predicate's tuples now, in either arrival order |
| reads an empty `violations` as a clean bill | `:arity` and `:constraint-exposure` entries appear in arrival orders that filed none, and a retraction no longer files `:no-placement` |
| branches on `violations`' `:violation` with a defaultless `case` | `:arity-truncated` and `:arity-report-truncated` are new kinds |
| counts `:arity` entries to size a problem | both retroactive passes file at most 8 and carry the totals on a truncation notice |
| writes to a KB opened `{:recover? false}`, or loaded `:belief? false` / `:belief? :stored` | refused `:unrecovered-kb`; call `recover` (or `reindex`) first, or bind `*write-unrecovered?*` |
| retracts against such a KB | refused, where it deleted the record and left its justifications dangling |
| spells one sentence as a top-level vector — `(assert kb '[likes Tom Ann])` | refused `:shape`; write the list, and ask a conjunction with `query` or `prove` |
| passes a non-map where an option map goes, `(open-kb :nope)` among them | `:unknown-option` by name, where it threw an unnamed error |
| reads `why`'s `:because`, `why-not`'s `:missing` or `preview`'s `:antecedents` | a cross-context firing lists the `genlCx` edges it was placed over, and a descended merge names each `genl` edge once rather than once per side |
| reads `defeat-class` on a cross-context conclusion | it caps on those edges, so a known-true fact read across a `:default` context edge answers `:default` |
| re-asserts known-true content over a `:monotonic` premise | the stronger class survives the re-assert; narrowing one is `retract!` and re-assert |
| asserts a rule concluding `(rewriteOf …)`, `(sameAs …)`, `(equals …)` or `(disjointMetatype …)` | it merges or separates while the KB runs, where only a restart saw it |
| lists a store directory through `catalog/classify` | classification reads `records/format.edn`; three disk backends classify as `:store` that did not, and a `records/`+`index/` pair alone no longer does |
| catches around `unload!` | a store that did not close reports `:unreleased`, where it reported silent success |
| runs `kb-quality` | a fifth reading, `:declarations`, names argument constraints that constrain nothing, and `:stranded-count` drops |
| matches an arity refusal on its `:message` | an inherited length reads "takes N arguments through P", not "is declared with N" |

### Writes over a KB whose derived state was never built

- **Breaking: such a KB refuses writes rather than accepting them unchecked.** Every
  definitional check bottoms out in `jtms/in?`, so over an empty network all ten match
  nothing and the assert lands — and nothing later catches it. `assert`, `assert-inert`,
  `retract!`, `edit!` and `preview` refuse by name (`:unrecovered-kb`), reporting
  `:hazards` and naming the call that clears them.
  *Class:* Breaking; writes that landed silently now throw.
  *Migration:* call `recover` (or `reindex`) before writing, which is what the content
  needed anyway; or bind `vaelii.core/*write-unrecovered?*` around the write, which now
  logs once per KB naming what is unchecked.
  *Breaks:* `:unrecovered-kb`, `:unrecovered-premise`, `*write-unrecovered?*`, `:recover?`
  [docs/storage.md](docs/storage.md), [docs/web.md](docs/web.md)

- **Breaking: a derived record's teardown is refused where belief was never built.**
  `retract-storage!` read "no TMS node" as "inert" and deleted a forward-chained record,
  leaving dangling the justifications that concluded it. Nothing per-handle separates the
  two cases, so the question is asked of the KB instead.
  *Class:* Breaking; a retraction that deleted a record now throws.
  *Migration:* call `recover` (or `reindex`) before retracting, which is what the sweep
  needed anyway.
  *Breaks:* `:unrecovered-kb`
  [docs/storage.md](docs/storage.md)

- **`check` and `check-edit` answer for the door they mirror.** `check-writable!` runs
  first at `assert` and was not in the stage list, so a batch validated against an
  unrecovered KB came back admissible and then refused on its first line. Both report
  `:unrecovered-kb` alone and first, and both go quiet under `*write-unrecovered?*`.
  *Class:* Additive; a new problem `:type` on two readers that report problems.
  *Migration:* none. A caller matching on the message rather than the `:type` sees
  "index was" where the index hazard stands alone.
  *Breaks:* `:unrecovered-kb`, `check`, `check-edit`
  [docs/storage.md](docs/storage.md)

- **Refusal: a declared hazard survives being read while the store is still empty.**
  `write-hazards` retired `import-dump`'s `{:no-belief true}` on any read taken before the
  records landed, handing the finished load a KB whose records are unbuilt and whose
  hazard is gone.
  *Class:* Refusal; writes a prematurely-released hazard let through are now refused by
  name.
  *Migration:* code clearing a store through `p/clear-records!` rather than `clear!`
  should call `kb/note-hazards!` with both keys false, as the suite's fixtures now do.
  *Breaks:* `write-hazards`, `note-hazards!`
  [docs/storage.md](docs/storage.md)

- **Refusal: `recover` stops believing a record the store does not hold.** A stored
  justification concluding a handle with no record minted a phantom and made it IN, so the
  KB came back believing a handle no query could return, and everything drawn from it.
  Such a justification is left out of the network and counted, logged once at `:warn`
  under `::justifications-unrooted`.
  *Class:* Refusal; the handle read absent and its belief read true, so the state it
  produced was not one anybody asked for.
  *Migration:* nothing to change; a store carrying such a justification now says so.
  *Breaks:* `recover`, `justifications-unrooted`
  [docs/storage.md](docs/storage.md)

### Loading a dump

- **`:belief? :stored` — store what rests on what, and settle it later.** Everything
  `true` does **except the `recover`**, for a corpus that cannot afford one; for a foreign
  dialect it is the only mode that keeps the justifications at all. The catalog carries the
  choice (`:rebuild` / `:stored` / `:skip`) rather than a checkbox, and `active-caveat`
  gained `:recoverable?` so the browser's banner names which repair applies.
  *Class:* Refusal for the `:belief?` **value** check; Additive for the mode itself.
  *Migration:* none — `true` is still the default. An unrecognised `:belief?` value is now
  refused by name (`:unknown-option`), since anything truthy would otherwise mean `true`
  and run the recover the caller asked to defer.
  *Breaks:* `:belief?`, `:unknown-option`
  [docs/catalog.md](docs/catalog.md), [docs/web.md](docs/web.md)

- **One frame a dump holds and this build will not construct stops taking the load with
  it.** A frame the structural checks refuse yields no record, and both import paths threw
  on it — while a dump is not a program being written, and the reading side cannot fix the
  writing side. It is counted in the summary's **`:refused`**, skipped, and logged, which
  is the policy the naming door has had all along.
  *Class:* Additive for `:refused` and `:frames`.
  *Migration:* a load that threw `:naf-not-closed` — or any other construction refusal —
  now finishes; assert `(zero? (:skipped (:refused summary)))` to keep the old strictness.
  [docs/naming.md](docs/naming.md)

- **A justification the import writes no longer rests on a record the import deleted.** A
  remapped load drops the meta-sentexes whose `(sentexHandle H)` will not resolve, but the
  dump-id map went on resolving their ids, so both deduction readers stored justifications,
  premise marks and provenance pointing at records that were no longer there.
  `forget-deleted` closes it, reporting **`:orphaned-ids`** and
  **`:dropped-justifications-orphaned`**.
  *Class:* Additive for both keys; a load that wrote a dangling justification now drops it
  and says so.
  *Migration:* none. A store already carrying them is repairable in place — delete every
  justification naming a handle `sentex-ids` does not yield.
  [docs/catalog.md](docs/catalog.md)

- **Refusal: an import frame that fills a justification's `:out` slot**
  (`:naf-justification`, a new `:type`). The slot is the NAF antecedent set — reserved,
  and empty in every KB the engine builds — but a justification frame in a dump is the
  record's own field map, which made that door the one way a filled one could reach a
  store. Three relabel invariants read the slot as empty rather than reading it.
  *Migration:* nothing — no dump the engine produced carries one.
  *Breaks:* `:naf-justification`, `import!`, `import-dump`
  [docs/naf.md](docs/naf.md)

- **A dump that fills that slot is refused before the import writes anything.** The check
  ran after the whole sentex phase had landed, and an import is not a transaction, so the
  refusal left a half-written store that `assert-empty-destination!` then refused to retry
  into. It streams the file in a pre-pass now; same `:type`, same message, same ex-data.
  *Class:* neither label; the refusal is the same refusal, and what changed is what the KB
  holds afterwards. [docs/catalog.md](docs/catalog.md), [docs/naf.md](docs/naf.md)

- **A restart stops answering through an edge nothing supports.** `rebuild-taxonomy`
  replays **stored** declarations, so a `genl` edge that is OUT from the moment its node is
  made still answered `isa?` — a restart believing a type the running KB did not. `recover`
  runs `refresh-beliefs` over the replay, before the settle.
  *Class:* neither label; a restart's answers move onto the running KB's.
  [docs/storage.md](docs/storage.md), [docs/taxonomy.md](docs/taxonomy.md)

### The predicate hierarchy descends

- **Breaking: `arity`, `asymmetric` and `functional` descend it.** Each read its mark off
  the exact functor while the machinery it convicts *with* already fanned down the
  hierarchy, so each was bypassable through a sub-predicate door. A predicate declaring no
  arity of its own takes the one its supers agree on; `(asymmetric parentOf)` convicts
  `(fatherOf a b)` beside `(parentOf b a)` in either order; `(functional parentOf)`
  reconciles two `fatherOf` fillers. **`arity` is the strict one:** two declared arities
  across one edge is refused. Supers that disagree bind nothing, a `variableArity` super
  releases the inheritance, and the generative marks descend nowhere.
  *Migration:* a specialization that genuinely reads a different number of arguments is
  `variableArity` on either end of the edge; a sub-predicate declaring a conflicting arity
  is refused, so give the two one arity or drop the `genl` edge.
  *Breaks:* `variableArity`, `asymmetric`, `functional`, `:arity`,
  *Breaks:* `binaryPredicate`, `functional-clashes`
  [docs/taxonomy.md](docs/taxonomy.md), [docs/inherit.md](docs/inherit.md),
  [docs/equality.md](docs/equality.md)

- **Breaking: an argument constraint on a predicate binds its sub-predicates' tuples.**
  `(genl fatherOf parentOf)` says every `fatherOf` tuple *is* a `parentOf` tuple, so
  `(argIsa parentOf 1 person)` refuses `(fatherOf TheRock1 Mary)` exactly as it refuses the
  claim spelled `parentOf`; `argGenl` and `interArgIsa` descend by the same argument. The
  refusal was door-dependent and failed at the one job it exists for, the matcher fanning a
  goal's functor over its subtypes. Held to the writer's vantage: an edge a context cannot
  see imports no constraint.
  *Migration:* a KB using predicate-level `genl` for retrieval fan-out alone, relying on
  the specialized predicate being unconstrained, is refused where 0.7.0 accepted it; widen
  the declaration, move it down, or drop the edge.
  *Breaks:* `argIsa`, `argGenl`, `interArgIsa`, `:arg-type`
  [docs/taxonomy.md](docs/taxonomy.md)

- **`argIsa` read as an *inference* descends with it, and so does the entailment.** `ask`
  types an argument through a super-predicate's declaration, because a claim `assert`
  refuses for being ill-typed must not be one `ask` cannot type at all. Under
  `*assertive-arg-types?*` the minted type names the `genl` edges it descended, so
  retracting one takes the type back, and the entailment is drawn when the **edge** arrives
  last.
  *Class:* Additive; the entailment is opt-in and off by default.
  [docs/argtypes.md](docs/argtypes.md)

- **Three predicate-metadata kinds join `has-prop?` / `props`:** `:declares-arg-isa`,
  `:declares-arg-genl`, `:declares-inter-arg-isa`, marking a predicate that is the
  *subject* of an argument constraint. The descension asks per super whether it declares
  anything at all — off the index an argument-root probe per super on every assert, and a
  set membership once it is marked. *Class:* Additive.
  [docs/taxonomy.md](docs/taxonomy.md)

- **Breaking: a `functional` or `asymmetric` mark reaches back down a `genl` edge, on both
  retroactive paths.** Under `:arbitrate` a mark or edge arriving *after* the facts left
  the clashing pair believed — permanently, the pair never entering `:clashes` for a later
  settle to re-derive. Both paths take their extent through the marked predicate's spec
  subtree now.
  *Class:* Breaking; a clashing pair that stood believed is now arbitrated.
  *Migration:* a caller reading `contradictions` or `violations` sees pairs the door has
  always refused when the mark arrived first — the two arrival orders agree now.
  *Breaks:* `contradictions`, `violations`, `:constraint-exposure`
  [docs/taxonomy.md](docs/taxonomy.md)

- **Breaking: the cross-context exposure pass reads its marks down the hierarchy, as every
  check it gates already did.** It read the mark off the **exact functor** per sentex, so a
  pair whose only mark sits on a super-predicate was dropped before any check saw it.
  *Class:* Breaking; a KB holding such a pair files a `:constraint-exposure` entry where it
  filed nothing.
  *Migration:* nothing to write — the entry names both handles, so the pair is what to look
  at.
  *Breaks:* `violations`, `:constraint-exposure`
  [docs/contexts.md](docs/contexts.md), [docs/taxonomy.md](docs/taxonomy.md)

- **Breaking: the retroactive arity report descends the hierarchy, as the door it mirrors
  already does.** Fact, declaration and `genl` edge are three ingredients and any can
  arrive last; the report read only the predicate its trigger named, so a ternary
  `fatherOf` fact under a binary `parentOf` stood believed and unmentioned. It sweeps the
  **spec subtree** now, and entries carry `:via`.
  *Class:* Breaking; nothing new is refused, and a caller reading `violations` sees a
  finding it did not.
  *Migration:* nothing to write — read `:via` to tell an inherited length from a declared
  one.
  *Breaks:* `violations`, `:arity`, `:via`
  [docs/taxonomy.md](docs/taxonomy.md)

- **Breaking: that report answers a `genlCx` edge, its fourth ingredient.** A visibility
  edge rebinds a predicate's length as a `genl` edge does, and `settle/arity-bound-by` knew
  three spellings and not that one. The pass triggers on the edge and sweeps whichever end
  `p/count-in-context` sizes smaller.
  *Class:* Breaking; `:arity` entries appear in two arrival orders that filed none.
  *Migration:* none for a KB whose contexts declare their own arities; one declaring in a
  super-context learns about facts that were already wrong.
  *Breaks:* `violations`, `:arity`
  [docs/taxonomy.md](docs/taxonomy.md), [docs/contexts.md](docs/contexts.md)

- **Breaking: the arity door words an inherited length as inherited, as its retroactive
  half already did.** `fatherOf is declared with 2 arguments, declared of parentOf but has
  3` credited `fatherOf` with a declaration it never carried; it reads `fatherOf takes 2
  arguments through parentOf but has 3` now, with a self-declared length unchanged.
  *Class:* **Breaking** on §3.8's counterweight: only the `:message` string moves, which is
  the class-1 test.
  *Migration:* read `:expected`, `:actual` and `:via` off the ex-data rather than matching
  the message.
  *Breaks:* `is declared with`, `:opposing-handle`, `:arity`
  [docs/taxonomy.md](docs/taxonomy.md)

- **Breaking: a `variableArity` predicate may be given argument types past its declared
  length.** `arg-position-problem` was the one arm of the arity family that did not read
  `checks/variable-arity?`, so `(argIsa qRel 3 person)` was refused on a predicate whose
  3-argument facts the same KB admitted.
  *Class:* Breaking; input that was refused is now admitted, and `kb-quality`'s
  `:stranded-count` drops.
  *Migration:* nothing in the shipped ontology moves — none of its three `variableArity`
  predicates declares past its length.
  *Breaks:* `variableArity`, `argIsa`, `:stranded-count`, `kb-quality`
  [docs/taxonomy.md](docs/taxonomy.md), [docs/quality.md](docs/quality.md)

- **`kb-quality` gains a fifth reading: argument constraints that constrain nothing.**
  `(argIsa parentOf 3 person)` is admitted while `parentOf` has no declared length; when
  one arrives, declared or inherited, the declaration is left naming a position the
  predicate provably does not have. `:declarations` names them and `quality-report` writes
  the section. **Deliberately not `violations`:** a stranded declaration is inert and reads
  the same an hour later.
  *Class:* Breaking for the `:arg-position` refusal message, which now splits on `:via` as
  the door and the report do; Additive for the reading itself.
  *Migration:* read `:via` and `:arity` off the ex-data rather than parsing `:message`.
  *Breaks:* `kb-quality`, `quality-report`, `:arg-position`, `is declared with`
  [docs/quality.md](docs/quality.md), [docs/taxonomy.md](docs/taxonomy.md)

- **Breaking: neither retroactive pass can file its way through the ledger, and
  `:arity-report-truncated` says when a cap stopped one.** The ledger keeps the newest
  1,000 entries and the arity report filed one per convicted predicate against a budget of
  4,096, so one binding over a wide subtree could evict every other violation in the KB.
  Both passes file at most the content-first **8** and say what the cap left out. Read the
  new kinds as *found, examined, and not named*.
  *Class:* Breaking for the cap, Additive for the kind and the keys.
  *Migration:* size a problem from `:predicates` and `:facts` on the notice rather than by
  counting `:arity` entries; past 8 the count is now visibly not the total.
  *Breaks:* `violations`, `:arity-report-truncated`, `:arity-truncated`,
  *Breaks:* `:constraint-exposure-truncated`
  [docs/taxonomy.md](docs/taxonomy.md), [docs/nmtms.md](docs/nmtms.md)

- **The retroactive arity sweep says when its budget stopped it, including in the case that
  carries no finding.** The `:truncated` flag rode on a finding, so a predicate that spent
  the budget convicting nothing left every predicate after it examined zero facts deep in
  silence. One **`:arity-truncated`** entry is filed either way.
  *Class:* Additive; a new `:violation` kind, so a defaultless `case` over them has one
  more to admit. [docs/taxonomy.md](docs/taxonomy.md)

- **Breaking: a descended merge names each `genl` edge once, not once per side.** Both
  sides of a functional clash reach their mark by their own path, and those paths are a
  **set**: two `fatherOf` fillers under `(functional parentOf)` descend one edge, which
  landed twice in the stored record and two or three times in the reports that read it.
  Belief never moved, but an antecedent list is the explanation a caller is handed.
  *Class:* **Breaking** on §3.8's counterweight: the list is shorter, deterministically so.
  *Migration:* nothing, unless you counted.
  *Breaks:* `why-not`, `preview`, `:because`, `:antecedents`
  [docs/nmtms.md](docs/nmtms.md)

### Contexts and placement

- **Breaking: a firing rests on the `genlCx` edges its placement was read over, and now
  names them.** A conclusion is placed in the maximal contexts that see the rule, the facts
  and the `genl` edges the match subsumed through, and each sighting is a reachability some
  ordinary sentex supports and somebody can take back. The justification named the
  ingredients and not the edges, so retracting one left the conclusion believed in a context
  that could no longer see any of its reasons — belief as a function of arrival order. The
  edges join the antecedent list, one shortest path per ingredient context.
  *Migration:* assert the `genlCx` wiring `{:strength :monotonic}` wherever a cross-context
  conclusion must stay indefeasible, and expect context edges among a justification's
  antecedents. Two things move for a caller who retracts nothing: antecedent lists are
  longer, and `defeat-class` caps on the edges like any other ground.
  *Breaks:* `genlCx`, `supporting-justifications`, `defeat-class`, `:monotonic`
  [docs/contexts.md](docs/contexts.md), [docs/nmtms.md](docs/nmtms.md)

- **Breaking: a retraction stops filing `:no-placement` entries about the rules it just
  took apart.** A conclusion that now has nowhere to be placed *is* the retraction the
  caller asked for, not a diagnosis of anything, and one per affected rule crowded the
  ledger a caller reads for what it did *not* mean to do. An ordinary firing that cannot
  place its conclusion still says so.
  *Class:* Breaking; a public reader returns fewer entries.
  *Migration:* none for a caller reading `violations` for problems. A caller counting
  entries across a retraction sees the count it would have had if the rules had never been
  asserted.
  *Breaks:* `violations`, `:no-placement`
  [docs/contexts.md](docs/contexts.md)

### Rules that conclude structure

- **A rule generator may stamp a generator, at any depth, and a variable an enclosing level
  fills may head a literal.** `(implies (typeVersion ?ipred ?tpred) (implies (?tpred ?type
  ?cap) …))` states a type-level/instance-level bridge once instead of once per predicate
  pair, and what reaches the index is still an ordinary rule over concrete functors. The
  scoping rule needed nothing added, and **a top-level rule antecedent is untouched**.
  *Class:* **Additive** — a shape that was refused is now accepted.
  [docs/generators.md](docs/generators.md)

- **Breaking: a rule concluding `(rewriteOf A B)` / `(sameAs A B)` / `(equals A B)`
  merges.** The conclusion reaches the arm an asserted equality reaches, so the closure
  learns the edge and every sentex naming the retired spelling gains a justified twin.
  Before, a running KB and its own restart disagreed about whether two terms were one thing.
  *Migration:* a KB with such a rule now merges where it did not, which moves matches,
  `different` answers and belief; if the rule meant something weaker than identity, restate
  it under a predicate of your own.
  *Breaks:* `rewriteOf`, `sameAs`, `equals`
  [docs/equality.md](docs/equality.md)

- **Breaking: a rule concluding `(disjointMetatype M)` separates M's members while the KB
  runs.** The mark reached the taxonomy only when a restart replayed it, so one store
  answered `disjoint?` two ways either side of one.
  *Migration:* a fact contradicting such a separation is refused `:disjoint` at assert time
  now, where it was stored unchallenged.
  *Breaks:* `disjointMetatype`, `:disjoint`, `disjoint?`
  [docs/taxonomy.md](docs/taxonomy.md)

### Belief, and reports that read as content

- **Breaking: a re-asserted fact keeps the stronger defeat class.** The premise mark was
  last-writer-wins, so a bare re-assert of known-true content retired it and the
  `:monotonic` negation then *defeated* the original — where the same three sentences
  without the re-assert in the middle leave an irreducible clash. The class resolves from
  content at the fact door as it already did at the rule door.
  *Migration:* narrowing a class is `retract!` and re-assert, as it is for a rule's
  `:direction`, `:defeasible` and `:strength`.
  *Breaks:* `:strength`, `defeat-class`
  [docs/nmtms.md](docs/nmtms.md), [docs/canonicalization.md](docs/canonicalization.md)

- **A justification reports as content, in both directions.** 0.6.0 closed every report and
  election that keyed on retrieval order; these are the two justification surfaces it left.
  `dependent-justifications` handed back an allocation-ordered id set unsorted, so two
  assertion orders of one KB listed the same dependents in opposite orders on a public API;
  and a firing's stored antecedent vector is ordered where it is **built**, since a firing
  is seeded by whichever antecedent triggered it. One carried from an earlier release keeps
  the order it was written with until it is re-derived.
  *Class:* neither label; the order it displaced was a function of how the KB was loaded, so
  nothing stable was there to depend on.
  [docs/nmtms.md](docs/nmtms.md), [docs/api.md](docs/api.md)

- **The wholesale wipe stops carrying the qualitative join baselines.** `clear!` left
  `:qcn-joined` standing beside the network cache it reset, describing a KB the call had
  just deleted. Hygiene rather than correctness — a stale baseline self-invalidates through
  its handle-subset check — but the wipe is the one thing that reaches a baseline.
  *Class:* none; resident engine state with no caller-visible surface.
  [docs/qcn.md](docs/qcn.md)

- **`why` builds its proof tree over an explicit work stack, not the JVM stack.** The walk
  was real recursion capped at a depth of 256 — but the cap is a ceiling on the *tree*, not
  a fix: a chain down a long transitive closure repeats no handle, so the cycle guard never
  fires, and a `{:max-depth n}` past the JVM's frame budget overflowed on a KB merely large.
  The walk is iterative now, so the cap bounds the size of the tree returned and nothing
  overflows however deep the derivation runs. A regression test pins it on a deliberately
  small stack, since the depth a recursion tolerates is the platform's and not the engine's.
  *Class:* neither label; the tree returned is identical, and the one input whose behaviour
  moves — a derivation deeper than the JVM's frame budget — returns its tree where recursion
  threw `StackOverflowError`.
  [docs/api.md](docs/api.md)

### Doors, catalogs and reports

- **Breaking: a top-level vector sentence is refused at both families of door** (`:shape`).
  A vector is `sequential?`, so `assert` flattened it to the list it looks like — while a
  vector goal is what every read door spells a **conjunction** with. One spelling, two
  doors, opposite answers, neither raising: `(assert kb '[likes Tom Ann])` stored the list
  and `ask` found it on the vector, while `prove` and `query` joined three symbols and
  answered nothing; and `ask` flattened the documented goal `[(dog ?y) (parentOf Tom ?y)]`
  into a sentence nothing matches and answered **false**. Nested vectors are untouched, as
  is `lookup`, whose level 0 reads a vector as an index path.
  *Class:* Breaking; a caller who wrote the vector spelling on both sides had code that did
  what its author believed, and it stops on upgrade.
  *Migration:* write one sentence as a list — `(likes Tom Ann)` — and ask a conjunction with
  `query` or `prove`, which are the doors that join.
  *Breaks:* `:shape`, `sentexes-matching`, `handle-of`, `ask-within`, `prove-within`,
  *Breaks:* `query-plan`, `provable?`, `query?`, `abduce`, `assert-inert`, `check-edit`
  [docs/api.md](docs/api.md), [docs/troubleshooting.md](docs/troubleshooting.md)

- **Refusal: a `nil` conjunct is a conjunct, not the absence of one.** The guard read the
  *value* of the first non-sentence member, so `[(dog ?x) nil]` passed it and the join then
  answered nothing — a real conjunct silently zeroed, which is the number nobody can check.
  It tests whether one exists now.
  *Migration:* nothing — the goal never did what whoever wrote it believed.
  *Breaks:* `:shape`, `:conjunct`
  [docs/api.md](docs/api.md)

- **Ten option doors word their refusal the same way, and `open-kb` gains the shape check.**
  The key check was written out at each door, so the wording drifted and one door was
  missing half of it: `(open-kb :nope)` came back as a bare `IllegalArgumentException` about
  creating an ISeq, where every other public entry point answers `:unknown-option`. With the
  doors sharing one refusal (`vaelii.impl.opts`) four messages change wording and `poll`'s
  ex-data gains the `:unknown` key the others carried; `:type` and every other ex-data key
  are unchanged at all ten. Separately, `query`'s non-map refusal reports the value it
  rejected under `:got` rather than under `:options`, which everywhere else is the roster.
  *Class:* Refusal for `open-kb`'s non-map, which previously threw an unnamed error.
  *Migration:* none for a caller discriminating on `:type`. A caller matching refusal text
  should match `:type :unknown-option` and read `:options` / `:unknown` instead.
  *Breaks:* `:unknown-option`, `open-kb`
  [docs/namespaces.md](docs/namespaces.md)

- **Breaking: a store on disk is recognised by the format marker it writes, not by a
  directory pair.** `catalog/classify` read a `records/` beside an `index/`, which three
  disk backends never write — so a store the browser could open listed as nothing at all,
  while a pair left by something else listed as a store and failed on open. It reads
  `records/format.edn` now.
  *Class:* Breaking; a directory's classification changes in both directions.
  *Migration:* none for a store this build wrote. A catalog entry pinned by a caller's own
  path should be re-listed.
  *Breaks:* `classify`, `:store`
  [docs/catalog.md](docs/catalog.md)

- **Refusal: `unload!` reports the release it actually performed, and gives way to the walk
  it would have emptied.** A `close-dir!` that threw was logged and the entry dropped, so an
  unload reported clean over a store whose index had not fsynced; the entry keeps its place
  with status **`:unreleased`** now, stops being the active KB, and a later unload retries.
  An entry whose KB a running export is still walking is refused **`:still-exporting`** —
  the walk has no snapshot.
  *Migration:* nothing for an unload nothing else is holding, which is every unload that
  succeeds; a caller catching around `unload!` sees `:unreleased` where a store that did not
  close reported silent success.
  *Breaks:* `unload!`, `:unreleased`, `:still-exporting`, `reset-registry!`
  [docs/catalog.md](docs/catalog.md)

- **Every kind `violations` can file has a row in the table consumers branch on.** It named
  six of the thirty, and all six rows carried `:detail` keys the entries no longer build.
  `violation_roster_test` scans the sources both ways.
  *Class:* neither label; no kind is new or moved. [docs/api.md](docs/api.md)

- **Refusal: a two-axis calculus checks its projection is a bijection.** The cardinal
  directions and the relative frame are one algebra — nine relations that are two
  independent coordinates on two axes — built now by `vaelii.impl.projection` from a single
  table each. A table that is not a bijection onto the nine axis pairs is refused where it is
  built (`:bad-algebra`) rather than composed: a missing pair composes to `nil` and stores it
  as a relation, and a repeated one still covers all nine while the inverse silently drops
  one.
  *Migration:* nothing — both shipped tables are bijections; a caller building their own
  calculus gains the refusal.
  *Breaks:* `:bad-algebra`
  [docs/qcn.md](docs/qcn.md)

### The shipped ontology

- **`asymmetric` stops claiming it hands you irreflexivity.** `CxCore`'s definition said the
  mark "makes ?predicate irreflexive too". It does not: conviction needs a *believed
  opposing claim*, and a self tuple `(?predicate a a)` is its own mirror, so there is no
  second claim to convict against and the door admits it. `CxSize`'s note on `largerThan`,
  which leaned on the same wrong step, is reworded to rest on preservation running downward.
  *Class:* neither label; ontology content, which §3.8 exempts from the Breaking label
  however far it moves an answer — and here it moves none, the engine having always behaved
  this way. What changed is a description that told a reader to expect a refusal nothing
  performs. [docs/taxonomy.md](docs/taxonomy.md)

### Performance

Three passes over the predicate hierarchy were quadratic in a *batch* of `genl` edges,
which is what a load writes. All three are measured and explained in
[docs/taxonomy.md](docs/taxonomy.md), "What a batch of edges costs the passes that read it";
the answers computed are identical, and all three are free where nothing is declared.

- **A settle reads its `functional` and `asymmetric` marks once, from the marked end.** Four
  gates asked the one question through `tax/props-over`, whose memo keys on the node a walk
  began at, so nested roots shared nothing. `settle/clash-marked-below` walks the marks
  **down** instead, once per pass. 1,000 askers over a 1,000-predicate chain go from 213 ms
  to 1.1. *Class:* neither label. [docs/taxonomy.md](docs/taxonomy.md)

- **A batch of `genl` edges costs the union of its subtrees, not the sum of them.**
  `settle/report-arity-reach!` expanded each edge's spec subtree separately, and none of it
  was bounded — the instance budget counts facts examined and this examined none.
  `tax/specs-of-all` seeds one traversal with every root: 512 edges go from 60.6 ms to 1.0.
  *Class:* neither label. [docs/taxonomy.md](docs/taxonomy.md)

- **The two retroactive `genl`-edge arms decide there is nothing to draw before reading the
  subtree, not once per fact inside it.** `special/equate-under-edge` had no gate at all, so
  every `genl` write on every KB materialized the subtree's extent to discover nothing was
  functional. **No curve moves** — `subsumption-seeds` walks the same subtree and must.
  *Class:* neither label. [docs/taxonomy.md](docs/taxonomy.md)

- **A check for a shape the sentence does not hold stops building a seq to find out.** Seven
  readings descended every sentence with `tree-seq` hunting a form almost none contain;
  `sentex/some-form` and `forms-where` are the two walks they share now. 13x on a plain
  one-antecedent rule assert and 25x on a six.
  *Class:* neither label; same answers, same depth-first pre-order.
  [docs/canonicalization.md](docs/canonicalization.md)

- **A refused sentence stops paying to resolve a stack trace nobody prints.** A checked
  import counts what the front door refuses, so the throw is a reporting path taken a hundred
  thousand times in a load — and three quarters of it was `ex-info` materializing the trace
  to elide its own two frames. `check!` builds the `ExceptionInfo` directly.
  *Class:* neither label; same class, same message, same `:type :naming` ex-data.
  [docs/naming.md](docs/naming.md)

- **A justification listing builds its content key once per entry, not once per comparison.**
  `sort-by` calls its key fn from inside the comparator, and a rule handle is an antecedent
  of every firing it licenses, so `dependent-justifications` paid the multiple on the whole
  history. Decorate, sort, undecorate.
  *Class:* neither label; the same `compare` over the same keys, both sorts stable.
  [docs/nmtms.md](docs/nmtms.md)

### Tooling

- **The whole matrix at once.** `lein test-matrix` runs the eight storage backends and the
  five sweeps concurrently, one JVM per configuration: ~13 minutes against the ~55 the two
  single-axis scripts take in sequence, which is the difference between a check that gets run
  before landing and one that gets skipped. Each configuration records the revision it
  compiled and the report says whether they agree; a red run names the failing **tests**,
  rolled up across configurations. *Class:* neither label.
  [docs/operations.md](docs/operations.md)

- **Every verdict names the tree it is a verdict about.** `lein gate`, `test-backends`,
  `test-sweeps` and the sharded test stage print the revision and the `src/`/`test/` dirty
  state on their banner, every summary row and every log they write: a count read an hour
  later is only comparable against the tree it was taken on. Progress splits by reader —
  mark rows for a terminal, one line per namespace for a pipe or CI, forced either way with
  `SUITE_PROGRESS`. *Class:* neither label. [docs/operations.md](docs/operations.md)

## 0.7.0 — 2026-08-12 — "contexts get one spelling"

- **Breaking: a context name is `Cx`-prefixed, not `Context`-suffixed.** `CoreContext`
  is `CxCore`, `UniverseContext` is `CxUniverse`, and the `assert` front door refuses a
  `Context`-suffixed name by the same naming check that already refused a malformed
  predicate or type. *Migration:* respell every context name — in a stored KB, an
  `assert` call, and a saved dump — to the `Cx` form. `docs/naming.md`.

- **Breaking: the context-transitivity predicate is `genlCx`.** `(genlContext sub super)`
  is `(genlCx sub super)`, so the relation between two contexts is spelled the way the
  contexts it relates are. The `genl` closure over types keeps its name. *Migration:*
  respell the predicate wherever an edge is asserted, matched or retracted; a stored
  `genlContext` edge is a fact under a predicate nothing reads, so re-assert it rather
  than expecting the taxonomy to find it. `docs/taxonomy.md`.

## 0.6.0 — 2026-08-12 — "stored rules become first-class"

A rule can conclude a rule, a NAF guard written as a
conjunction guards instead of firing unconditionally, and every door that reaches a rule
reads **belief** rather than storage. Beside them, the arrival-order dependences left in
the belief loop are closed — a revived datum, an un-merged spelling, and every report,
digest and election that keyed on retrieval order — and two reads that grew with what the
KB *holds* rather than with what the write *touched* now read forward off the region.

**Three entries are Breaking**, which is what makes this a minor rather than a point
release: the daemon answers an export refusal 400 where it answered 500, the model's tool
surface drops two ops, and the CLI's refusals move to stderr. Seven Refusal entries batch
here rather than each forcing its own release, which is what §3.8 of `CONTRIBUTING.md`
designates a minor for. Every Breaking and every Refusal entry carries its *Migration*
line.

**Triage, for a 0.5.1 caller.** This is the index to what touches something you have
written.

| If your code… | Then |
|---|---|
| treats a 5xx from the daemon's `:export` op as a backend fault | the five destination refusals answer **400** now; retry logic keyed on 5xx stops retrying a caller mistake |
| drives `:preview` or `:clear-caches` through the LLM tool surface | they are no longer exposed to a model — call the op on the daemon or the API directly |
| writes `(ist Ctx S)` in an antecedent or an `exceptWhen` | refused `:not-well-formed`; say it with `decontextualizedPredicate` or a `genlCx` edge |
| passes `(ist Ctx S)` to a read | it answers now instead of returning empty, with the named context winning over the argument |
| writes `(unknown (and A B))` as a guard | it guards now; it fired unconditionally before. Under a quantifier the same shape is refused |
| branches on `violations`' `:violation` with a defaultless `case` | `:functional`, `:asymmetric` and `:constraint-exposure-truncated` are new kinds |
| runs `check` over `(not (implies …))` | refused `:not-well-formed` at both doors, where `check` passed it and `assert` threw |
| runs a `:refuse` KB and reads an empty `violations` as a clean bill | cross-context `functional` and `asymmetric` pairs are reported there now |
| passes `--strength` to the CLI's `assert-rule`, or reads CLI refusals off stdout | the flag is honoured now, and refusals print on stderr |
| forks a KB with an opts map naming neither `:space` nor `:dir` | the fork lands on its own space instead of the shared process default |
| asks a `symmetric` predicate about a claim that is inherited rather than stored | the mirror composes with the other provers now, so an `ask` can answer more |
| writes a kind-level `(hasCapability <kind> …)` against the shipped ontology | kind-level claims are `capabilityType`; `hasCapability` is the instance-level reading alone |

- **A capability claim about a *kind* is `capabilityType`, and about a *member* is
  `hasCapability`.** One symbol read at two levels gets one argument check, so seven facts
  the starter shipped were convicted by a declaration the starter also shipped — silently,
  the declaration and the facts sitting in different contexts. The kind-level content moves
  to `capabilityType`, a `typeRelationPredicate` carrying the `argPreserving` pair;
  `hasCapability` keeps `argIsa … 1 animal`. `argPreservingInverse` answers the six
  conclusions that vanish with the kind-level rule. Two new sweeps put every shipped
  sentence to `check` against the fully loaded KB and every stored fact to the declarations
  the same KB ships — either alone misses what the other finds. The `typeToInstancePred`
  pairing stays prose: `hasCapability` cannot carry the mark without changing its argument
  family. *Class:* none; `resources/kb/` is data rather than surface (§3.8).
  [docs/inherit.md](docs/inherit.md), [docs/taxonomy.md](docs/taxonomy.md)

- **A guard keyed on the operator instead of on what it reads.** An `exceptWhen` whose
  query is itself a query operator — `unknown`, a `thereExists`, an aggregate — was indexed
  under a functor no sentex carries, so no arriving fact could queue it: the exception was
  evaluated once and re-evaluated never, blocking forever including after the guard should
  have released, and the stratification graph read the same keys, so a cycle through one
  was refused nowhere. `rules/watched-predicates` peels the frames for all four sites that
  key on them. The settle-time narrowing peels them too, or the corrected key would have
  bought a quadratic — 48 → 192 level-6 evaluations for the same six triggers, against 0
  once peeled. And `check` predicts the NAF-literal refusals rather than only `assert`
  throwing them: they lived in the constructor, so the dry-run door could not see them.
  *Class:* neither label for the guard — belief moves for a rule of this shape, and the
  guard answered from arrival order rather than content; **Additive** for `check`.
  [docs/exceptions.md](docs/exceptions.md), [docs/naf.md](docs/naf.md)


- **A rule can conclude a rule.** `(implies <antes> (implies <antes'> <conseq'>))` is a
  **generator**: its firing stores the rule it concludes, holes filled. The hole split is
  computed rather than declared — a variable the generator's own antecedents mention is
  bound by the join and ground in the mint, every other survives as a variable — so there
  is no template vocabulary to disagree with the template it annotates, and a **hole may
  stand in functor position**, which is the point: one generator ranges over a family of
  predicates while every rule the index keys on has a concrete functor. A mint is derived
  content, justified by the firing rather than marked a premise, so retracting what
  licensed it un-believes it through the ordinary relabel. Rules follow belief now at all
  four chainer sites, which is what makes that work. Five refusals bound it: a generator
  generating a generator, an `exceptWhen` on the stamped rule, a `set/backwardRule`
  generator, one sharing no variable with what it stamps, and a generator **cycle** —
  refused outright rather than depth-capped ([docs/defenses.md](docs/defenses.md)).
  *Class:* **Additive**; shapes that were refused are accepted, and nothing could
  previously make a stored rule un-believed. [docs/generators.md](docs/generators.md)


- **A NAF guard written as a conjunction now guards.** `(unknown (and A B))` was accepted
  and inert in three places at once: no prover claims the functor `and`, so the goal came
  back unanswered and read as *not derivable* — the `unknown` holding, the rule firing
  unconditionally — while the re-check index posted it under a predicate no fact carries
  and the stratification check drew its negative edge from the same functor. An author who
  wrote a two-condition guard got a rule with no guard at all. `sentex/naf-query-conjuncts`
  is the one accessor all four readers share, so the conjuncts are evaluated by the
  exception's own block-if-all evaluator, each conjunct's predicate is watched, and each is
  a negative edge; conjuncts are sorted and flattened, as an exception's are. A conjunction
  **under a quantifier** is refused (`:quantified-conjunction`), and an empty one with it —
  [docs/defenses.md](docs/defenses.md) says why the flat reading is not available.
  *Class:* neither label for the guard, no author's code having done what its author
  believed; **Refusal** for the two shapes. *Migration:* bind the witness with a generator
  antecedent and leave one literal under the `unknown`.
  [docs/naf.md](docs/naf.md), [docs/aggregate.md](docs/aggregate.md)

- **The strictest policy stops being the leakiest.** Under `:refuse` a cross-context
  `functional` or `asymmetric` clash was neither refused nor reported: the definitional
  checks are scoped to the writer's own cone, the vantages are deliberately withheld under
  that policy, and the exposure ledger had an entry kind for disjointness only.
  `settle/expose-constraint-clashes!` files `:functional` and `:asymmetric` entries shaped
  like the `:disjoint` one, re-deriving each clash from the vantages the refusal itself
  would ask from — so the report cannot drift from what the door would refuse, and closing
  the gap widened no vantage. It costs a KB declaring neither property two `seq`s, gated on
  the declared vocabulary; a `genlCx` edge is the one trigger reaching past the region,
  because visibility itself moves there. Entries are capped and never silently
  (`:constraint-exposure-truncated`), and keyed on the handle pair so both arrival orders
  file one entry. *Class:* **Additive** — a new entry kind in an accumulating ledger. A
  `:refuse` KB that saw an empty `violations` may now see entries, which is the point.
  [docs/nmtms.md](docs/nmtms.md)

- **A hidden set kept where the sentexes are, not rebuilt per placement.**
  `res/excepted-handles` fetched a record, re-derived a target and asked `jtms/in?` for
  every stored `except` in the KB, per placement and per candidate justification.
  `kb/note-excepted!` maintains `{context -> {hidden-handle -> #{except-handle}}}` at the
  store instead, rebuilt by `recover` because no store holds it; the roster holds what is
  **stored** and readers filter by belief, since an `except` can be defeated with no sentex
  arriving. On 400 facts and 380 derivations the read goes from 88.8% of the run to 3.1% at
  1,000 excepts, and 0 excepts is unmoved. `res/hidden-fn` hands back a predicate — nil when
  the vantage hides nothing — so callers with handles in hand stop materializing a set.
  The guard is an oracle: `meta_sentex_test` compares the roster against a full scan of
  storage after every kind of arrival, defeat, revival and removal, across a `recover`.
  *Class:* neither label; same arity, same contract, same answer set.
  [docs/contexts.md](docs/contexts.md)

- **The planner's subtype fan is made cheap rather than remembered.** `est-matches` cost a
  unary type literal over the type's whole subtype closure, once per pick per plan per
  firing attempt — **13.2%** of a chaining run on a 364-type hierarchy. For the shape that
  costs, `fan-of-roots` reads the trie counts directly and the fan halves to 6.8%; a deeper
  prefix still takes the general walk. Remembering the answer instead does not work and the
  harness says so on both paths: a memo stamped on the change clock measures 0.98–0.99x
  under chaining, the run's own placements retiring the entry between one plan and the next,
  and a finer stamp is unsound rather than fiddly. `lein perf` gains `visibility-reading`,
  the check that would have caught the walk above — flatness being a growth claim a ratio
  can see. *Class:* neither label; the number returned is identical by construction.
  [docs/inference.md](docs/inference.md)

- **`ist` places, and four layers had it half-reading.** An `(ist Ctx S)` in antecedent or
  `exceptWhen` position is refused `:not-well-formed`: the literal is matched under a
  functor no sentex carries, so it satisfies nothing — while the naming check, range
  restriction, canonicalization and well-formedness all read the frame as meaningful, so
  `check` reported no problems and `assert` returned a handle. A positive antecedent yields
  a rule that cannot fire; an `exceptWhen` never matches, so the conclusion it was written
  to block stands believed; an `(unknown (ist …))` fires unconditionally. The refusal names
  both repairs. On the read side the same form now **answers** — every door taking a
  sentence and a context asks S in Ctx, the named context winning over the argument, which
  is the resolution `assert` already makes. It grants no visibility a context argument did
  not already grant. A wrong-arity `ist` or one standing as a conjunct of a vector goal is
  refused rather than answered empty. *Class:* **Refusal** for the antecedent and the two
  read shapes, **Additive** for the reading. *Migration:* say a rule's premise with
  `(decontextualizedPredicate P)` or a `genlCx` edge into the rule's own cone.
  [docs/contexts.md](docs/contexts.md), [docs/api.md](docs/api.md)

- **A datum that comes back believed goes back on the agenda.** Two routes let belief
  arrive with nothing chaining behind it, so the same knowledge in one order concluded and
  in the other did not. A revived antecedent licenses the firing its defeat withheld — the
  firing that never happened left no justification to release and reached no placement to
  re-ask — so the trigger is read from `jtms/revived`, with `jtms/touched-new` naming the
  nodes the window created so a re-seed is not a second forward chain per settle. The
  equality door is the same defect where `revived` cannot see it: supersession moves belief
  with no relabel behind it, so `refresh-supersessions` feeds `*unmerged-sink*` and settle
  re-seeds, bounded by `max-unmerge-rounds`. *Class:* neither label; belief moves only
  toward conclusions the same knowledge already reached in another order. Guards: both
  un-merge routes and twenty orderings, six of which disagreed.
  [docs/nmtms.md](docs/nmtms.md), [docs/equality.md](docs/equality.md)

- **An answer picked from a fan is keyed on content, never on arrival.** Fourteen reads
  elected a survivor, a representative or a display line by retrieval order, which under the
  columnar index is assertion order. Two of the keys were also being elided by an ambient
  `*print-length*` — including a digest stored durably in `termOfUnit` content — so the
  print vars are bound off wherever EDN is written for something other than a human to read.
  The elections themselves span `dedup-constant`, clash reports, `one-supporter`, glosses,
  `rewrite-target`, `why-not`'s `:contradicted-by`, the quality rule line,
  `strongest-per-tuple`, ASPIF emission and `label-context`'s minted copies. And the handle
  cache stopped answering from another KB: `canon-stamp` carries the record store, two KBs
  declaring nothing symmetric having stamped one shared empty set. *Class:* neither label;
  the order displaced was not reproducible for the same knowledge.

- **A collected NAT leaves none of its bookkeeping behind.** `nat/bookkeeping-handles`
  answered lazily while its caller retracts what it hands back, so a tail forced after the
  `termOfUnit` map's own retraction found no expression and the result types stayed stored —
  in the retrieval orders that hand back the map first, and not in the others. The set and
  the orphan list are realized before the first retraction. *Class:* neither label.

- **A stored sentex is not a believed one, and five reads had it the wrong way round.** ASP
  grounding takes only believed assumption and constraint rules, a records-only import
  stores each record with its dump strength and premise mark so a later `recover` has
  premises to believe, the catalog's belief caveat probes for a believed datum rather than
  any node, and the generator reports `:stored` as storage. The converse correction is the
  reified-NAT sweep: uses count by **storage**, since a stored-but-OUT use revives and
  collecting the map from under one dangles the constant. *Class:* neither label; each read
  answers the question its docstring already claimed. [docs/nat.md](docs/nat.md)

- **Retrieval answers what the reference answers.** Four matching reads disagreed with the
  fan-out they are checked against, three of them silently: the mirror probe asks the
  candidate's own functor rather than mirroring whenever *some* predicate under the queried
  one is symmetric; `naf-query` unwraps an aggregate as it unwraps `thereExists`, so the
  count moving no longer leaves the old conclusion believed; the rete alpha matcher skips
  `exceptWhen` meta-sentexes; `aggregate-values` normalizes compound values, so two
  spellings of one merged measure count once; and the three pre-canon reads that gated on
  the list spelling take the vector spelling as the same sentence. *Class:* neither label;
  the answer withdrawn was one the two paths disagreed about.
  [docs/inference.md](docs/inference.md), [docs/canonicalization.md](docs/canonicalization.md)

- **A symmetric or inverse reading composes with what is derived.** The mirror answered off
  storage alone, so an *inherited* claim had no mirror; `(pred b a)` goes back through the
  registry minus `SymmetricProver` now, bounded at two levels by `*mirror-depth*`. A partner
  declared on a sub-predicate is the same edge (`tax/inverses-under`), the mirror licenses
  the forward door and the firing names the symmetry it read through, and a defeat inside
  arbitration re-joins what its sentence licensed over closures refreshed to what is
  believed now. *Class:* neither label — answers are added, none withdrawn.
  [docs/inherit.md](docs/inherit.md), [docs/taxonomy.md](docs/taxonomy.md)

- **A negated rule is refused at the door.** `(not (implies …))` built a `RuleSentex` whose
  key cannot be computed, so `check` answered admissible and `assert` threw a bare
  `IndexOutOfBoundsException` from inside the store; `connective-problems` refuses it
  `:not-well-formed` at both doors. **And a rule cannot be stored inert:** `assert-inert` is
  the labeling primitive, and what one bought was a rule that had never been through
  `index-rule-sentex` — believed, unreachable by any chainer, and unfixable by a later
  `assert` of the same rule. Refused `:not-indexable`, with the message naming the other
  inertness: `set/inertRule` is a rule that is believed, indexed, browsable and fires
  neither way. Beside them, five legal API calls stop failing under `clojure.spec`
  instrumentation. *Class:* **Refusal** for both — one shape reached a stack trace rather
  than storage, the other a rule nothing was firing. *Migration:* assert a negated rule as
  the positive rule with the negation in the consequent; a rule meant as documentation is
  `set/inertRule`, and one already stored inert is `retract!`ed and re-asserted.
  [docs/solving.md](docs/solving.md), [docs/inference.md](docs/inference.md)

- **Storage keeps no dead frames, and a torn dump refuses.** A round of durability fixes
  across the disk store, the overlay and both import paths — the class the gate's memory
  backend cannot see, which is why the matrix exists. **`:truncated-dump`** compares frames
  read against what `meta.edn` states on both import paths, and the records-only path
  refuses a dump naming a handle twice, where the second frame silently destroyed the first
  record and counted both. No frame whose only fate is a tombstone: `unmark-premise!`
  re-stores only a record carrying a strength, and the overlay's set insert removes a
  removal record only when one exists. Two reads at open: `validate-idx-tail!` rides the
  chunked walk instead of a seek per slot, and `rebuild-premises!` tombstones crash damage
  only, rethrowing `:unknown-frame` — a build that cannot read a log must not delete it.
  Index entries are normalized at the export frame, so one logical index stops dumping
  byte-differently per backend. *Class:* **Refusal** for the two new kinds — one input is a
  truncated file, the other loses a record it reports as loaded. *Migration:* re-export.

- **The uberjar loads the ontology it ships.** Layer discovery listed a directory, which a
  packaged jar need not carry, so an uberjar started with `CxCore` alone and no upper or
  middle layer — silently, the KB simply being smaller than the same tree run from source.
  Discovery lists the jar's own entries now, anchored on `kb/CxCore.txt`, and an unlistable
  protocol is refused rather than answered nil. *Class:* neither label; a caller running
  from source saw every layer already.

- **ASP routes to a solver that can actually run.** `AUTO` handed off past the size cutoff
  on `available?` alone, so a machine carrying `libclingo` and no `clasp` binary solved
  small programs and threw on large ones — the failure arriving with the workload rather
  than at the probe. The handoff is gated on a once-per-JVM probe that runs the binary; a
  missing one is `:solver-unavailable`, `clingo`'s aspif temp file is deleted on any exit,
  and `dense-roots`' reserved family throws `:reserved-family` rather than pinning a
  three-element decode for a four-element key. *Class:* **Refusal** for the two new `:type`s.
  *Migration:* install `clasp` if you relied on the large-program path, which was throwing.

- **The daemon answers a caller's mistake with 400, and the model's tool surface loses two
  ops.** `:export`'s five destination refusals join `serve/client-error-types`, so a
  directory that exists and is not empty stops counting as a backend fault at every reverse
  proxy between the caller and the daemon; and `:preview` and `:clear-caches` are excluded
  from the tool surface a model reaches, neither being a read whatever its name suggests.
  A cancel can no longer unsettle a finished job. *Class:* **Breaking** — a status code, and
  a removal from the exposed tool set. *Migration:* a client that retries on 5xx will report
  these instead of retrying, which is the intent; call either op on the daemon or through
  `vaelii.core` directly.

- **The browser writes what it shows, and shows what the ledger holds.** Four ledger kinds
  are about a pair or a budget rather than a dropped sentence, so each row printed "nil"
  beside a live link to `/term?q=nil`, while `:message` at the top level went unread on the
  two kinds that put it there — both renderers read either now, and `core/violations` states
  that `:sentence` and `:context` are not on every entry. The editor survives a
  conjunction-concluding line, which was refused `:bad-handle` *after* the write had landed;
  a write is refused while an export walks the KB; `unload!` waits for a `:cancelling`
  loader as for a running one; and a repeat source's key suffix is one past the highest
  still loaded. A fork with an opts map naming neither `:space` nor `:dir` lands on its own
  space rather than the shared process default, where two forks saw each other's writes.
  A KB whose store cannot be counted renders `:unreadable` rather than as a healthy empty
  one. *Class:* neither label. [docs/overlay.md](docs/overlay.md), [docs/web.md](docs/web.md)

- **CLI flags mean what they say.** `assert-rule` passes the `--strength` it parsed —
  accepted-and-dropped stored a known-true rule at `:default` — and asserting a rule that is
  already stored now marks the premise, which matters more: a generator's stamped rule is a
  conclusion, so asserting it returned a handle for a rule that retracting the generator
  took away. The class resolves from content, as `:direction` and `:defeasible` do. A value
  flag refuses a following flag as its value instead of opening a directory literally named
  `--starter`; a flag belongs to the commands that read it, and one carried elsewhere is
  refused rather than dropped; and refusals print on **stderr**, so a script reading stdout
  as EDN gets data. *Class:* **Breaking** for the stream move and the per-command roster,
  **Refusal** for the flag-as-value. *Migration:* redirect with `2>&1` if you read refusals
  off stdout; drop the flags your commands were ignoring; re-assert any rule whose
  `--strength` was dropped. [docs/canonicalization.md](docs/canonicalization.md)

- **Three more costs read the change rather than the KB.** The overlay's removal record asks
  the base `kv-member?` instead of materializing the whole posting per probe;
  `refresh-equality` walks the moved handles through a reverse map instead of re-asking
  belief of every supporter per merge; the qualitative join baselines live in their own
  bounded map, so the resident cache clearing at its limit no longer degrades every later
  delta join to a full one; and `settle`'s `clash-candidates` sorts the moved region only
  when something reads the order — a `:refuse` KB, the default, paid two sorts per settle to
  feed a pass that was never going to run. `core/check`'s docstring says what it predicts
  and what it does not. *Class:* neither label; each answers what it answered.


## 0.5.1 — 2026-08-11 — "faster writes, more to watch"

A run of costs that grew with what the
KB *holds* rather than with what the write *touched* — the taxonomy reconcile, the five
flat caches, the reified-NAT orphan sweep, a retraction's teardown, the standing-clash
ordering, a context-cycle repair, a repeated closure ask and a query plan's child count —
each now reads forward off the region a settle moved, and each has a `lein perf` check
standing where the claim is. Four places where **arrival order decided an answer** are
closed. Beside them the process gained instruments for the rest: the change feed crosses
the process boundary as a subscription with a cursor, long work is a job registry with a
screen that watches it, `kb-quality` reads the knowledge where every other instrument
reads the engine, and the conjunctive planner costs a join rather than a column of
literals.

**No entry is Breaking**, which is why this is a patch. Three carry a *Migration* line
anyway, because a caller can observe them and should be told what to expect.

**Triage, for a 0.5.0 caller.** This is the index to what touches something you have written.

| If your code… | Then |
|---|---|
| reads the first N of `preview` / `edit-with-consequences!`'s `:believed-added` or `:believed-removed` | you get a different N — the halves are content-ordered now, and were handle-ordered |
| calls `clear-caches` and expects the literal cache's hit rate to zero | pass `{:counters? true}`; the reset is off by default |
| walks a `declared-transitive` predicate that also declares an `inverse` | the walk sees the inverse-recorded hops too, so an `ask` can answer more |
| branches on `violations`' `:violation` with a defaultless `case` | `:arbitration-truncated` is a new kind |
| builds on the shipped Space or Time vocabulary | an argument position that held `thing` now names a type, so an assert 0.5.0 accepted can meet an `:arg-type` refusal — widen the convicting declaration it names, or state the argument at a type the position admits |


- **A settle pays for the region it moved, not for what the KB holds.** Eight reads were
  charging the second. `refresh-relation` walked every supporter to decide whether to run
  and recomputed every edge's believed-supporter set — 176.6 ms in a 64k-edge relation —
  where `:handle-edge`, the transpose of `:support`, reads the scope forward off the moved
  handles: 9.2 µs. The five flat caches read `:cache-support` backward, so every settle
  paid the declared vocabulary to learn it had nothing to do: 5.0 ms at 32k declarations,
  against 5 µs read forward off `:cache-handle-keys`. `record-clashes!` ordered every
  standing clash report on the settle path, so an assert into a KB holding 800 dilemmas
  paid for a reading nobody asked for — stored in arrival order and ordered at the read by
  `settle/ranked`. A `genl` edge with nothing above or below it cost 800
  `arbitrable-violations` calls and a `genlCx` edge re-derived 400 opposed bodies, both
  weighed per pair now; `refresh-supersessions` re-examined every displaced spelling every
  settle; and a negated exception conjunct registered under `not`, hiding the predicate it
  is about, waved the recheck through to `:all`. What the scoping removed was a whole-KB
  rescan four writers leaned on, so a writer touching a shared edge records it in `:dirty`
  / `:cache-dirty` and the reconcile takes those whether or not belief moved there. Gates:
  `taxonomy-belief-flip`, `flat-cache-belief-flip`, `standing-clash-reading`,
  `taxonomy-edge-arbitration`, `context-edge-arbitration`. *Class:* neither label; every
  reading answers what it answered. [docs/taxonomy.md](docs/taxonomy.md),
  [docs/equality.md](docs/equality.md)

- **The arbitrating half of a bounded pass says when its budget stopped it.** The reporting
  half filed `:exposure-truncated`; the half that spends the same budget *before anything
  is decided* said nothing, so a KB could leave standing a pair a finished sweep would have
  defeated and show a clean ledger. **`:arbitration-truncated`** (`:triggers` `:sample`
  `:budget` `:message`), one entry per settle; pairs past a cut go undecided rather than
  decided the other way, and discovery accumulates in `:clashes` so a later settle can
  surface them. *Class:* Additive — a new `:violation` kind.
  [docs/taxonomy.md](docs/taxonomy.md)

- **A `disjointMetatype`'s membership is vocabulary, not a roster.** `(disjointMetatype M)`
  separates M's members by being consulted, so `(M b_t)` leaving stopped separating the
  pair while the mark still stood, no closure moved, and neither member was in the region —
  the KB kept reporting a dilemma the oracle does not. Only the departure was silent.


- **Four places where arrival order decided an answer.** A predicate's **second declared
  inverse** hid its first: the taxonomy held one partner per predicate, so
  `(transitive beforeEv)` proved a chain with `afterEv` declared second and failed with it
  declared first, and retracting one dropped the whole entry. `:inverse` is
  `{predicate -> #{partners}}` now, maintained in both directions; `inverse-of` keeps its
  shape and answers the lexicographically smallest. **`kb-quality` ranked its capped lists
  on the handle**, so two loads of one KB reported the same `:never-count` over a different
  `:never`. **A preview's capped diff** was built off a region sorted numerically, so the
  browser's 50-row panel showed a different fifty depending on load order, with `:bounded?`
  true either way. And **an LLM prompt** was cut before it was sorted, so a term past the
  cap was shown a prefix of arrival order. All four rank on content — sentence then context
  — at the point each caller caps, and the LLM heading tells the model it is looking at a
  sample. *Migration:* a caller reading the first N of either preview half gets a
  different, better-defined N. *Class:* neither label; a sequence that moved with load
  order was never a contract. [docs/preview.md](docs/preview.md),
  [docs/taxonomy.md](docs/taxonomy.md), [docs/llm.md](docs/llm.md)

- **A card's cut is a count, including the cut that was not counted.** `used-with` claimed
  everything its scan missed was still offered under a later tier, which is false for
  exactly the predicates it exists to find; `:dropped` gains `:unscanned`, one O(1) read per
  position. Beside it, `correct.clj` took `first` of a position's `argIsa` declarations, so
  two contexts declaring one position decided by index order whether a reversed-argument
  alternative was offered — it ranks by specificity now. A declaration's supporters were
  being lost the same way: the `disjointMetatype` sweep walked *believed* memberships where
  it records *supporters*, so a membership defeated at that moment could never be revived,
  and `derive-functional-equalities` took `first` of a `(functional P)` stated in two
  contexts, so retracting one withdrew a merge the other still licensed.


- **The model backends refuse by name, never by value, and a turn that ran out of tokens is
  not a deletion.** The JDK rejects a bad header character by quoting the value verbatim,
  and the browser renders that onto the proposal panel — so a `.env` ending in CRLF was one
  hop from putting an API key on a page; it is `{:type :llm-bad-credential}` carrying no
  value. A streamed body reads under a watchdog (`:llm-timeout`), a 200 whose body is not
  JSON raises `:llm-bad-response` with a bounded excerpt, and eleven sites catch `Throwable`
  — a `StackOverflowError` on deeply nested model text read as *the model proposed nothing*,
  `canon` overflowing around 500 nestings against the EDN reader's 5,000. `:stop-reason` is
  read before the diff, so a truncated turn is `:truncated` rather than every row the model
  never reached coming back as a `:remove`. `apply-proposal!` calls `edit!`, which is not a
  transaction, so it returns `{:result :applied :failed-at :error}` and runs the settle by
  hand on the failure path. *Class:* Additive for the three new `:type`s.

- **The taxonomy's closures terminate, scope their repairs, and read a repeat.** A `genlCx`
  edge out of a context that sees another one back never returned: the depth potential ranks
  the condensation, and `raise-depth` lifted a single node, which put it above its own mate
  round the cycle without end — the lift moves whole components now. Retracting one edge of
  a context cycle rebuilt every component (11.19x across 16x a background the retraction is
  not about); an edge merely *incident* on a cycle is left alone, and the same retraction
  reads 0.97x. `TransitivePredicateProver` holds the reach per
  `[direction predicate node context]` stamped with the change clock, and a closed goal
  reads the cache without filling it; `(P ?x ?x)` cost a closure per node to answer nothing
  and is one Tarjan condensation. And a transitive predicate's hops are the believed
  matches, the **inverse spelling among them**: `(transitive before)` walked stored `before`
  facts alone, so an `(inverse before after)` chain broke mid-walk and answered negative
  with no diagnostic. *Migration:* such an `ask` returns at least what it did and never
  less. *Class:* Additive for the cache; neither label for the rest.
  [docs/taxonomy.md](docs/taxonomy.md), [docs/storage.md](docs/storage.md)

- **A unary fact about a reified NAT was deleted with the constant, silently.** One clause
  of the orphan sweep matched on **arity alone**, so `(prime (PrimeFn Seven))` — a claim
  somebody asserted — made the constant look orphaned once its other uses went, and the
  sweep retracted the claim with it. No error, no report. Bookkeeping is decided by
  **authorship** now: `nat/minted-for` re-derives what `mint-nat!` wrote, and everything
  else naming the constant is somebody's assertion whatever its arity. The sweep also cost
  what the whole KB had ever reified — matching `(termOfUnit ?k ?e)` after every teardown
  and to a fixpoint, 16.70x across 16x the NATs the retraction is not about, which on a
  corpus of OpenCyc's order is seconds per retraction — and asks only about the constants
  the teardown's own removals named: 1.22x, gated by `retract-nat-scaling`. A teardown
  records only what that sweep will read, so a KB that reifies nothing pays nothing.
  *Class:* neither label; a caller whose unary claim was being deleted underneath them was
  not getting what they believed.


- **The change feed crosses the process boundary, as a subscription with a cursor.** `watch`
  takes a function and a function does not cross an EDN wire, so the daemon's half is
  `:watch` / `:poll` / `:unwatch` / `:watchers` over a ring and an integer cursor — all four
  in `serve/feed-ops` rather than `serve/ops`, which is what keeps a subscription out of the
  model's tool set. A parked long poll held a thread nothing counted, so 55 concurrent polls
  drove the 50-thread pool to 50/50 busy and `/health` from 62 ms to 25,997 ms: `max-parked`
  (16) bounds how many may wait, and a poll that does not ask to wait is never refused.
  `{:wait-ms 1e300}` answered 500 and `##NaN` made the poll answer instantly forever — it is
  `nat-int?`, capped before coercion. What one caller can allocate is bounded three ways,
  nothing authenticating `POST /op` on the loopback default: 64 subscriptions, 256 events
  per ring, and one unpolled for five minutes reaped at the next call. The ceilings bound
  the event count and not the bytes, and the docs say so. *Class:* neither label — the feed
  is new in this release. [docs/feed.md](docs/feed.md)


- **A conjunction is costed as a join rather than as a column of literals.** `plan/est-rows`
  answers what `est-matches` does not — not *can* this literal fan out, a sound upper bound,
  but *how much*, an expectation wrong in both directions and composing for exactly that
  reason — returning the relation's shape and threading it through the planner's fold, so
  the *k*-th pick is costed against the rows reaching it. **No statistics table**: every
  number is already in the count-aware trie, and where neither side read a count the model
  falls back on a proxy rather than calling the join a cartesian product. Generators are
  split into connected blocks and ranked by adjacent transposition, with two placements
  outside the law because they are claims an estimate cannot make. Planning one fixed
  conjunction is now flat in the size of the KB, `plan-scaling` reading flat with
  `p/count-children` against 24.6x without. `lein bench-plan` reports the q-error per join
  depth: 1.00 through six literals, and 1.00 / 2.75 / 2.87 on a corpus built to break the
  independence assumption where a compounding model would read about 7.5 at depth 3.
  `query-plan` carries `:est-rows`, `:est-prefix` and `:block` beside `:est-matches`.
  *Class:* **Additive**; a new `IndexStore` read, owed by both implementations.
  [docs/inference.md](docs/inference.md), [docs/indexing.md](docs/indexing.md)

- **Long work is one mechanism: a job registry, and the screen that watches it.**
  `vaelii.impl.jobs` holds every operation that takes minutes rather than milliseconds, with
  one status vocabulary, one progress reading and one cancel; `/jobs` watches them, a job
  survives the request that started it, and nothing unsettled is ever dropped, since
  forgetting a job releases its writer claim while a thread still running is still writing.
  The catalog's load and export moved onto the registry rather than beside it, and
  `POST /chain` became a job — a fixpoint over a corpus was minutes of this process's one
  writer inside a request, with nothing on screen and no way to stop it. A second writing
  job is refused `:job-busy`, naming the job that holds the writer. *Class:* not Breaking;
  `:busy` was thrown at one impl site and read by one impl namespace.
  [docs/web.md](docs/web.md)

- **What this process is holding, on a page — caches, heap, and the profiler.** Nothing
  measured what the engine holds *beside* the store, which is a dozen derived structures
  whose whole purpose is that a repeated question is not recomputed. `caches` is one read
  over all of them — entries, the bound they are cleared at, what one entry counts, and the
  hit rate where anything counts one. A row carries `:scope` and `:counters` because the two
  differ: the literal cache's entries are one KB's and its counters are global. Every
  cache-holding namespace declares itself into a register at load, so there is no central
  list to forget, and a row that throws costs its own row and no other. The clear is a
  measuring instrument rather than an edit — bare rather than `!`, moving no belief, usable
  while a load runs — and it no longer zeroes the process-wide hit counters every other KB
  in the JVM was reporting: that is `{:counters? true}`, off by default. *Class:* neither
  label; both are new in this release. [docs/web.md](docs/web.md)

- **The shipped ontology declares its positions, and decontextualizes predicate metadata
  and nothing else.** `CxSociety` declared `(decontextualizedPredicate marriedTo)` — the one
  *domain* relation carrying a mark the rest of the ontology reserves for claims about a
  predicate — so a marriage stated anywhere became a claim of the whole KB, and a rule
  firing on the lifted copy put `knows` within reach of every data context. 227 `argIsa` /
  `argGenl` declarations fill the positions that carried none, at `thing` throughout, and
  six new upper types narrow them where a constraint should refuse something: Space takes
  `spatial_thing` on all 100 of its positions, Time `temporal_thing` on 46 and `time_point`
  on 16. Flight becomes a capability of a kind rather than a verb-shaped one-place
  predicate, with the exception written twice because there are two things to except.
  `::prop-kind` accepts every kind the engine marks, six of ten having been specced — so
  `:asymmetric`, which `has-prop?`'s own docstring lists, was a documented call
  instrumentation refused. *Class:* no label — ontology content (§3.8); what it owes is the
  roster that pins the shipped set. *Migration:* a KB built on the shipped Space or Time
  vocabulary can be refused where 0.5.0 accepted it — the refusal names its convicting
  declaration. [docs/argtypes.md](docs/argtypes.md), [docs/contexts.md](docs/contexts.md)

- **A bulk load is decomposed, and the index write is 57% of it.** `lein bench-loadphase`
  loads one corpus repeatedly with one more phase stubbed out from the outside in, so
  consecutive runs differ by one phase and the deltas **sum to the baseline**: at 1,000,000
  distinct binary facts on `:memory`, 43.4 µs/fact and 23,100 facts/s, the index write is
  56.8%, the JTMS node and premise mark 21.5%, the special-predicate suite 10.5%. Postings
  are 35–39% of the load and count maintenance 6–10%, so **the counts are priced and are not
  the lever**. Two write-side tricks measured worse and are reported rather than built. The
  one write on that path that grew with the corpus is guarded — the negation memo's `:dirty`
  set took a `conj` per fact — which does not move the wall clock but removes a structure
  proportional to the corpus. `lein bench-profile` grows the two arms no reasoning workload
  runs: an interactive arm whose read table is the inverse of every other's (88%
  `:term-index`), and a churn arm, the only way `unindex-sentex!` runs at all.
  [docs/storage.md](docs/storage.md), [docs/profile.md](docs/profile.md)

- **Eleven checks join the perf gate, and 27 in the vector all judge.** A read of the
  standing clash set is Ω(n log n) by construction, so `standing-clash-reading` is calibrated
  from both ends — 85.4x and 80.9x healthy over a floor near 66x, 937.8x with the read
  filtering by cross product — and ships at 175x. `retract-merge-scaling` reads 5.66x alone
  and 10.49x in place and ships at 18x: `lein perf` runs one JVM over the whole vector, so
  that position dependence is a property of the harness rather than of the engine.


## 0.5.0 — 2026-08-07 — "operating the engine as a service"

Operating the engine, in the two senses a running process needs: what it will let a caller
do, and what it will tell an operator it is doing. The daemon authenticates and refuses to
bind an address without a credential, ships as a container image, and says which posture it
started in; every switch the build reads has a row in a table a test keeps honest; the log
level is a dial a running process turns; and the failures that look like answers each
gained something that says so. Nine entries are **Breaking**; the three **Refusal** entries
(§3.8) cover input where what 0.4.0 did with it was run a configuration nobody asked for
and report a clean pass.

**Triage, for a 0.4.0 caller.** Every Breaking and Refusal entry carries its own one-line
*Migration*; this is the index to the ones that touch something you have written or
deployed.

| If your code… | Then |
|---|---|
| names `:record-space` / `:index-space` | one `:space` — keep the record number, drop the index one |
| runs a daemon on a non-loopback `--listen` | export `VAELII_API_TOKEN` there and in every client, or it exits 2 |
| reads a daemon 401, or branches on the wire `:type` | `:unauthorized` is a new one; `GET /health` is the only route without the token |
| relies on `VAELII_RETE=0` running the sweep | it means off now; unset, or `=1` for on |
| sets `VAELII_NOHIER` | it is `VAELII_HIER`, the other way up — `VAELII_NOHIER=1` becomes `VAELII_HIER=0` |
| sets `VAELII_QUERY_ENGINE` / `VAELII_QUERY_STRATEGY` | a name outside the roster is refused rather than silently running the default |
| sets `VAELII_WEB_PORT` for `lein browser` while `-main` stayed on 3000 | it moves both; pass `--port 3000` to pin `-main` |
| lists KBs out of a search-path directory holding more than 200 | name the ones that matter in the catalog file |
| depends on vaelii and has no SLF4J provider of its own | add one — `org.slf4j/slf4j-nop` no longer arrives transitively |
| branches on what `term-role` answers | `:sense` and `:lexeme` are two new answers — add arms, or a `default` |
| writes a `lex`-namespaced predicate | it names a lexeme now, and a lexeme names no relation |
| calls `core/context-size`, or sends the daemon `:context-size` | both are `count-in-context` — same arguments, same answer |
| compares two compound terms with `different` | a merged symbol inside one now makes them equal, where it did not |
| sets `VAELII_ASP_SOLVER` to a name outside `clingo`/`clasp` | it is refused at `open-kb` rather than silently running auto |

- **Breaking: a name can carry two more roles — a sense, and a lexeme.** `term-role`
  answers `:sense` for a disambiguated type and `:lexeme` for a symbol in the `lex`
  namespace, so its documented domain gains two values a total `case` has no arm for; a
  lowercase dashed name is a legal unary type where it was refused, and a lexeme applied to
  arguments is refused (`:lexeme-functor`). *Migration:* add `:sense` and `:lexeme` arms or
  a `default`; a `lex`-namespaced predicate names a lexeme now and cannot be applied.
  `docs/naming.md`.
- **Breaking: `context-size` is `count-in-context`.** The three O(1) cardinality readers are
  one family and two of them said so. *Migration:* `(v/context-size kb ctx)` becomes
  `(v/count-in-context kb ctx)` and `{:op :context-size}` becomes `{:op :count-in-context}`
  — same arguments, same answer, old spellings gone rather than deprecated.
  `docs/api.md`, `docs/indexing.md`.
- **Breaking: `different` descends into compound arguments.** It normalized each argument
  with one lookup in the symbol-keyed equality closure, so a compound was never found in it
  and `(different (QuantityFn 5 Kilogram) (QuantityFn 5 Kg))` answered *different* with
  `(sameAs Kilogram Kg)` believed. *Migration:* a goal comparing two compounds can newly
  answer false where a merge reaches inside one; comparing symbols is unchanged.
  `docs/equality.md`.
- **Breaking: one space number names a KB's stores, `:space`.** A `:disk` KB's derived
  directory is `space-<n>`, and the suite owns a block of two db numbers rather than four.
  *Migration:* `{:record-space 2 :index-space 3}` becomes `{:space 2}`; either retired key
  is refused by name (`:unknown-option`) rather than ignored, and `:dir` names a durable
  directory the derived spelling does not reach.
  *Breaks:* `:record-space`, `:index-space`
  `docs/storage.md`.
- **Breaking: the daemon authenticates, and refuses to bind an address without a token.**
  With `VAELII_API_TOKEN` set every request carries `Authorization: Bearer <token>` or is
  answered 401 `{:type :unauthorized}`, with `GET /health` the only route that answers
  without it. `--listen` naming a non-loopback address without a token is one line on
  stderr and exit 2, where 0.4.0 logged a warning and served the whole write block to
  anything that could reach the port. *Migration:* export `VAELII_API_TOKEN` for a daemon
  that names an address and give the same value to every client; nothing changes on the
  loopback default. `docs/operations.md`.
- **Every switch the build reads has a row, and a test keeps the roster honest.**
  `docs/operations.md` gains a configuration table — 56 environment variables and system
  properties, each with where it is read, its legal values, its default and the one thing it
  decides. `config_surface_test` pins the names in both directions and checks each
  `file:line` citation against the line it names, so the table cannot drift without a
  failing test.
- **Refusal: the four harness switches read a value instead of a presence.** They were
  membership tests, so `=0` ran the sweep it names, and the two query switches took a bare
  `(keyword …)`, so a misspelt engine ran the *default* and reported a clean pass for a
  configuration nothing exercised — the worst shape a test switch can have, since the result
  reads as evidence. *Migration:* none for a value in the vocabulary; a job relying on `=0`
  meaning *on* now gets the sweep off. `docs/operations.md`.
- **Refusal: the ASP backend switches are read against their domains, at the door.** A
  misspelt `VAELII_ASP_SOLVER` matched no arm and ran auto, so a run pinned to clasp could
  use clingo and report a clean pass; `VAELII_CLINGO_MAX_BYTES` threw from the first ASP
  solve rather than from the configuration that was wrong. Both go through `config/check!`,
  refused at `open-kb` by name. *Migration:* none for a legal value. `docs/operations.md`.
- **Breaking: `VAELII_NOHIER` is `VAELII_HIER`, and the sense is the other way up.** A
  switch carrying the negation in its own name makes `=0` mean *on*, and the entry above had
  just made the value load-bearing. `VAELII_HIER` defaults true. *Migration:*
  `VAELII_NOHIER=1` becomes `VAELII_HIER=0`; a `VAELII_NOHIER` left set is simply unread,
  since a variable cannot be refused by name. `docs/operations.md`.
- **The log level is a dial a running process turns.** `set-log-level` takes one of
  `:error :warn :info :debug :trace` and installs Trove's console backend at it; `log-level`
  reads back what is in force, and `VAELII_LOG_LEVEL` says it at startup. Unset, the engine
  installs **no** backend at all, so an application holding its own `*log-fn*` keeps it.
  Three `:debug` statements are what make turning it up worth doing. `docs/operations.md`.
- **Breaking: `VAELII_WEB_PORT` moves `-main`'s port, and not only `lein browser`'s.** Both
  read one `default-port`: the variable, else the `vaelii.web.port` property, else 3000, and
  an explicit `--port` still wins. *Migration:* a deployment that set the variable for `lein
  browser` while relying on `-main` ignoring it now moves both; pass `--port 3000` to pin it.
- **Breaking: a search-path directory is probed for its first 200 entries.** `sources` is
  recomputed per request, which is what lets a corpus appear with no restart and what made
  the scan unbounded. The cut is named on the page and in the log, since a list that quietly
  ends early reads as "this machine has no other KBs". *Migration:* name the ones that
  matter in the catalog file to list them regardless of the count. `docs/catalog.md`.
- **The front door says what a legal-but-wrong sentence should have been.** `(isa Muffet
  Dog)` breaks no naming invariant, so it stored a two-place relation nothing reads while
  `isa?` answered false with nothing to search for. `nm/advice` reads intent where
  `problems` reads the invariants, logging `:warn` once per process with the rewrite that
  was meant; a `:no-placement` drop names `genlCx` beside the entry's own keys.
  `docs/naming.md`.
- **A second `open-kb` defaulting onto the shared in-RAM space now warns**, naming both
  fixes — give the KB its own number, or name `{:space 0}` to say the sharing is meant. A
  warning rather than a refusal, since sharing the space is how `recover` sees the same
  records and how a base is mounted. `docs/storage.md`.
- **Refusal: the CLI checks each command's argument count before it dispatches.** `dispatch`
  reached into `args` with `nth`, so a short line answered `error:
  IndexOutOfBoundsException` and a long one dropped the extra operand in silence. One table
  carries every command's arity, operands and gloss, so `check-arity!` and the usage text
  cannot go out of step. *Migration:* none at the right arity; `lein cli help` prints the
  count each command takes. `docs/operations.md`.
- **`docs/troubleshooting.md` is a new page, indexed by symptom rather than by subsystem.**
  The engine's hardest failures are the ones where nothing goes wrong — a query answers
  `()`, an `assert` returns a handle — so a reader has to already know the cause to find the
  page explaining it. Nine symptoms, each with what you would have observed, how to confirm
  it in one call, and the fix.
- **`lein lint` gains a versions check, and the kondo row notes a local/CI mismatch.** The
  0.4.0 bump left the `:with-foreign` pin naming `0.3.0`, so every
  `lein with-profile +with-foreign` command failed to resolve; `lint-versions` reads that
  pair and the `lein-cloverage` version stated twice.
- **Three doc samples now print what they actually produce, and `prove`'s docstring says it
  counts proofs, not answers.** A goal reachable both as a materialized fact and as the rule
  concluding it comes back twice with equal maps — wrap in `distinct`, or reach for `query`
  / `ask`, which project to the goal's variables.
- **The daemon ships as a container image**, with a two-stage `Dockerfile` and
  `docker-compose.yml`. The container binds an address, so the token is required — an image
  run without `VAELII_API_TOKEN` does not start rather than serving unauthenticated — and
  one container per volume, a second opener being refused `:disk-locked` rather than scaled,
  which is why the compose file carries no `replicas:`. `docs/operations.md`.
- **A reflection warning and an uncalled public var now stop the build.** Both signals were
  already emitted and neither was read: `reflect` compiles `src` and `bench` and fails on
  any reflection, auto-boxing or primitive-recur warning, and `unused` fails on a public
  definition with no usage against a baseline. Ten warnings had to go first, none in `src`.
- **Breaking: `org.slf4j/slf4j-nop` no longer reaches a consumer's classpath.** It sat in
  top-level `:dependencies`, where it could win SLF4J's provider race against a consuming
  application's own backend and silence it — the one thing a library must not do on a
  consumer's behalf. *Migration:* an application that had no provider of its own and relied
  on vaelii's now sees SLF4J's "no providers" line again — add one as its own dependency.
  `docs/operations.md`.
- **A public `--listen` bind with no `VAELII_ALLOWED_HOSTS` now warns.** Naming an address
  drops the `Host` allowlist to every `Host` answered — deliberate, since a reverse proxy
  sets its own — but nothing said so at startup. `host-posture` names the policy beside the
  token question, apart from the TLS line so a reader knows which check is missing.
- **`docs/troubleshooting.md` and `docs/storage.md` name `:type :unknown-backend`.**
  `open-kb` throws it from five call sites and none carried a line in either doc; the entry
  reads the other key each throw's ex-data carries to say which of the five it is.


## 0.4.0 — 2026-08-05 — "correctness fixes against the invariants"

Correctness fixes found by reading the engine against its own stated invariants, in the
places 0.2.0 and 0.3.0 did not reach: a backward-chaining loop guard that made a
conjunctive query answer nothing, doors that disagreed about what they would accept, an
index trusted without being checked against the records it describes, slots and keys that
let arrival order decide belief, and derived caches a settle read one revival out of date.
Thirteen entries are **Breaking**, which is why this is 0.4.0. The **Refusal** entries
(§3.8) cover input where what 0.3.0 did with it was corrupt state or answer a different
question in silence.

**Triage, for a 0.3.0 caller.** Every Breaking and Refusal entry carries its own one-line
*Migration*; this is the index to the ones that touch source you have written.

| If your code… | Then |
|---|---|
| hands `assert` text it did not read as EDN | it is refused (`:shape`) — fix the producer |
| writes `exceptWhen` literals like `(lives_in ?x cold_place)` | spell them to the invariants; re-check any rule 0.3.0 left bare |
| spells an `edit!` batch `{:adds …}` | spell it `{:add […] :remove […]}` — the old key wrote nothing |
| names one of `:record-space` / `:index-space` | name both, or neither, in every opts map |
| passes `:direction` to `assert` on a non-rule | it is refused; a rule takes it and now acts on it |
| states one rule two ways (bare `implies` after a `set/*Rule`) | the slots join by content; `retract!` and re-assert to narrow one |
| calls `edit` or `edit-with-consequences` | they are `edit!` and `edit-with-consequences!` — the wire op stays `:edit` |
| matches `:bad-opt`, or a `:shape` from a non-map `opts` | match `:unknown-option` |
| reads a dump's `meta.edn` dialect | it is `:vaelii` |
| stores skolem witness names across runs | the names moved; rebuild from the assertions rather than carrying both spellings |
| parses a daemon 500 for a client mistake | it is a 400 with a `:type` |
| writes `(ist Ctx S)` with other than three elements | it is refused with `:shape` |

- **A conjunctive query could answer nothing while each of its conjuncts answered.**
  `[(anc Tom ?y) (anc Tom ?z)]` was empty where `(anc Tom ?y)` answered twice: the per-path
  loop guard grew for a whole frame, and a queued conjunct is a sibling of the expansion
  rather than a descendant. Silent in every direction — forward chaining and the node engine
  both answered, `provable?` said false, and `prove-within` reported `:status :complete`.
  `docs/inference.md`.
- **Breaking: `assert` refuses a sentence that is not an s-expression.** A string — what a
  failed EDN read hands back — was stored, indexed and believed as an object no query can
  match; `nil` likewise; a symbol, number or map threw an untyped
  `UnsupportedOperationException`. `check` refused all five, so the door built to predict
  `assert` disagreed with it. *Migration:* nothing a working caller sent is refused; fix the
  producer that handed `assert` unread text, and discriminate on `:shape`.
- **Breaking: an `exceptWhen` query's literals are held to the naming invariants.** A
  literal `docs/naming.md` says is refused was stored as an exception no query could match,
  so the rule read as guarded and fired as bare. Both doors read each conjunct before the
  rule is stored. *Migration:* spell the exception's literals to the invariants, and
  re-check any rule 0.3.0 left bare.
- **Breaking: an `edit!` batch key nothing reads is refused.** `{:adds […]}` bound nil, so
  `edit!` wrote nothing and reported a success, while `check-edit` — whose job is to predict
  exactly that — reported no problem; over the daemon it was a `200 {:ok true}` for a write
  that did not happen. *Migration:* spell the batch `{:add […] :remove […]}`.
- **Breaking: naming one in-RAM space number and not the other is refused.** The two default
  independently, so `{:backend :memory :record-space 77}` paired a private record store with
  the process-default index every other in-memory KB writes: `assert` found the other KB's
  handle, read it as a duplicate, **stored nothing**, and returned a handle `in?` answered
  true for. *Migration:* name both or neither, in every opts map.
- **A durable index is checked against the records it claims to describe.** `layout.edn`
  gated the index's key shape and nothing gated its coverage, so a short index opened clean,
  answered short forever and re-cemented its own stamp — and re-asserting a fact it could
  not find minted a second handle for a sentence already stored. Three ways in: a torn
  `kv.log` tail, a directory grown under a derived-index mode, and a crash between the
  record write and the index batch. `docs/storage.md`.
- **Breaking: `assert` acts on `:direction` instead of accepting and dropping it.** Only
  `assert-rule` read the key, so a rule asserted `{:direction :backward}` stored `:both` and
  forward-chained, materializing the cross product a backward-only rule exists to avoid. A
  `:direction` on a non-rule, one contradicting the sentence's own wrapper, and a value
  outside the roster are refused. *Migration:* spell the direction; a `check` caller matching
  `:shape` for a non-map opts matches `:unknown-option` now.
- **Breaking: a re-asserted rule's direction and defeasibility resolve by content.** Neither
  slot is in the identity key, so a rule stated two ways resolved to one record and the
  second spelling was dropped — arrival order deciding a slot that decides belief. A bare
  `implies` after a `set/inertRule` stayed inert and never fired. The resolution reaches
  conclusions already derived, a justification baking the rule's contribution in at fire
  time. *Migration:* the join only widens a slot; to narrow one, `retract!` and re-assert.
  `docs/canonicalization.md`.
- **The derived caches are reconciled with what `clear-defeats!` revived.** A settle lifts
  last settle's defeats at its top while the cached closures were refreshed only in
  `settle-finish` — after `constraint-nogoods` had read them — so discovery asked its
  question against a vocabulary one settle out of date, and a `P`/`¬P` pair made visible by
  a revived `genlCx` edge went unarbitrated in a state `recover` disagrees with.
- **The disk KV index reads and publishes its RAM map under the lock.** `apply-ops!` read
  `@data` before acquiring and published after releasing while `compact!` runs on the
  durability daemon's executor — a thread the single-writer contract says nothing about — so
  a compaction in either window rewrote the log from a map missing the in-flight write.
  `kv-clear!` was sharper: a compaction between its truncate and its publish wrote the whole
  pre-clear map back over the log just emptied.
- **Breaking: a client's mistake answers 400 with a `:type`, not 500 with none.** An
  unreadable body, a wrong argument count and an unknown op all answered untyped, the first
  two as 500s — which count as backend faults at every reverse proxy and 5xx alarm. The
  engine's whole refusal vocabulary answers 400, unlogged. *Migration:* branch on `:type`
  rather than on the status code; every `{:ok false}` carries a non-nil keyword.
- **The browser's `/propose/*` EDN read catches `Throwable`**, as every other untrusted-EDN
  read in the namespace already does: a deeply nested form raises `StackOverflowError`,
  which an `Exception` catch let escape, and the browser has no exception middleware.
- **Refusal: `query` refuses a non-map `opts` and a negative or non-integer `:max-depth`.**
  Both read as "no depth", which is not an error condition but a *different question* — the
  no-rule-expansion answer, returned as if it were the bounded one asked for.
  `{:max-depth 0}` is admitted: it is that answer asked for by name. *Migration:* none for a
  working caller.
- **Breaking: `edit!` refuses what `check-edit` reports, before applying anything.** The two
  disagreed in both directions: a 4-element `:add` entry applied with the extra silently
  dropped where the dry run reported `:shape`, and a non-sequential entry threw a bare
  `ISeq` error from every door. An unknown `:remove` handle is refused before any entry is
  applied, so a checked-clean batch cannot half-apply. *Migration:* a remove-if-present batch
  filters its handles through `in?` first.
- **The recursive-literal hold-back keys on the peeled predicate.** A `not`- or `ist`-headed
  consequent read its own frame as the predicate, so every frame-headed antecedent was "the
  recursive literal" — two orderings of a negated-head rule minted two handles, and a
  genuinely recursive rule with a negated head lost the hold-back, turning right-recursion
  left-recursive.
- **Breaking: a skolem witness is a function of its rule's content, not its handle.**
  Retracting and re-asserting the same rule re-fired to a *different* witness, so a fact
  stated about the old one silently stopped co-referring — and two KBs holding the same
  knowledge in different orders stored different `termOfUnit` content, a handle in stored
  content that order independence rules out. *Migration:* rebuild the KB from its assertions
  (`export!` / `import!` replays firings) rather than carrying both spellings.
  `docs/skolem.md`.
- **Breaking: `edit` is `edit!`, and `edit-with-consequences` is
  `edit-with-consequences!`.** The batch's `:remove` half runs the same `retract-storage!`
  sweep `retract!` runs, while the name read as additive — the one gap in the `!` roster the
  convention exists to close. *Migration:* rename the calls; the wire op stays `:edit`.
- **Breaking: `:bad-opt` is retired, and one compression spelling survives.** Two keywords
  split one failure class on no rule a reader could predict — seven sites said `:bad-opt`
  where thirty-four said `:unknown-option`. *Migration:* discriminate on `:unknown-option`
  and `:unsupported-compression`.
- **Breaking: the dump's `meta.edn` names its dialect `:vaelii`.** Decorative on the read
  side, but it is a value in the frozen format and a documented key of `import-dump`'s
  return, so the name it carries is now-or-never. *Migration:* a reader matching the old
  value matches `:vaelii`; `import-dump` reads dumps written either way.
- **The node engine's claimed-key reads each guard's identity, not the guard count.** Two
  distinct rules, each carrying its own `exceptWhen`, can rewrite one goal to the same
  canonical residual through the `genl` fan; keyed on the count the two children were one
  key, so the second was dropped before it was enqueued and every answer only its exception
  admits was lost — silently, on the path `query` routes to whenever `:max-depth` is given.
  `docs/inference.md`.
- **A belief flip on a visibility `except` queues the same re-check as its arrival.** Only
  the store and removal chokepoints called `recheck-except`, so an except *defeated* by a
  settle's resolution revived nothing it hid: backward proving answered yes while the store
  held nothing, and which belief set the KB ended with depended on the order the except and
  its defeater arrived.
- **`recover` reads only positive, atomic declarations into the taxonomy.**
  `sentexes-with-functor` returns both polarities and the rebuild arms destructure the
  positive shape positionally, so a stored `(not (genl a b))` bound its inner sentence as a
  taxonomy node and nil as the other — poisoning every cache on any recover, the default
  `{:recover? :auto}` reopen included.
- **A `:neg` nogood is an at-least-one in every reader.** The ASP translation's soft branch
  emitted only the positive body atoms, so a `:neg`-only nogood — what `set/softConstraint`
  over negated choice literals produces — emitted its violation witness as an unconditional
  fact: no steering pressure, and `:violated` reported a satisfied at-least-one as broken.
  `docs/solving.md`.
- **`conflicts` and `contradictions` are content-ordered.** Each report's sides were already
  ordered by content; the *list* came off a hash set of handle-keyed nogoods, so which pair
  `(first (contradictions kb))` returned was an answer about which was typed first.
  `docs/nmtms.md`.
- **Refusal: the connective frames are shape-checked at every door.** An `implies` at arity
  2 threw a bare `IndexOutOfBoundsException` while arity 4 stored a silently truncated rule
  `check` read as clean; `(not A B)` stored as a positive fact whose record and index
  disagreed; a bare symbol passed as a rule literal was accepted, unmatchable; and a
  non-finite measure magnitude stored cleanly, then threw out of every later duration goal
  in the context. *Migration:* nothing a working caller sent is refused — every one of these
  stored an object no query could match.
- **Refusal: the last open rosters close.** `find-terms` and `abduce` take key rosters (a
  misspelt `:keep?` tore down the scratch context whose handles the caller meant to commit),
  the CLI refuses a flag outside its roster, `escalate` refuses a floor outside 0–7, and
  `import-dump` refuses an unknown `:framing` where it guessed a reader and failed as a
  `ZipException`. *Migration:* spell the key or flag as the refusal's roster lists it.
- **Refusal: the web and serve entry points refuse what their grammars do not know.**
  `vaelii.web --listen` with no address parsed to a nil host — Jetty's wildcard bind, with
  the Host allowlist reading nil as *any* — so a truncated command line put the browser's
  unauthenticated write routes on every interface with the rebinding guard off. `serve` read
  its positionals as a prefix, so a misplaced flag ran a disk daemon in memory.
  *Migration:* none beyond completing the command line.
- **Refusal: the opts and shape rosters reach the remaining doors.** The roster guard held
  at `assert`, `why`, `query` and `open-kb`, and every other door took the misspelt key in
  silence — answering a different question than the one asked. *Migration:* spell the key as
  the refusal's roster lists it.
- **Refusal: the operator's mistakes answer in one line.** A CLI flag missing its value bound
  nil in silence — `lein cli assert '(dog Muffet)' Ctx --strength` stored known-true content
  at `:default` — and now exits 1 naming the flag; `--memory --dir` is refused as a
  contradiction. *Migration:* none beyond completing the command line.
- **The browser and CLI survive what they read.** The repl loop and the CLI command arm
  catch `Throwable`, so a deeply nested form answers `error:` and a next prompt; the
  browser's retract POST makes the `check-edit` round-trip `docs/operations.md` promises, so
  a stale handle answers the problem panel rather than a success-styled "Retracted 0
  sentexes".
- **Refusal: every durability switch is read against a domain, and a value outside it fails
  the open.** Each of the thirteen checkable switches was a membership test or an equality
  against one spelling, so none of them had a wrong value — every misspelling was the *other
  branch*, silently: `vaelii.disk.auto-compact=disabled` read as compaction on, and
  `vaelii.disk.fsync=always` as the three-second tick, the level the operator was trying to
  leave. *Migration:* none for a working setup, but two spellings now *act* where they were
  ignored. Spell what you mean. `docs/storage.md`.
- **Refusal: the mapped index image refuses the platform it corrupts on.** The image
  publishes by renaming a new file over the live one while it is mapped, which is what put
  `vaelii.index.snapshot` on macOS and Linux only — `docs/storage.md` said so and nothing
  enforced it, so on Windows the publish failed part-way through a four-file commit.
  *Migration:* none — the property never worked where it is now refused.
- **Breaking: `assert-rule` refuses a rule literal whose predicate is a variable.** Such a
  rule was indexed under `?var0`, which no arriving fact and no goal can spell, so it
  answered no backward goal at all and fired forward only when the concrete-predicate
  antecedent beside it arrived: two arrival orders, two answers, from a rule the engine
  reported as accepted. An `:inert` rule is exempt. *Migration:* assert the instantiated
  rules, one per predicate the metarule ranged over.


## 0.3.0 — 2026-08-04 — "a type on every refusal"

Correctness fixes across the durable index, the snapshot, the JTMS, the export dump
and the bounded prover, a sweep that gives every refusal a `:type`, the one wire
contract 0.2.0's own sweep left qualified, and the serialization both servers' storage
layer already assumed. Then a run of **inference and belief** work: two orders that
reached two answers, the two doors that disagreed about an inherited claim, and two
enumerations that grew with the vocabulary rather than with their own answer. Eight
entries are marked **Breaking** — they refuse input 0.2.0 accepted or change an
observable contract, which is why this is 0.3.0 and not 0.2.1; the rest are compatible.

- **Breaking: the daemon's refusal `:type` keywords are plain** — `:not-edn`,
  `:cross-origin`, `:bad-host`, `:body-too-large`, where the namespace serving them
  qualified each one. This finishes tree-wide what 0.2.0's own breaking entry claimed.
- **Breaking: both servers hold one request-body ceiling.** The cap and its
  `VAELII_MAX_BODY_BYTES` override (16 MiB) live in `vaelii.impl.guard`, which both
  read, so the browser answers **413** for an oversized form body where only the daemon
  did. A daemon read is also fully realized **inside** the write monitor — `wire-safe`'s
  walk is what realizes a lazy answer, so running it after the monitor released let a
  `:query` straddle a concurrent `:assert`.
- **Breaking: the browser serializes its writes.** Jetty serves the write routes on a
  thread pool, so two POSTs were two writers — where the storage layer is written on the
  promise that they are not. Interleave two and the WAL holds both frames while the RAM
  map holds one, so the running index and the one replayed on the next open disagree.
  The browser now takes one process-wide monitor around every content write, as the
  daemon always did; a concurrent write waits rather than racing.
- **Every `ex-info` the engine throws carries a `:type`.** Twenty refusals threw an
  untyped map, so a caller had to guess from which keys were present. Two forms that
  threw a raw Java exception now answer instead: `(genl ?x ?x)` / `(disjoint ?x ?x)`
  answer the question one variable in both positions asks.
- **Breaking: an `ist` form must have exactly three elements.** 0.2.0 read `assert` and
  `check` positionally, so `(ist Ctx S junk)` asserted with the extra silently ignored
  and `(ist Ctx)` raised a raw `IndexOutOfBoundsException`. Both refuse with `:shape`.
- **The durable index is gated on its key layout at open.** A log whose stamp does not
  match `kv/index-layout-version` is cleared, rebuilt from the records and restamped,
  `:recover?` notwithstanding; without the gate such a log replays cleanly and then
  misses every read whose key shape moved. **A 0.2.0 durable store carries no stamp, so
  its first open under 0.3.0 pays one automatic reindex**: O(records), logged at `:warn`,
  paid once. `docs/storage.md`.
- **Breaking: `open-kb` refuses a `:base` whose durable index is at an older key
  layout** (`:stale-index-layout`). The repair is a write and a base is mounted
  read-only, so the refusal names the one place the rebuild can happen: open that
  directory as a KB, then mount the fork over it.
- **Breaking: `(fork (fork base))` is refused** (`:stacked-fork`), which is what
  `docs/overlay.md` has always stated.
- **Breaking: `open-kb` refuses a `:recover?` setting it does not name.** `:auto` is the
  default, `true` an alias for it, `:warn` and `false` the rest; any other value read as
  the warn branch and handed back an empty TMS over a store that is not empty, which
  answers `[]` to everything. A stale derived index is dropped on open whatever
  `:recover?` says.
- **Breaking: `close!` releases a durable fork's own directory.** A fork's writable half
  takes the same exclusive lock as any durable KB, so without its own `:dir` it could
  never be handed to another process short of exiting the JVM. 0.2.0's docstring promised
  the opposite, so code that closed a fork in a `finally` and kept reading it worked and
  now does not.
- **A failed compaction takes its temporary files with it.** A rewrite that threw closed
  its handles and left `<log>.compact` behind, and the next compaction in the same
  session opened that temp and appended to it — its replay then put back records deleted
  in between. The cleanup is scoped to the pre-commit phase: past the marker the temps
  are the only complete copy.
- **A failed open gives back the directory lock with no handles still on it.**
  `open-kv-backend` and `open-token-log` replayed their logs outside any guard, so a torn
  frame propagated to a caller that answers a failed open by releasing the lock —
  leaving it released while this JVM still held an open handle.
- **A fork's merged `kv-entries` is realized under its monitor.** Both halves were lazy,
  so the seq handed back from inside the lock realized outside it. An export of a fork
  taken while anything wrote it projected two states at once.
- **The rete alpha registry is synchronized.** It is JVM-lifetime shared state reached
  from the store observer hooks, which fire on whichever thread is writing, and a
  `HashMap` racing its own rehash can leave a reader spinning on a probe loop that never
  terminates. Its check-then-put is one step too, so two callers cannot leave the loser's
  alpha permanently unmaintained.
- **`load-source` claims the catalog under one monitor.** The busy test, the
  already-loaded test and the registration were three separate reads, so two requests
  arriving together each passed all three and spawned a loader.
- **The browser reads untrusted EDN under `Throwable`, as the daemon does.** A deeply
  nested form overflows the reader's stack with a `StackOverflowError`, which an
  `Exception` catch lets escape — a 500 where an unreadable term is the ordinary answer.
- **The index snapshot's roots-fallback blob is validated like the sections beside it.**
  `roots-fallback.nippy` carries argument-root postings, which are primary index truth,
  and a missing or torn blob loaded as `[]` behind a warning while every argument-root
  read answered `#{}` out of a snapshot that opened clean. The meta records the blob's
  count and byte length, and the load thaws strictly.
- **The mapped index snapshot survives a JVM shutdown, and a failed save leaves the
  previous image intact.** The stamp is taken against the records before a byte moves,
  durability registrants close in phases, and every section lands in a `.tmp` until the
  swap. A failed *open* likewise gives back the handles it took.
- **An export dump carries every provenance stamp, and `export → import → export` is
  byte-stable.** The provenance walk covers justification handles as well as sentex ones,
  and import stores a justification's antecedents as a **vector**, the shape the engine's
  own write path stores.
- **The JTMS dedup index carries the identity of the TMS it mirrors.** A nested chain
  over a second KB — legal from an `:on-progress` callback, with overlapping handle
  spaces — could answer one KB's dedup question out of the other's supports. Keys coerce
  fixnum boxing to `Long` at the boundary, since the map compares with Java `equals`
  where the scan compares with `=`.
- **`prove-within` prepares its goal**, through the same `prepare-goal-for-read` every
  other read path takes, so a reifiable NAT or a merge-retired spelling is the same
  question under the bounded prover that it is under `ask`.
- **The rete forward matcher fans over predicate-`genl` sub-predicates at every arity**,
  as the reference `res/match-pattern` does. Fanning only for a two-element sentence gave
  the opt-in matcher a different belief set on any rule whose antecedent had another
  arity.
- **A firing refused at derive time comes back when its exception releases.**
  `place-conseq` does not place a firing whose `exceptWhen` exception already holds, and
  such a firing left no justification and nothing in `jtms/blocked` — so a settle pass
  could not see it and the conclusion stayed suppressed after the block lifted. The same
  knowledge in the other order concluded it. The refusal is recorded as `[rule handle,
  bindings]`, capped at 4096 entries per rule. `docs/exceptions.md`.
- **Five order-independence repairs.** `contradictions` names the same side of a clash
  whatever order the two arrived in; the two settle sweeps sharing one exposure-instance
  budget walk their moved region in content order; `query` with `{:proof? true
  :portfolio? true}` returns each answer once; `negation-nogoods` writes with a
  compare-and-set; and the node engine's inline join plans with the `:est-override`
  belonging to its registry leaf.
- **A forward rule fires on a claim argument-position preservation licenses**, so
  `sentexes-matching` and `ask` stop disagreeing about the same knowledge.
  `(argPreserving largerThan 1 genl)` beside `(largerThan dog cat)` licenses
  `(largerThan chihuahua maine_coon)`, which `ask` reached while the fixpoint fired only
  on the claims that were written — so the conclusion it never drew had no `why`, no
  retraction path and no way to be an antecedent. The join contributes the handles the
  inherited claim was read from, so retracting any of them withdraws the conclusion. One
  asymmetry is left: a justification confers the weakest class it rests on, so a
  `:monotonic` claim declared preserved by a `:default` declaration draws a `:default`
  conclusion. `docs/inherit.md`.
- **A head-existential rule carrying an aggregate mints a ground witness.**
  `skolem/frontier-vars` subtracts a post-join literal's output, so the Skolem NAT no
  longer takes a variable into its argument list.
- **An open `disjoint` goal is enumerated from the declarations rather than from the
  vocabulary.** A separation convicts two subtrees, so the answers are the subtypes of
  what a *visible* declaration names and the cost is the answer's own size; 0.2.0 asked
  `taxonomy/disjoint?` once per type, and once per **pair** with both arguments open. On
  4,000 types carrying one separation that is 15.4 ms to 0.13 ms with an argument bound —
  flat where it grew linearly — and at 1,000 types the two-variable goal goes from 2.5 s
  to 4 ms. `lein perf`'s `disjoint-enumeration` check is the claim.
- **A definitional clash is arbitrated from a context that can see both halves.** The
  checks are scoped to the context they are asked in, so a pair whose halves sit either
  side of a `genlCx` edge was answerable from exactly one of the two, and only when
  that half was the one the settle moved. `settle/clash-askers` runs the check from the
  candidate's own context and from the maximal common descendant of it and each context
  holding a sentex it could pair with; nothing is widened.
- **A pair per opposing sentex, not per opposing type.** One sentence stated in a general
  context and again in one that sees it is two sentexes, of possibly different strength,
  and a claim that denies it denies both — where the checks named one handle each, so the
  content-first of the two was weighed and the other left believed beside content that
  contradicts it.

## 0.2.0 — 2026-08-03 — "the public API boundary, drawn"

**Not a drop-in upgrade from 0.1.0.** Several of the changes below refuse input
0.1.0 accepted or change an observable contract — each such entry is marked
**Breaking** — which is why this is 0.2.0 and not 0.1.1. Entries between here and
the 0.1.0 header are in it, newest first.

- **The argument roots are scoped by predicate** (`[:argument-root pred pos
  term]`), so a materialising join reads one literal's postings rather than
  wading through every functor's at a shared slot. An `[:argument-slot pos
  term]` roster, reference-counted off those postings, keeps the
  predicate-agnostic reads answerable as a union over the predicates present.
  The packed long has no room for a fourth key part, so the dense roots route
  the family to their boxed fallback. `index-layout-version` is **2**: an index
  written by 0.1.0 reads as `:layout-changed` and is rebuilt on first open —
  no action needed, but a large durable store pays a reindex for it.
- **Breaking: every handle-taking fn refuses a non-handle** (`:bad-handle`) —
  the vector `assert` returns for a conjunctive rule included, which 0.1.0's
  `retract!` silently answered with `{:removed-sentexes 0}`. `nil` stays a
  question with an answer (`in?` false, `why` `{:stored? false}`,
  `add-provenance` a no-op), and `check-edit` reports what `edit!` throws. `why`
  also takes `{:max-depth n}` (default 256), marks a capped branch
  `{:truncated? true}` instead of overflowing, and refuses bad opts
  (`:unknown-option`).
- **`close!` releases a durable KB's directory** without waiting for JVM exit,
  and `import!` is `export!`'s inverse. An unclean close still releases the
  lock and registry; the first component failure is rethrown after.
- **An `argIsa` / `interArgIsa` / `argGenl` refusal names its convicting
  declaration in content order**, not in whichever order retrieval enumerated.
- **The five sweeps run in CI** — dense TMS, incremental matcher, node query
  engine, its tacticians, reference retrieval — each failing-set-identical
  with the default it replaces. Nothing ran them before.
- **Breaking: `assert` refuses a non-map `opts`** (`:unknown-option`) —
  `(assert kb s ctx :monotonic)` stored a defeasible sentence in 0.1.0.
  `check` already reported the same request; the two agree now.
- **Breaking: `open-kb` recovers by default** (`:recover? :auto`). The old
  `:warn` default handed back a KB that answered wrongly from a reopened
  store. The cost moves to construction — O(records) on a populated store —
  and `{:recover? false}` defers it. `:warn` and `false` remain.
- **The public surface is six namespaces**, where it was one: `vaelii.core`
  plus thin shims `vaelii.client`, `vaelii.starter`, `vaelii.web`,
  `vaelii.serve` and `vaelii.cli` over the `impl` namespaces they front. The
  boundary is now what the docs said it was.
- **Breaking: `vaelii.client`'s `assert` and `assert-rule` are spelled bare**,
  without the `!` 0.1.0 gave them. A `!` marks a fn that destroys stored
  knowledge and neither does — both are additive, and `retract!` is what takes
  one back — so the client now spells them exactly as `vaelii.core` does. A call
  site writing `c/assert!` or `c/assert-rule!` no longer resolves.
- **A clash names the sentex that states the membership**, not one that merely
  entails it, under either retrieval strategy.
- **An auto-compaction queued for a closed store is dropped**, so the next
  open no longer replays it as a crash-interrupted compaction.
- **Breaking: error `:type` keywords are plain across the tree**
  (`:unknown-source`, not `:vaelii.impl.catalog/unknown-source`), and
  `open-kb`'s backend refusals carry one. Swept in the same pass: the settle
  re-check queue no longer drops entries queued by a concurrent thread, and
  `foreign/register` refuses with `ex-info` rather than an elidable `{:pre}`.
- **Leiningen 2.10 is the minimum**: `:preserve-eval-meta` needs it, and 2.9
  ignores the key silently.
- **Breaking: `POST /op` requires `Content-Type: application/edn`.** The type
  is not CORS-simple, so a browser must preflight and the daemon answers no
  CORS headers — which closes cross-site request forgery against a loopback
  daemon. A client that sent no content-type is refused; add the header.
- **Breaking: a request body over 16 MiB is refused** (413) before it reaches
  the heap; `VAELII_MAX_BODY_BYTES` adjusts the cap.
- **Breaking: DNS rebinding is closed on both servers.** Every route requires
  a `Host` naming the interface the server was started on. A request with no
  `Host` still passes (a non-browser client carries no ambient browser
  context); a reverse proxy or local alias sets `VAELII_ALLOWED_HOSTS`.
- **`+with-foreign` names a coordinate that exists**
  (`com.vaelii/vaelii-foreign`); the bare id it carried resolved nothing.

## 0.1.0 — 2026-07-31 — "the first release"

The first release. What follows is the development log that produced it, newest
first; every entry below is in 0.1.0.

## 2026-07-30 — "declarations re-check what they change"

- A declaration re-checks the exceptions it moves: `(symmetric P)`,
  `(transitive P)`, `(inverse P Q)` and the `argPreserving` forms change what
  may be concluded with no fact arriving; `(functional P)` sweeps the extent
  when it lands.
- An equality restates a fact for each reader rather than once for the KB, and
  is itself a re-check trigger for `exceptWhen`, `unknown` and census reads.
- A change feed: the region a settle already computes is handed to a listener
  instead of discarded.
- English in — a sentence read into candidates a person still has to accept.
- A qualitative relation two contexts entail together fires a forward
  rule; a believed negative reaches the wiring a positive does; "some context"
  means the union of what the readers answer.
- Three readers of one question agree over a cyclic hierarchy, and settle
  repairs the context ranking after reconciling belief as well as before it.

## 2026-07-29 — "one entry point for backward chaining"

- One front door for backward chaining: the four paths measured, then
  consolidated to two chainers behind one entry point with one dial. A proof
  of an ephemeral answer reads the way `why` does.
- The goal frontier's order is a policy measured on time-to-first-answer,
  `:ground-first` by default; the goal-stack chainer drives one solution at a
  time and level 7 streams its search.
- Foreign formats arrive as a classpath plugin, so a reader ships and retires
  without touching the engine.
- A constraint declaration may name a second sentex it must not weigh, and a
  depth bound has no default because there is no defensible one.

## 2026-07-28 — "the gate: lint, suite, and scaling"

- `lein gate`: lint, the suite, and the scaling claims, measured and failed on
  rather than asserted; five checks added for costs that grow with what they
  must not.
- The columnar index is written once and mapped back; backend names read
  `<records>-<index>`, all seven.
- A literal's matches are remembered and retired on a clock; converging
  branches share one rule expansion; a third backward chainer whose state is
  a frontier.
- The naming invariants belong to the knowledge base, and the bulk door counts
  what it skips.

## 2026-07-27 — "aggregation over query results"

- Aggregation: a count is a query operator, and a firing that rests on one is
  maintained like any other — gated by a permutation test. A census counts
  distinctness through the representative the asking context elects.
- `argIsa` entails as well as constrains, behind a toggle, retroactively too.
- A definitional clash names a second sentex, making it a nogood, and the
  arbitrating sweep asks the taxonomy rather than a fixed functor set.
- The qualitative network lives on the knowledge base and warm-starts off its
  own previous answer; a violation ledger is a claim about one KB.
- The browser draws term shapes, composes English at three densities, and
  gained `lein browser`; OpenCyc loading went from 378s to 277s.

## 2026-07-26 — "reads scoped to the asking context"

- Contexts got a vantage: every taxonomy supporter records the context it
  asserts from, so disjointness, matching fan-out and settle all read only
  what the asking context can see.
- A firing names the `genl` edges it subsumed through — belief and strength
  run through them like any antecedent, checked against all 24 orderings.
- Records and index became two independent choices, plus an overlay backend:
  a private writable fork over a shared read-only base.
- A knowledge base is readable before it finishes loading, and the suite runs
  on every backend from one script.

## 2026-07-25 — "OpenCyc in the engine's own format"

- OpenCyc, read and re-expressed: every constant given back its role, 1.1M
  sentexes in the engine's own format, on the machine that reads it. Nothing
  of Cycorp's is redistributed.
- An export format no rename can break, with `xz`, an importer, and an oracle
  comparing two knowledge bases; a dump lands every record at its handle.
- Qualitative spatial and temporal reasoning: RCC-8 and three more spatial
  algebras, Allen intervals, durations and instants, behind one glue.
- One gap written in two units is one constraint: both spellings snap to the
  tolerance grid, and a unit given two conversion factors is its own base.
- A knowledge-base catalog with a browser that switches between KBs;
  `inherit` declared rather than assumed; definitional checks reach every
  term; `argGenl` constrains one level up.

## 2026-07-24 — "denser storage, measured first"

- The scale program opened with measurement first: the truth-maintenance
  wall, a posting-encoding bake-off on a real corpus, and a rule audit.
- Three dense representations, each measured: `:memory-dense` integer
  postings, the `:memory-columnar` int-token trie with CSR compaction (3.18x
  whole-index), and a bitmapped TMS behind a protocol.
- The disk side got dense too: positional record reads with a hot-record LRU,
  a positional frame codec, tokenized bodies over a durable dictionary — all
  behind a backend parity gate.
- Recursive forward chaining went O(n³) → O(n log n); a term roster
  enumerates vocabulary in O(terms).
- The web browser was hardened — escape by default, guard the parse, bind
  loopback, refuse cross-origin writes — and a pluggable LLM proposes edits
  and never applies them.

## 2026-07-23 — "performance fixes, and an operational surface"

- A performance review, its findings fixed: the disk log records operations
  rather than grown values (killing an O(N²) write amplification), settle
  keeps a coincidence set, re-checks narrow to the moved cone, region
  fixpoints became semi-naive worklists, compaction is copy-on-write.
- Symbolic equational reasoning: pure oriented rewriting with full
  Knuth-Bendix orientation, order-independent normalization, and
  non-confluence surfaced; `rewriteOf` extended over predicates and types.
- An operational surface: an EDN-over-HTTP daemon, a command-line driver, a
  thin client, and a browser that attaches to a daemon — with the public API
  closing every hole the browser tracked.
- Existential rule heads with deterministic skolemization; an occurs check;
  closures answered on demand; the record split into atomic and rule shapes
  with interned symbols; a bulk-load fast path.

## 2026-07-22 — "sound negation as failure"

- Negation as failure, at top level and in antecedents, with block, sweep and
  revive, and stratification to keep it sound.
- Resource-bounded anytime inference with qualitative cost tiers and a
  cost-ordered forward-chain join; `ask-within` normalizes its goal.
- Reification of non-atomic terms; structural subterm indexing,
  oracle-proven, then on by default.
- The storage seam: index logic onto one key-value protocol, an in-memory
  backend, then the on-disk substrate — files, lock, durability, record
  store, index store.
- The index benchmark harness, and a per-handle provenance side map.

## 2026-07-21 — "equality lands, and a sudoku solved"

- `exceptWhen` canonicalized into the record, blocking excepted conclusions
  with only reachable firings re-checked; its query reified the way a fact
  is.
- Equality landed: the closure, the `different` prover, a specification
  suite, and wiring into assert; stratification is checked on edge change.
- The engine split out of one namespace into five, and the knowledge base
  restructured into a layered tree loaded on start.
- `assumptionRules` with persistent solve and labeling contexts, proven on a
  sudoku.
- Retrieval got sharper: argument roots, multi-column narrowing, predicate
  subsumption, set-algebra retrieval, an opt-in incremental matcher.
- Truth-maintenance mutations are atomic; lint arrived.

## 2026-07-20 — "order independence, made an invariant"

- Canonical rule form — canonical variables with a varmap, literal order,
  comparison direction — so rules alike up to renaming share one handle.
- The eight-level lookup-to-query stack, lazy throughout, with a browser page
  showing which level answered.
- Order independence and locality pinned as invariants: region-local
  relabelling, belief-following closures, content-keyed tie-breaks.
- The answer-set layer wired to the edge-solver seam, with a labeling
  materialized as a context; the defeasible layer made sound, six bugs
  pinned as failing tests first; `exceptWhen` began as a failing suite.
- Everything but `core` moved under `vaelii.impl.*`; `!` reserved for
  irreversible operations; tests became net-neutral, and a second concurrent
  run fails fast rather than corrupting the first.

## 2026-07-19 — "the whole stack, day one"

The first day: a contextualized common-sense knowledge base with a trie
index, inference and truth maintenance.

- Sentexes — a sentence plus the context it holds in — stored as records
  behind protocols with nippy serialization; rules are sentexes too, with
  built-in transitivity for types and contexts.
- Forward chaining with dependency-directed retraction, and a backward
  chainer; a non-monotonic TMS with strengths, soft prioritized
  contradictions, and a solver seam.
- An inverted term index, directed rules, disjointness, well-formedness
  checks, and a pluggable prover query engine; structural connectives
  canonicalize into the record; evaluable arithmetic.
- A web browser over the whole thing, over a starter ontology with every
  term documented.

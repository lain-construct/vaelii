# Bounded KB integrity

- **Covers:** `kb-integrity` — one read-only checkpoint report for the complete visible
  `predAllSpecified` / `predSpecifiedAll` population, query-only definition clashes
  over a caller-owned finite set of ground candidate terms, the predicate `genl`
  edges that widen a declared argument type, the candidate types with no `genl`
  path to `thing`, and the `genl` edges a cover forces on a candidate type that the
  closure does not hold.
- **Not here:** repairing findings, enumerating a domain, vocabulary completeness,
  generic constraint auditing, or the represented settled dilemmas returned by
  `contradictions`; how definitions infer membership → [defns.md](defns.md); what a
  specified declaration requires → [predall.md](predall.md); how an `arg` declaration
  descends a predicate `genl` edge → [argtypes.md](argtypes.md); what a cover
  declares → [taxonomy.md](taxonomy.md#covering-a-whole-and-the-parts-named-against-it); general
  knowledge-quality census readings → [quality.md](quality.md).
- **Assumes:** sentex, context, ground term, `genl` → [glossary.md](glossary.md).

## The call

```clojure
(v/kb-integrity kb #{-212 0 212} 'CxUniverse)
;; => {:status :audited :candidate-count 3}

(v/kb-integrity kb candidates 'CxUniverse
                {:max-work 10000 :max-ms 1000 :max-results 100})
;; => {:status :truncated :reason :max-work :candidate-count 500
;;     :work 10000 :elapsed-ms 37.2 ...partial finding categories...}
```

The candidate argument must be a set, and every member must be ground. This is the cost
and meaning boundary: a caller names the known terms worth checking; the query engine
never turns the audit into an open term enumerator. Collections need not be repeated.
The sweep derives its finite collection population from visible `defnSufficient`
declarations and their `genl` ancestors, exactly the population the positive definition
prover can reach.

The optional budget has three independent bounds. `:max-work` meters direct audit rows,
prover dispatches, and prover results, so a one-term candidate set cannot hide the cost
of an aggregate condition over a large KB extent. `:max-ms` is a cooperative wall clock,
checked at the same boundaries and inside the argument-preservation prover's claim walk
([anytime.md](anytime.md)). `:max-results` caps findings. A `nil` bound is no bound.
Reaching any bound returns `:status :truncated` with a reason and never labels a partial
sweep `:audited`. The daemon fills all three when the map is absent, clamps callers to
its ceilings, and refuses an over-ceiling request by type before acquiring the
operation's work.

Work and time are cooperative, not preemptive hard ceilings. The sweep checks immediately
before and after every prover selection/dispatch callback and every result-stream pull.
An opaque callback—or a chunked lazy stream that computes several answers in one pull—may
overrun until it returns; the following checkpoint then truncates before another callback
or pull begins. The `Prover` protocol does not require a prover to yield one answer per
pull. `:max-results` is different: it is an absolute bound on findings returned,
including snapshots truncated for work or time.

The definition pass performs one unavoidable open census of visible `defnSufficient`
declarations because callers intentionally supply terms, not collection names. It then
validates one collection and one ground candidate at a time. The specified pass likewise
uses small declaration censuses only to identify its finite worklist, then audits each
declared predicate independently. The widening pass does the same: one census of visible
`arg` declarations, then one direct `genl` edge at a time. The `thing` pass reads no
census: it checks one candidate term at a time. The implicit-`genl` pass reads none
either: one candidate term, then one visible cover over it, at a time. These focused units are where
cooperative checkpoints and partial-result preservation sit.

`:categories`, a set of category keys, runs the passes of those categories alone and
reads nothing for the others. On a large KB the census passes (the specified and widening
categories) can spend the daemon's `:max-work` ceiling before a candidate pass starts; a
caller names the candidate categories to reach them.

An explicit `nil` options value means the same thing as omitting the options arity,
in-process and through the generated daemon clients. The daemon still supplies its own
ceilings before dispatching either spelling.

A finding changes the top-level status and adds only the populated categories:

```clojure
{:status :gap
 :candidate-count 1
 :definition-inconsistencies
 [{:collection widget
   :term 7
   :passing-sufficient
   [{:defined-collection widget :condition (qualifies ?x)}]
   :failing-necessary
   [{:defined-collection widget :condition (required ?x)}]}]
 :all-specified-violations
 {[predAllSpecified hasPet person]
  {:status :audited :violations #{Bob}}}}
```

`:status :audited` means all five passes ran and none found a gap. `:status :gap` cannot
be confused with that clean shape even when only one sparse category is present. The
specified category is exactly `all-specified-violations`, including its typed declaration
gaps; it is composed, not reimplemented.

## What a definition finding means

The definition prover treats a passing own-or-spec `defnSufficient` as a positive
membership witness. A failing own `defnNecessary` is simultaneously a negative witness.
When no strict-genl necessary fast-fails the positive path, the collection can therefore
answer both `(Coll term)` and `(not (Coll term))`. The report preserves every passing and
failing declaration as evidence, including the collection on which an inherited
sufficient was declared.

A definition finding is not one `contradictions` reports. `contradictions` reports
settled, represented default dilemmas already present in the truth-maintenance state. A computed
definition condition is evaluated only when queried, so its latent clash has no stored
pair for `contradictions` to enumerate. `kb-integrity` asks the bounded definition
question without changing the meaning or cost of the existing reader.

The sweep stores and files nothing. Aggregate diagnostics raised only because a
definition condition was evaluated are redirected to an audit-local sink, preserving
the condition's truth without changing the live violations ledger or logs. It identifies
gaps; remediation remains a separate, explicit write.

## What a widening finding means

`(genl P Q)` between predicates says every `P` tuple is a `Q` tuple, so `Q`'s `arg`
declarations constrain `P`'s tuples too ([argtypes.md](argtypes.md)). When `P` declares
its own type at a position and `Q` demands one that type is not subsumed by, the edge
does not say what its author meant: `(arg parentOf 1 animal)` under
`(genl parentOf originatorOf)` with `(arg originatorOf 1 person)` makes every animal
parentage an `originatorOf` tuple, which only persons may fill.

Nothing on the write path reports this as a defect of the edge. Depending on the
contexts the declarations sit in and on arrival order, `(parentOf Fido Rex)` over two
dogs is refused `:arg-type`, or is admitted with `(person Fido)` minted onto it. Neither
outcome files a violation or a contradiction naming the edge. So the sweep reads the
declarations instead of any fact:

```clojure
{:status :gap
 :candidate-count 0
 :genl-arg-widening
 [{:spec parentOf :genl originatorOf :arg 1 :spec-type animal :genl-type person}
  {:spec parentOf :genl originatorOf :arg 2 :spec-type animal :genl-type person}]}
```

One finding is reported for each spec type at each position that no demanded type
subsumes. Subsumption is the reflexive `genl` closure read from the audit context. A
spec type that *is* subsumed (`fatherOf` declares `person` under `parentOf`'s `animal`)
is compatible, and so is an identical type. A spec position that holds several declared
types is their intersection, so it is compatible as soon as one of them is subsumed.
`:genl-type-declared-on` is present when the demanded type is declared above `Q`, on a
super-predicate the constraint inherits through `res/constraining-predicates`, the same
closure `assert`'s argument check reads.

The pass has these limits:

- **Declaration census, not candidate terms.** A widening is a fact about two
  predicates' declarations, not about any individual, so the caller's candidate set does
  not bound it. The pass reads every visible `arg` declaration once to find the
  predicates that declare their own types (a few hundred on the shipped load), then each
  such predicate's direct visible `genl` edges. Edges out of a predicate that declares
  nothing of its own are skipped, because such a predicate has no declared domain for an
  edge to widen. A multi-step chain is still covered: the demanded types come from the
  whole closure above the direct genl.
- **`arg` only.** `genlArg` bounds a position one level up (a subtype, not a member),
  `quotedArg` types a mention, and `interArg` and the covering forms (`args`,
  `argAndRest`, …) relate positions rather than typing one. Comparing any of them
  against an `arg` type would compare different levels, so none is read here.
- **`genl` only.** `genlInverse` and other relation-to-relation forms are not read.
- **Visible from the audit context.** An edge or declaration asserted in a context the
  audit context cannot see contributes nothing, as for every other read.

Each declaration row, edge and position comparison spends one work unit, and
`:max-results` counts these findings after the definition and specified categories, in
that order.

## What a not-under-thing finding means

Every type is a specialization of `thing`. Nothing on the write path reports a term
declared `(unary_predicate X)` with no `genl` path to `thing`: no violation or
contradiction names the term. So the sweep reads the declaration and the taxonomy for
each candidate:

```clojure
{:status :gap
 :candidate-count 1
 :not-under-thing
 [{:term orphan_kind}]}
```

One finding is reported for each candidate term, in print order. The path is the
transitive `genl` closure read from the audit context, so `(genl nested_kind placed_kind)`
with `(genl placed_kind thing)` places `nested_kind` under `thing`.

The pass has these limits:

- **Candidate terms, not a census.** The caller's candidate set bounds the pass, as it
  bounds the definition pass. A type declared `unary_predicate` but absent from the set
  is not read, so the pass never enumerates the KB's types. A candidate that is not a
  ground symbol (a number, a string, a compound) cannot be a type and is skipped.
- **`unary_predicate` only.** A binary or wider predicate is not a type, so a predicate
  `genl` edge between two binary predicates is not a finding however its chain ends.
- **`thing` is the root.** `thing` itself is never a finding.
- **Visible from the audit context.** A `unary_predicate` declaration or a `genl` edge
  asserted in a context the audit context cannot see contributes nothing, so a type whose
  only edge to `thing` is asserted below the audit context is a finding there.

Reading the declaration and testing the `genl` path each spend one work unit, and
`:max-results` counts these findings last, after the widening category.

## What an implicit-genl finding means

A cover places individuals: an instance of the whole denied every part but one is an
instance of the remaining part
([taxonomy.md](taxonomy.md#the-coverage-inference-is-gated-on-explicit-negation)). The
same argument holds of a type, and nothing on the write path applies it there. A type
under the whole that is disjoint from every part but one has all its instances in that
part, so `(genl X P)` is true, but no sentence states it and the `genl` closure does not
derive it. The sweep suggests each such edge, with the cover that forces it and, for each
other part, the declarations that separate the type from it:

```clojure
;; (partition thing tangible intangible)
;; (partition thing temporal atemporal)
;; (genl tangible temporal)
;; (genl abstract_kind atemporal)
{:status :gap
 :candidate-count 1
 :implicit-genl
 [{:term abstract_kind
   :genl intangible
   :cover [(partition thing intangible tangible)]
   :disjoint-from [{:part tangible
                    :grounds [(partition thing atemporal temporal)]}]}]}
```

`abstract_kind` is separated from `tangible` by the second partition, which holds a
supertype of each, so every `abstract_kind` is `intangible`. The finding is a
suggestion: the sweep asserts nothing, and the edge is the author's to state.

One finding is reported for each candidate term and cover that force an edge, in print
order of the term and then of the cover. The separation is `disjoint?`, so an explicit
`disjoint` pair, a shared `disjoint_metatype`, a `sibling_disjoint` parent and a
separating cover all count, each inherited down the `genl` closure; `:grounds` names the
believed declarations it rests on.

The pass has these limits:

- **Candidate terms, not a census.** The caller's candidate set bounds the pass, as it
  bounds the `thing` pass. A candidate is read as a type when it is declared with arity
  one, or, with no arity visible, when it is the subtype of a visible `genl` edge; an
  individual and a relation of two or more places are skipped.
- **Covers over a supertype or over `thing`.** Every visible `covering` or `partition`
  over a supertype of the term is read, and every one over `thing` even when the term
  has no `genl` path to `thing` yet. A `separating` roster claims no coverage and forces
  nothing, though it may separate the term from a part.
- **Exactly one part left.** A term separated from every part is empty and is forced
  under none; a term left two parts or more is forced under none. A part, or the whole
  itself, is never a finding.
- **Only edges the closure misses.** A `genl` already stated, or derived through the
  closure, is not a finding.
- **Visible from the audit context.** The cover, the separating declarations and the
  `genl` edges are those the audit context sees.

Reading the term's arity and edges, each cover and each part's disjointness test spend
one work unit, and `:max-results` counts these findings last, after the `thing` category.

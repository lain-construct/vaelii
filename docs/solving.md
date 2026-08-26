# Solving: assumptionRule and persistent, inert labeling contexts

- **Covers:** how `assumptionRule` and constraint declarations become `do/label`'s
  persistent, inert labeling contexts, without touching base belief.
- **Not here:** the ASPIF encoding and solver backends the resulting program runs on →
  [asp.md](asp.md); committing one labeling live into base belief →
  [labeling.md](labeling.md).
- **Assumes:** sentex, context, premise → [glossary.md](glossary.md).

How a solve is expressed, run, and **kept** — as sentexes in the records, not an
in-memory snapshot — and why the base KB is never disturbed.

## Opt-in, persistent, inert

The KB's job is to be **always available with almost everything true**, and to do
**everything incrementally** — no operation scans the whole KB. So belief carries no
forced/supportable/excluded axis: `settle` solves nothing, and a classification exists
only where a caller asked for one.

A solve is an **opt-in, persistent, inert artifact**. Choices are declared with
`assumptionRules`; a solve grounds them and then either enumerates every optimal answer
set, writing **each one as its own context** whose truth values are ordinary sentexes in
the records, or returns a single answer set and writes nothing. What it does write
persists and is inspectable; the base KB is untouched either way.

## `assumptionRule` — a choice, not a truth

```clojure
(set/assumptionRule (implies <body> <head>))
```

A choice rule (`{head} :- body` in ASP): when `body` is derivable, `head` is an atom a
solve may set true or false. It is a virtual wrapper like `set/defaultRule` / `exceptWhen`,
canonicalized into the `RuleSentex` record's **`:assumption`** field and, being part of the
rule's identity, into the **trie key** — a choice rule and its bare twin are different
sentexes.

`:assumption` is a *firing mode*, **not** a strength class (`strength.clj` keeps its two
classes; there is no third). `forward-sentex?` / `backward-sentex?` return false for a
choice rule, so it **never chains into belief** — asserting `(candidate Item)` does not
derive `(color Item red)`. A solve is the only thing that consults it.

**This is where a disjunctive conclusion lands.** `(implies <body> (or C1 C2))` is
refused at the assert door, and the refusal points here: a disjunctive head says one of
two things holds without saying which, and belief is a label on a stored sentex rather
than on a set of them, so forward chaining has nothing to place. What it *is* is a
choice, and a choice has a home — one `set/assumptionRule` per alternative, plus a
`set/hardConstraint` over the combinations that cannot stand together, read back as an
answer set. (A rule **antecedent** that disjoins is a different question with a different
answer: it is polycanonicalized into one rule per alternative and never reaches a solve
at all — [canonicalization.md](canonicalization.md).)

## `hardConstraint` / `softConstraint` — a nogood over the choices

```clojure
(set/hardConstraint (implies <body> <marker>))
(set/softConstraint (implies <body> <marker>))
```

A constraint rule's head is a **contradiction marker**, not a truth, and its body is a
conjunctive nogood mixing background facts with choice-head patterns. Like
`assumptionRule` it is a virtual wrapper canonicalized into the `RuleSentex` record — into
**`:constraint`**, as `:hard` or `:soft` — and, being part of the rule's identity, into
the trie key: `sentex/key-tokens` gives every rule a constant `:constraint` slot, so a
hard constraint, its soft twin and its bare twin are three sentexes. `rules/constraint-of`
reads the class back off the record, `rules/constraint?` the bare fact of one.

It chains in neither direction (`forward-sentex?` / `backward-sentex?` are false for it),
so the marker is never derived: asserting everything its body names concludes nothing. A
solve is the only reader.

**Grounding it is a join.** Every constraint rule visible from the solve's base — the
same `genlCx` up-closure that scopes the `assumptionRules` — has its body split by
predicate: a literal whose predicate names a ground choice head is a **choice literal**,
everything else is a **background** fact. The background literals are proved together
through the ordinary conjunctive prover (`prove` in the base, belief-filtered and
cost-planned); each solution is then extended across the choice literals against an index
of the ground heads. Every satisfying binding yields one nogood over the choice-head ids
it used, with the substituted head riding along as that nogood's description. A negated
choice literal `(not <choice>)` carries through as a head required *absent*, so a body of
nothing but those is an at-least-one. Negated *background* literals are outside the
contract.

```clojure
;; no edge may have the same colour at both ends — two different individuals, which
;; the direct-clash detectors (always one shared individual) cannot express
(assert kb '(set/hardConstraint
             (implies (and (edge ?x ?y) (color ?x ?k) (color ?y ?k))
                      (monochrome ?x ?y)))
        'CxUniverse)
```

**A negated choice literal is joined like a positive one**, against the same index and
after them, so it may be partially ground and its own variables count as bindings:

```clojure
;; every pick must be taken — one nogood per ground (pick c), each forbidding that
;; head's absence.  `?c` is bound by nothing but this literal, and that is enough.
(assert kb '(set/hardConstraint (implies (not (pick ?c)) (mustPick ?c))) 'CxUniverse)
```

A negated literal matching *no* head drops its binding rather than constraining
anything, and that is the right answer either way: an atom that does not exist is
absent in every model, so it can never be false-*together* with the rest and the
requirement it guards is vacuous for that binding.

**Hard and soft differ at the encoding** ([asp.md](asp.md)). A hard nogood renders as an
ASPIF integrity constraint — no violation atom, no minimize term — so a model whose whole
signed body holds is excluded outright. A soft one takes the weak-constraint path the
auto-detected clashes take: a violation atom and a minimize term, so violating it costs
rather than excludes. An adjacency clash is not tradeable, which is what makes `:hard` the
class a colouring wants — and a program whose hard constraints already pin what must be
chosen is the one `:sat` below is for.

## The inert-fact primitive

`core/assert-inert` stores and indexes a sentex but **skips the belief step**
(`add-premise` / `mark-premise`). The sentex lives in the record store and in the index
(trie, `[:context-root ctx]` root, term index), is inspectable via `sentexes-in-context`, and survives
`recover` — but it is **not a JTMS premise**, so it is never IN.

This is what makes labelings coexist, and it needs no ATMS. Every belief-filtered read —
`sentexes-matching`, `in?`, and the `settle` nogood scan (`negation-nogoods`) — sees only IN
sentexes. So an inert `(not head)` sitting in a context that sees a believed `head` forms
**no** nogood and moves **no** belief. Coexistence falls out of *not premising*.

```clojure
(assert-inert kb '(color Item red) 'CxRedWorld)   ; stored, inspectable, never IN
```

**A rule is refused here** (`:not-indexable`), and the reason is that this door does not
index one. A rule fires because `index-rule-sentex` posted its predicates, which happens
where a rule sentex is *created* — the assert door's new branch, and the generator mint —
so a rule stored inert would be unreachable by either chainer, and would stay unreachable
after somebody asserted it, that assert resolving to the stored sentex and taking the
branch that does not index. What it left was a rule `in?` called believed and no fact
ever fired. A labeling labels atoms and their negations, so nothing this primitive exists
for wants one.

The **other** inertness is a rule's own: `set/inertRule` is believed, indexed and
browsable and chains in neither direction — a rule kept as documentation
([inference.md](inference.md)). One word, two states, and the distinction is whether the
KB believes what it stored.

## `(do/label Base Into [mode])`

Grounds the `assumptionRules` visible from `Base`, constrains the ground heads, solves,
and — under `:all` — materializes **one inert labeling context per optimal answer set**.
The optional third argument is the mode: `:all` (the default), `:one` or `:sat`, and
anything else is refused as `:not-assertible`.

1. **Ground** — each assumptionRule's antecedents are proved over the facts believed in
   `Base` (a scoped, belief-filtered join — not a whole-KB scan), its head substituted
   per solution. A rule's `exceptWhen` guard is honored per binding, evaluated in `Base`
   — grounding is a fourth consumer of a rule's firing beside the three chainers, and a
   choice the exception holds of is not offered. That is how a candidate menu is
   filtered declaratively ("any cell may take any value, except one already ruled
   out"). The grounding stays **in memory**: the Program keys the heads by
   program-local ids — never KB handles — and the menu comes back as `:choices` in
   the result. Nothing about it is stored. A grounding is derived solver working
   state, recomputable from the assumptionRules and the base's believed facts; a
   persisted copy would carry no justification linking it to what produced it, and
   would rot silently the moment the base moved.
2. **Constrain** — clashes among the direct heads become nogoods: a `(not X)`/`X` pair, a
   `functional` predicate given two values, a `disjoint` type clash. Each constraint rule
   visible from `Base` is ground into nogoods over the heads its body names as well —
   hard ones as integrity constraints, soft ones minimized like these.
3. **Solve** — under `:all`, the `:all-optima` solver mode over the tiebreak-off encoding
   (`edge/enumerate-optima`) returns every optimal answer set as a distinct set of
   chosen-true heads; under `:one` / `:sat` a single `:label` solve returns one. The
   tiebreak is off in every mode: singling out one of several equally valid answers is
   not what a solve is for, and the content-keyed program is order-independent without
   it.
4. **Materialize** (`:all` only) — per answer set, a `genlCx` child `Into1`,
   `Into2`, … of `Base` holding `(head)` for a chosen-true head, `(not head)` for a
   chosen-false one, and an inert `(labelingOf <ctx> <Into> <i>)` **ownership marker**.
   A choice head must be a **positive** literal for this round-trip to hold: `(not
   head)` marks a chosen-*false* positive head, so a head that were itself `(not X)`
   would read back as its positive core with the polarity flipped. Grounding refuses a
   negated head (`:choice-head-not-positive`) before any world is written.

The numbered names are for humans; **ownership is recorded in the marker, never
inferred from a name**. Rediscovery (`do/classify`, and the replace sweep below) reads
the markers back through the term index, so a user context that happens to be named
`<Into><i>` is neither aggregated nor swept — and materialization skips any
numbered slot an unrelated context already occupies, so it is never written into
either. Two belt-and-braces guards back this: the sweep refuses to touch a context
holding any *believed* sentex (everything a solve writes is inert by construction),
and `retract!` tears an inert sentex down directly. And the sweep takes a context's
own **extent**, plus — for a marked labeling context only — the one `(genlCx <ctx>
<Base>)` edge that placed it under *this run's* base, matched whole rather than by its
functor: a sentex *about* a solve context asserted from elsewhere (an edge a user hung
under `<Into>Class` or under a context of their own, a claim naming `<Into>1`) is that
user's and survives. Hanging a labeling under contexts of one's own is the ordinary way
to read a solved world beside other knowledge, and a functor-wide sweep would delete
those edges on the next run.

**Replace-on-rerun, under `:all`** (the other two modes write nothing to replace).
Re-running `do/label` with the same `Into` clears the previous run's artifacts before
writing the new ones: every marked labeling context — its truth values, its marker, *and*
its placement edge under the base, so a surplus stale context (a run that shrank from
three labelings to two) drops out of the hierarchy and `do/classify`
cannot sweep it back in — plus the classification. So a solve converges instead of
accreting; without the sweep, two groundings' truth values would union into one
context, and an inert `(head)` beside an inert `(not head)` asserts nothing at all. A
run that grounds *no* choices clears too — "no labelings" is its honest result. The
one exception is `:no-backend`: nothing was computed, so the previous artifact is left
standing.

**A run that cannot replace what is there refuses**, with `:labeling-run-blocked`, and
refuses before the solve rather than after it. Two things stop the sweep, and
proceeding past either is worse than not running at all:

- **A labeling context somebody has asserted believed content into.** The sweep
  declines to touch it — that is the guard above, and it is right — but the old marker
  then survives beside the new run's, and `do/classify` aggregates two groundings into
  one classification.
- **A labeling whose `labelingOf` marker has been retracted.** The marker is an
  ordinary sentex, and rediscovery is the only way the sweep finds a context, so losing
  one hides that context from the sweep forever while its `genlCx` edge goes on holding
  it in the hierarchy — a believed monotonic edge nothing will ever retract, and one
  more leaked slot on every re-run. It is recognized instead by what a marker-less
  artifact still is: a slot name, a non-empty extent with nothing believed in it, and
  this run's own placement edge under `Base`.

Believed content is what distinguishes a user's context from a lost artifact, and it is
decisive in both directions: a context of one's own that occupies a slot — even one hung
under this very base — is neither swept nor refused over. The refusal names what is in
the way; retracting that context's extent, or naming a different `Into`, clears it.
`(do/label _ _ :one)` and `:sat` are unaffected, having nothing to replace.

```clojure
(assert kb '(set/assumptionRule (implies (candidate ?c) (color ?c red))) 'CxUniverse)
(assert kb '(set/assumptionRule (implies (candidate ?c) (color ?c blue))) 'CxUniverse)
(assert kb '(functional color) 'CxUniverse)
(assert kb '(candidate Item) 'CxUniverse)

(assert kb '(do/label CxUniverse CxPlan) 'CxUniverse)
;; => CxPlan1: (color Item red)  (not (color Item blue))
;;    CxPlan2: (color Item blue) (not (color Item red))
;; base belief unchanged; contradictions 0; both worlds coexist
```

### The three modes

* **`:all`** (the default) enumerates every optimal answer set and materializes each, so
  the worlds coexist and persist for `do/classify` to aggregate. This is the mode for
  studying the whole space, and enumeration is infeasible where the optima are
  astronomically many — a large graph colouring has more proper colourings than can be
  listed.
* **`:one`** takes one optimal answer set from a single solve, minimizing defeated
  assumptions (keep as much belief as possible), and returns it **persisting nothing**.
  This is the mode for wanting an answer rather than an artifact, and it stays feasible
  at scale: one solve, no enumeration, no materialization. `Into` is accepted for a
  uniform imperative shape and unused.
* **`:sat`** is `:one` without the keep-belief objective — plain satisfaction, so clingo
  stops at the first model instead of proving cost-optimality over the choice atoms.
  Where the hard constraints already pin what must be chosen, "keep as much as possible"
  adds nothing and the optimization is a scaling wall.

The result is `{:base :into :choices [..] :labelings [{:context :true [..] :false [..]}]
:count n}`, with `:context` nil under `:one` / `:sat`, phase timings (`:ground-ms`,
`:translate-ms`, `:solve-ms`) for a profiling caller, and `:count 0` plus a `:reason`
when there is no labeling to report: `:no-choices` (nothing was ground), `:no-backend`
(nothing could be solved), or `:unsatisfiable`.

**`:unsatisfiable` is the answer when the hard constraints admit no model.** A hard
at-least-one over choices every other hard constraint forbids has no solution, and
"none" is what a solve of it reports. It matters most under `:one` / `:sat`, where a
single answer set comes back: an infeasible program keeps nothing, and *keeping
nothing* is indistinguishable in shape from the one perfectly ordinary world in which
every choice happened to be false — which for such a program is a world its own
constraints exclude. So the count is 0 and the reason says why, rather than one
labeling being reported that no model backs. Under `:all` the same program enumerates
nothing and reports `:count 0` on its own.

## `(do/classify Into)`

Gathers brave/cautious over the labelings a prior `do/label` produced — a pure
aggregation over the persisted contexts, no solver, no whole-KB scan, and one extent
read per labeling (each is loaded once into an in-memory polarity table). A choice
head is:

* **forced** — `(head)` in every labeling (a cautious / skeptical consequence);
* **excluded** — `(not head)` in every labeling;
* **supportable** — otherwise (a brave / credulous consequence only).

The result is written as inert sentexes `(forced H)` / `(supportable H)` / `(excluded H)`
in `<Into>Class`, for inspection — replacing its own previous output, the same
replace-on-rerun discipline `do/label` applies to the labelings.

```clojure
(assert kb '(do/classify CxPlan) 'CxUniverse)
;; CxPlanClass: (supportable (color Item red)) (supportable (color Item blue))
```

## Inspecting a solve

Everything a solve produces is an ordinary sentex in a context, so it is read the way any
context is: `sentexes-in-context`, the term index (`find-sentexes`), and the web browser.
The truth values are **inert**, so `sentexes-matching` / `ask` (belief-filtered) will *not* return
them — read the context's extent, not its belief. Retracting a labeling's sentexes
removes it — `retract!` tears an inert sentex down directly through the removal choke
point, since it is not a TMS datum and the dependency sweep cannot find it — and
re-running `do/label` under `:all` replaces the whole run.

## What a choice constrains

A constraint — an auto-detected clash or a constraint rule alike — reaches the **direct**
ground choice heads and nothing further. Choices do **not** propagate through ordinary
rules — "choosing red makes it warm, and warm things can't be here" is not expressible
as one, because the Program is built from the choice
heads and the nogoods standing over them: nothing runs the chainer with a choice held
hypothetically, and nothing emits the rule base to clingo's grounder. A constraint that
only bites downstream of a rule therefore has nothing to bite on.

## Relationship to dilemmas and `do/labeling`

A defeasible-default **dilemma** (`contradictions`) is *represented*, not solved — both
sides stay believed and the engine arbitrates nothing. Classifying one is an opt-in
solve: `(do/label CxDilemma Into)` then `(do/classify Into)`, which produces persistent
inert contexts. `(do/labeling Ctx)` commits one labeling *live* into base belief (global,
one at a time — docs/labeling.md); `do/label` is the inert, coexisting, persistent path.

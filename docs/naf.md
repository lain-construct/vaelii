# Negation as failure: `unknown` and `thereExists`

Closed-world negation as a query operator, and the existential that closes a
variable off so it can be negated. Neither is ever stored.

## The two operators

```clojure
(unknown S)          ; holds iff S is not derivable — closed-world negation
(thereExists ?x S)   ; holds iff some binding of ?x makes S derivable
(thereExists [?x ?y] S)
```

`unknown` is negation as failure: `(unknown (flies Tweety))` holds exactly while the
KB cannot derive `(flies Tweety)`. `thereExists` existentially quantifies its
variable (or vector of variables) and **projects it out** — it produces no binding,
it is a test. Its point is to *close a variable off* so `unknown` can negate an
existential:

```clojure
(unknown (thereExists ?c (parentOf ?c Tom)))   ; "Tom has no known parent"
```

Both are answered by a prover (`vaelii.impl.provers` — `UnknownProver`,
`ThereExistsProver`), usable as a top-level goal (`ask` / `ask?`) and as a rule
antecedent. Neither is assertible: a `wff` arm refuses `(unknown …)` /
`(thereExists …)` as a stored fact, the way `different` is refused — a query operator
states no fact.

## Fully bound to evaluate

`unknown` and `thereExists` are **ground/closed only**. Applicability refuses a goal
with a free variable — `sentex/free-vars`, which counts every variable *except* the
ones a nested `thereExists` binds:

| form | `free-vars` |
|------|-------------|
| `(parentOf ?x ?y)` | `{?x ?y}` |
| `(unknown (flies ?x))` | `{?x}` (unknown is transparent) |
| `(thereExists ?x (parentOf ?x ?y))` | `{?y}` (the binder subtracts `?x`) |
| `(unknown (thereExists ?x (parentOf ?x ?y)))` | `{?y}` |
| `(unknown (thereExists ?x (parentOf ?x Tom)))` | `{}` — closed |

An open `(unknown (flies ?x))` is not a test but a search over the whole domain's
*complement* — every `x` that does not fly — so the prover **refuses** it rather than
answering explosively, exactly the honest refusal `different` makes. In a rule, the
free variables must be bound before the `unknown` runs (closure, below) — by a
*generator* antecedent, or by one of the deferred literals that **writes** rather than
only reads: an aggregate's `?n`, an `evaluate`'s output. A `thereExists`'s own variable
never has to be — that is what it is for.

`check-naf-closed` holds every consuming literal to that rule, not only `unknown`: a
`(lessThan ?m 35)` whose `?m` nothing in the rule writes is refused at assert time
too. A bare *goal* nothing binds still answers empty, and the difference is the point
— a goal is asked and gone, while a rule is stored and re-run, so an unbindable input
would silently find nothing backward and throw mid-fixpoint forward, after the rule
was already stored.

## Evaluated over the registry

The argument runs through the **registry** — level 6 of the lookup stack, the *same*
list `exceptWhen` uses. This is a deliberate choice, and it is the same one
[exceptions.md](exceptions.md) makes: closed-world reasoning must read what the KB
**derives without an unbounded proof search**. So a forward-derived fact counts — it is
stored and believed by the time the query runs — while something reachable only by
backward chaining does not. The registry reaches genl specificity, the genlContext
visibility closure, the transitive/symmetric/inverse metadata, disjointness and the
evaluables, and no member of it expands a rule — so nothing here can start a proof
search from inside a relabel loop.

`(unknown S)` is answered by running `S` at level 6 and inverting: **no** solution
means `S` is not derivable, so `(unknown S)` holds. `(thereExists ?x S)` is answered
by running `S` at level 6 and reporting existence, binding nothing outside.

## In a rule antecedent

`(unknown S)` in a rule body is `exceptWhen` **inlined per-literal**: the rule does
not conclude for a binding under which `S` is derivable.

```clojure
(implies (and (bird ?x) (unknown (flies ?x))) (walks ?x))
;; birds walk, unless they are known to fly
```

It shares `exceptWhen`'s whole machinery — evaluation point, re-check index, block /
sweep / revive — differing only in **polarity and combination**:

- an `exceptWhen` exception is one condition, block-if-**all**-conjuncts-hold;
- each `(unknown S)` antecedent is an **independent** condition, block-if-**any**-holds
  — one derivable `S` withdraws the conclusion.

The two block conditions are OR'd wherever a firing's block status is decided.

### Evaluated in the placement context, not the join

An `unknown` antecedent is **not** a join filter. Forward chaining *skips* it in the
join (it binds nothing and names no fact) and checks it at **derive time, per
placement context** — precisely where `exceptWhen` is checked, and for the same
reason: forward and backward must evaluate a NAF condition in the *same* context, or
`sentexes-matching` and a backward search would disagree about one rule. Backward
solves it as a deferred antecedent through the prover at the query's context, which
is the backward analogue of the placement context. Both read the identical level-6
judgement (`chain/unknown-inner-holds?` → `provers/exception-holds?` over the single
inner literal), so the two can never drift.

### Standalone positive `thereExists` desugars

A *standalone* positive `(thereExists ?y S)` antecedent — one **not** wrapped in
`unknown` — is **desugared to `S`** in the `sentex` constructor, with `?y` a fresh
local variable. A standalone existential is exactly `S` with a variable that the
match binds and that (by locality) reaches nothing else, so `S` alone is the
faithful native reading: it joins the store like any generator, one witness per
solution, and needs no special matcher. A person-with-a-child is a parent:

```clojure
(implies (and (person ?x) (thereExists ?y (parentOf ?x ?y))) (aParent ?x))
;; stored as (implies (and (person ?x) (parentOf ?x ?y)) (aParent ?x))
```

A `thereExists` **inside** `unknown` is a NAF query, evaluated by the prover, and is
left intact. So `thereExists` is deliberately *absent* from `deferred-predicates`;
only `unknown` is deferred.

## Order independence, and the re-check

Belief must not depend on arrival order. A conclusion drawn while `S` was absent must
be **withdrawn** when a later fact makes `S` derivable, and **revived** when that fact
leaves. This is the `exceptWhen` block/sweep/revive path, reused verbatim:

- The rule is posted in the re-check index (`[:exception-index <predicate>]`) under every
  predicate its `unknown` antecedents mention — `rules/recheck-predicates` unions the
  exception's and the NAF antecedents' predicates. A fact arriving or leaving on one
  of those predicates (or any subtype, via the genl spec fan-out) queues the rule.
- An **equality** queues it too, and that one no predicate can key. `(unknown (flies
  Tweety))` is answered under Tweety's representative, so merging Tweety with a Birdy
  that flies makes the inner query derivable with nothing on `flies` having moved at
  all — and the firing's own stored binding is now a spelling the KB does not answer
  under. `special/recheck-equality-edge` is the trigger and `chain/settled-bindings` is
  what the firing is re-checked with; [exceptions.md](exceptions.md) has the shape,
  which `unknown` inherits along with the rest of the machinery.
- At the next `settle`, the queued firings are re-evaluated; a firing whose `S` is now
  derivable is **blocked**, and the ordinary dependency-directed sweep **deletes** the
  conclusion and everything resting on it — *garbage collection, not defeat*, exactly
  as for an exception ([exceptions.md](exceptions.md), "Garbage collection, not
  defeat").
- `retract!` captures the rules whose NAF condition a retraction *released* and
  re-chains them, so a revival — which is a re-derivation, not a flipped bit — is
  visible by the time it returns.

The settle-time firing filter (`firing-reachable?`) shapes the exception's conjuncts
and the `unknown` antecedents' inner queries the same way: a ground inner narrows
against the trigger, an existential one (`(thereExists ?x …)`, never ground) falls
through to "keep", which is the safe over-approximation.

## Stratification

Negation as failure needs a stratified rule set. An `(unknown S)` antecedent is a
**negative** dependency on `S`'s predicate (fanned over the genl spec closure), joined
to the same dependency graph as `exceptWhen` and `different`
([exceptions.md](exceptions.md), "Stratification"). A rule set with a cycle through
negation — one rule's `unknown` depends on what another concludes and back — is
**refused at assert time** (`:type :not-stratified`), including the one-rule cycle (an
`unknown` on what the rule concludes) and a cycle a `genl` edge would close. Ordinary
positive recursion is untouched.

## The `out` tracking decision — why nothing is stored

The JTMS `Justification` carries an `:out` slot — a **negation-as-failure antecedent
set** ([nmtms.md](nmtms.md)): a justification is invalid if any of its `:out` datums is
IN. This is Doyle's out-list, and it is the textbook home for `unknown`. It stays
**reserved and unused**, and NAF is maintained by **re-evaluation** instead. The
reasons are the ones [exceptions.md](exceptions.md) already gives for `exceptWhen`,
plus one that is decisive:

- **An existential NAF has no handle.** `(unknown (thereExists ?x (parentOf ?x Tom)))`
  is negation over a *pattern*, not a proposition. There is no single node whose
  OUT-ness stands for "nobody is a parent of Tom", so the `:out` slot — a set of
  handles — simply cannot represent it. The moment `thereExists` enters, the out-list
  is the wrong shape.
- **It stores the negative space.** Using the slot for the ground case
  `(unknown (flies Tweety))` when `(flies Tweety)` is not stored means *materializing*
  an unbelieved node for it — a probe for every proposition that happens not to hold.
  Over a large domain that is the negative space `exceptWhen` refused to store.
- **It cannot compose with computed truth.** A level-6 answer reached through
  transitivity, disjointness or arithmetic has no single node to mark OUT either.

So: **we do not track things that are known-false-but-not-in-the-KB as negated
facts.** Nothing about a NAF condition is stored; it is re-evaluated on the same
triggers an exception uses, and nothing ever *populates* the `:out` slot: the existential
case has no single handle to put in it, so `jtms/valid?` reads the slot on every relabel
and finds it empty. This keeps NAF
consistent with the codebase's existing closed-world mechanism (`exceptWhen`) and the
store free of negative space.

`unknown` is also **belief-sensitive** for free: a stored-but-OUT `S` (a defeated
default) is not believed, so a level-6 match skips it, so `(unknown S)` holds of a
defeated `S` — closed-world negation reads current belief, not mere storage.

## What surfaces where

- Blocking produces **no nogood**: a blocked conclusion does not exist, so nothing is
  contradictory and nothing is arbitrated. `unknown` is undercutting, like
  `exceptWhen` — not a rebuttal.
- A blocked conclusion has no handle, so `why-not (kb sentence context)` reports it
  the same way it reports an excepted one.

## Deferred antecedents in every chainer

`unknown` in a rule body is honoured by **all** the chainers — forward chaining
(`chain/solve-deferred`), `res/prove`, and the node engine.
The last two discharge an antecedent by fact matching and rule expansion, which on its
own proves nothing for a *deferred* antecedent — `unknown`, `different`, `evaluate`.
`res/solve-deferred` closes that: `resolution` sits below the prover registry (`provers`
requires `resolution`), so it cannot name `solve-goal` at compile time and reaches it
through `wiring/solve-goal` — one of the three calls [`vaelii.impl.wiring`](namespaces.md)
collects, because `unknown` runs the registry back over its own argument and so is mutually
recursive with the chainer asking for it. Resolved once into a `delay` rather than carried
on a thread binding, because `query` is lazy and a deferred literal reached mid-stream
must still find the solver; an optional `*deferred-solver*` var overrides it. So `prove` /
`query` / `ask` / forward chaining all agree about a rule with an `unknown` (or `different`
/ `evaluate`) antecedent, and they agree by construction rather than by four separate
implementations.

## Limitations

- **No existential `unknown` witness.** `(unknown (thereExists ?x S))` answers only
  *whether* a witness exists, never *which*; that is inherent to negation as failure.
- **One-level quantification.** `free-vars` respects a `thereExists` one level deep;
  nested quantifiers inside a single literal are not round-one scope.

## Where the pieces are

- **Two provers** over the level-6 list, ground/closed only, complete and
  authoritative; members of `default-provers` and of the `wff` refusal table.
- **Representation** in `sentex`: `unknown?` / `there-exists?` recognizers, `free-vars`
  respecting the quantifier, `unknown` in `deferred-predicates`, the standalone
  `thereExists` desugar, and `check-naf-closed` (closure + quantifier locality).
- **Forward chaining**: `unknown` skipped in the join and blocked at derive time per
  placement context (`naf-blocks?`), alongside the exception.
- **Belief maintenance**: `justification-excepted?` blocks on a NAF antecedent too;
  `index-rule-sentex` / `disintegrate-sentex!` post the NAF predicates in the re-check
  index (`rules/recheck-predicates`); `settle` narrows NAF firings the same way it
  narrows exception firings. Sweep and revival are the ordinary paths — including the
  refusal record ([exceptions.md](exceptions.md), "A refused firing is remembered as
  bindings"), which covers a firing an `unknown` blocked at derive time exactly as it
  covers one an exception blocked: both are re-askable from the bindings alone, and
  both are entries in the same record.
- **Stratification**: `checks/negative-predicates` and `check-stratified` treat an
  `unknown` antecedent's predicate as a negative edge, so a cycle through it — by rule
  or by `genl` edge — is refused.
- **Every chainer**: `res/solve-deferred` (the registry reached through
  `wiring/solve-goal`, overridable via `*deferred-solver*`) lets `res/prove` and the
  node engine evaluate a deferred antecedent, so every chainer agrees about `unknown`,
  `different` and `evaluate` alike.

`naf_test` covers `free-vars`, both operators at top level (belief-following, the
open-goal refusal, the combination, non-assertibility), the `unknown` antecedent firing
and derive-time block, order-independence (block-and-sweep on late arrival, revival on
retract), `unknown (thereExists …)` and standalone positive `thereExists` in a rule, the
closure and locality refusals, and the stratification cycle refusals.

## The third member of the family

[aggregate.md](aggregate.md) adds `agg/count` and its four siblings against the
same seams: query operators, refused by the same `wff` arm, deferred literals with the
same closure rule and the same `:naf-not-closed` diagnostic, level-6 bodies, negative
edges in the same stratification graph, and firings maintained through the same
re-check index. Two things differ, and both follow from an aggregate binding a
**value** where `unknown` is a test — it is evaluated per placement context rather than
skipped in the join, and a queued aggregate rule is re-joined whether or not anything
blocked (a count that rose licenses a firing no block ever suppressed).

# Symbolic (schematic) equational reasoning

Equations with **variables over function terms** — `(equals (fatherOf (fatherOf ?x))
(grandfatherOf ?x))` — and how they come to rewrite and prove terms. This is the
gap [equality.md](equality.md) leaves open: the closure there is a partition over
**symbols**, so it merges names but says nothing about a term-level *definition*.

Two things are built on top of the partition, and both **reduce to machinery that
already exists** rather than adding a new theory engine.

## The two reductions

### Part A — compound equality over reifiable NATs

`(equals (MotherOf Alice) (MotherOf Bob))` — *Alice and Bob share a mother, so they
are siblings* — needs nothing new when `MotherOf` is a `reifiableFunction`. Each side
is a **ground reifiable NAT**, so `assert` reifies it to its NART constant *before*
well-formedness runs ([nat.md](nat.md)): the sentence the checks see is an ordinary
`(equals K1 K2)` over two symbols, and the partition + migration merge them. A fact
about one holds of the other, and retracting the equation un-merges them — all the
belief-following of ground equality, for free.

A compound that **does not** reduce is still refused. A NAUT measure
`(QuantityFn 5 Kilogram)` is an `unreifiableFunction` application: it stays
structural, never reifies to a symbol, so `wff/equality-problems` sees the compound
and rejects it. Measure sameness is `sameQuantity`, a *computed* comparison
([quantity.md](quantity.md)), not the equality closure.

### Part B — schematic equational rules

`(equals L R)` with **variables** is not a merge — it is an oriented **rewrite rule**
over a schema. Stored and queried terms are normalized to a single normal form, so a
stored `(parentChain (fatherOf (fatherOf Tom)))` and a query `(parentChain
(grandfatherOf Tom))` meet. Everything below is Part B.

`vaelii.impl.rewrite` is the pure term algebra — orientation, matching,
normalization — knowing nothing of the store, belief, or the taxonomy. The taxonomy
caches the active oriented rules (belief-following, like the partition),
`kb/rewrite-term` threads normalization into the same path ground congruence uses, and
`vaelii.impl.special` justifies each rewritten twin.

## Orientation and termination

A schematic equation is oriented into a rewrite `L → R` by a **reduction order**, so
rewriting strictly decreases every term at each step and therefore **terminates** —
whatever the rule set, with no confluence or completion argument. The order is the
**Knuth-Bendix order** with unit weights (`rewrite/kbo>`):

- Every function symbol and variable weighs 1, so a term's weight is its leaf count
  (`term-size`). The **heavier** side rewrites to the lighter.
- An **equal-weight** pair is decided by a fixed **symbol precedence** — the root
  symbols compared, then the arguments lexicographically. So `(f (g ?x)) = (g (f
  ?x))` orients (toward whichever root the precedence ranks lower), where a size-only
  rule would refuse it.
- Both are gated by the **variable condition** (`var-dominates?`): every variable
  must occur at least as often in the bigger side as in the smaller. This is what
  keeps the order stable under *every* substitution — without it, a substitution
  duplicating a variable the smaller side has more of could make the rewrite grow.

`kbo>` is a genuine reduction order (stable under substitution and context,
well-founded), so a rule `l → r` with `l ≻ r` terminates. The **precedence is a total
order on symbols by their natural `compare`** — content-derived, never arrival-order —
so orientation is order-independent: the two spellings of one equation, and the
equation and its mirror, orient identically.

A **permutative** equation — `(rel ?x ?y) = (rel ?y ?x)` — is KBO-incomparable in
both directions and is **refused** at assert time (`wff/equality-problems`, before
anything is stored). No term order can orient a permutation; that needs AC-rewriting,
a separate and larger mechanism. An equation whose variable condition fails both ways
(a side carries a variable the other lacks) is refused for the same reason.

## Matching and normalization

- **One-way match** (`rewrite/match`): a rule LHS is a *pattern* whose variables may
  bind; the subject is a term (possibly variable-bearing). Only the pattern's
  variables bind — a variable in the subject is an opaque constant — so a rule never
  captures a query's variables. Because orientation forbids an RHS variable absent
  from the LHS, the match binds every variable the RHS substitutes.
- **`normalize`** rewrites a *term* to a fixpoint: innermost subterms first, then the
  root, repeating until nothing applies. Termination is the reduction order; a large
  guard is a pure safety net that a bug would trip rather than hang.
- **`normalize-sentence`** rewrites a *predication* `(pred arg…)` by normalizing each
  argument and **leaving the functor and shape untouched**. A schematic equation is
  about denoting terms, which live in argument position; a predication is an
  assertion, not a term. `fatherOf` the function symbol and `fatherOf` a predicate are
  the same symbol, so protecting the predication is what stops a rule about the *term*
  `fatherOf(fatherOf(x))` from rewriting a *fact* that merely shares the shape.

## The write path — cache, migrate, supersede

When a schematic equation is asserted (`vaelii.impl.special`, the equality table's
integrate arm):

1. **Orient and cache.** `rewrite/orient` produces `[lhs rhs]`; `tax/add-rewrite-rule`
   stores it belief-following (a support/active split reconciled by `refresh-beliefs`,
   the same discipline as the equality partition — a defeated equation stops
   rewriting, a revived one resumes).
2. **Migrate.** Every stored sentex the rule's LHS head reaches (`kb/find-sentexes`,
   one term-index lookup — a superset the per-sentex check narrows) gets a **rewritten
   twin** under the normal form, placed in the original's context, **derived and
   justified** by `[the original, the equation]`. `migrate-sentex` counts each
   applicable rewrite rule (and each symbol equality) as an independent witness, so a
   twin gets one justification per contributor.
3. **Supersede.** The un-normalized original stays stored but is not believed and does
   not match — the same TMS `:superseded` state a merged spelling uses.

Because the twin is a justified derivation, dropping the equation invalidates it: the
dependency-directed sweep collects the twin and un-supersedes the original. So
retraction is a re-derivation, not a flipped bit — the same belief-following ground
congruence has.

## The read path — one normal form everywhere

`kb/rewrite-term` is where symbol congruence and schematic normalization compose: it
replaces every symbol with its class representative (ground congruence — the term
index locates a merged term at any depth) and then normalizes the argument terms
under the active rewrite rules. Both halves are **gated** — a KB with no merges pays a
representative lookup per symbol, one with no schematic equations skips normalization
(`tax/rewrite-rules` is empty).

Migration and every query path go through `rewrite-term`, so a stored term and a goal
meet at one normal form. **All four query paths normalize the top goal**: `sentexes-matching` and
`ask` (via `kb/rewrite-goal`), and `prove` and `query` (via
`core/prepare-goal-for-read`, which reifies NATs *and* rewrites the goal). It is the
**top** goal that is normalized — stored facts are already in normal form via
migration, so a subgoal a rule expansion generates needs no further rewriting, the
same reliance `ask` makes. `different` is exempt from goal rewriting: its arguments
must stay un-rewritten to read class membership.

## Order-independence

Two properties keep the normal form a function of the *set* of equations, never their
assertion order — the invariant [nmtms.md](nmtms.md) makes non-negotiable:

- **Orientation** is content-derived (weight, then a total symbol precedence), so the
  same equation always orients the same way.
- **Rule application** tries rules in a **content-sorted** order (`tax/rewrite-rules`
  sorts by printed LHS/RHS), so two overlapping rules that could rewrite one term pick
  the same winner regardless of which was asserted first — order-independence holds
  even for a non-confluent rule set. The order is derived once per rule *set*, not per
  call: it is memoized in the taxonomy's `:rewrite-order` side atom, stamped on the
  identity of the `:rewrite-active` map, so every writer of that map retires it and no
  writer has to remember to. Without it, every `sentexes-matching` carrying a context paid the sort
  — `kb/rewrite-goal` calls `rewrite-term`, which reads this.

## Recover

Supersession is derived from the rules, not stored, so `recover` re-establishes it.
`rebuild-taxonomy` re-orients each stored schematic equation into the rule cache, the
twins' justifications replay from the durable store on their own, and
`core/recovered-supersessions` nominates the rule-reached sentexes as supersession
candidates — `supersession-map` re-derives the actual displacement, since
`rewrite-term` normalizes. So the same beliefs stand either side of a restart.

## Confluence — surfaced, not completed

A terminating rewrite system is confluent iff every **critical pair** joins. The
engine does not *complete* a non-confluent set (Knuth-Bendix completion can loop), but
it does **detect and report** the conflicts. When a schematic equation is asserted,
`rewrite/non-joining-pairs` computes the critical pairs between the new rule and the
other active rules — a non-variable subterm of one LHS **unifies** with the other LHS,
giving two ways to rewrite the overlap — and normalizes both reducts; a pair that does
not join is recorded in the [violations](api.md) ledger as `:non-confluent` (naming
both rules and both forms) and logged. So two equations that disagree about a shared
term — `f∘f = g` alongside `f∘f = h` — are surfaced to the author.

It is **detection, not resolution**: nothing is dropped. The normal form stays
deterministic (rules applied in content-sorted order), and `unify` remains the arbiter
of every match, so a non-confluent set can only make a term written one way miss a
theory-equal term written another — never match wrongly. **Self-overlaps are
excluded**: a lone rule's abstract non-confluence (`f³` reduces two ways) is absorbed
by the deterministic normalization — the same syntactic term always normalizes the
same way — so it never causes a miss and is not flagged; only two *distinct* equations
disagreeing is worth the author's attention.

## What is not built

The **open-goal / search** half — E-unification / paramodulation (proving `(equals ?x
?y)` by searching rewrites on demand), Knuth-Bendix **completion** (turning a
non-confluent set confluent), and AC-rewriting for permutative equations. See
[equality.md](equality.md), "What is not built".

## Where it lives

- `vaelii.impl.rewrite` — pure: `term-size`, `orient` / `kbo>`, `match`, `normalize` /
  `normalize-sentence`, `schematic-equation?`, `rule-applies?`, and
  `non-joining-pairs` (critical-pair confluence detection). Requires only
  `vaelii.impl.sentex`.
- `vaelii.impl.taxonomy` — the belief-following rewrite-rule cache
  (`add-rewrite-rule`, `del-rewrite-rule!`, `rewrite-rules`, refreshed by
  `refresh-beliefs`, cleared by `clear-relations!`).
- `vaelii.impl.kb` — `rewrite-term` threads normalization into congruence.
- `vaelii.impl.special` — the equality table's schematic arm:
  `integrate-rewrite-rule`, `migrate-matching`, and the schematic contributor
  collection in `migrate-sentex`.
- `vaelii.impl.wff` — `equality-problems` waves the schematic shape through and
  refuses an unorientable one.
- `vaelii.impl.checks` — `check-ground` exempts a schematic equation from the
  non-ground refusal.
- `vaelii.core` — `prepare-goal-for-read` (the `prove` / `query` normalization),
  `recovered-supersessions` (the recover seam).
- Tests: `rewrite_test` (the pure algebra), `equational_test` (the integration:
  Part A, Part B, belief-following, termination, order-independence, KBO orientation,
  the four-path parity), `recovery_test` (durability).

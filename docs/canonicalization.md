# Sentex canonicalization (`vaelii.impl.sentex`)

Beyond the connectives, a sentence is put into a canonical form so logically
identical knowledge is stored once.

## Canonical variables

A rule's variables are renamed `?var0`, `?var1`, … by first occurrence in
canonical order. **`:varmap`** maps them back to what the author wrote
(`{?var0 ?x}`), and `sentex/originalize` restores the original names for display.
Facts carry no varmap.

## Canonical literal order

A rule's antecedents are sorted **structurally** — rank, arity/shape, then value.
Ordering runs *before* numbering with a variable-**blind** comparator, so it can
never depend on the author's variable names. Literals that tie under it (a
same-predicate self-join) are resolved by an **exact prefix minimization** — the
order is built one literal at a time, keeping only the minimal extensions — which
returns the smallest canonically-numbered form without enumerating the tie group's
permutations.

The comparison runs over the **whole rule** — antecedents, then consequent, then
exception — because two orders can render identical antecedents and differ only in
what the consequent says about them. Comparing antecedents alone leaves that decided
by traversal order, and breaks dedup at tie groups as small as **two**. A lexical
comparison of constant symbols is the last resort.

Cost is O(k²) numberings for any tie group whose literals are distinguishable at
all. The hard shape is genuine **automorphism** — k antecedents of one predicate
sharing no variables, a joinless cross product — where every ordering renders the
identical antecedents and only the consequent (then the exception) separates them.
The exact search would keep all k! orderings and pick the minimal consequent at the
end; `prune-by-tail` instead folds the consequent into the search. Such a group is
**joinless** (so every ordering renders the same antecedents) and **tail-isolated**
(its variables touch no other antecedent, so its ordering changes nothing but its own
consequent), which makes the consequent the whole tiebreak — a never-reordered form,
so projecting it is content-, not order-dependent. Projecting it under each survivor's
partial numbering (an unnumbered variable → a sentinel that sorts last) and keeping
only the minimal-so-far survivors each round collapses the automorphic case to O(k²)
too, with no cap. It is exact, not a heuristic: numbering is monotonic across rounds,
so an unnumbered variable can only be given a larger number later — a survivor whose
projected tail is strictly larger can never be the whole-rule minimum. The tie is
broken **per origin** (the incoming survivor a candidate descends from), so it never
decides between orderings that differ on an earlier group's antecedents, which outrank
the tail. The result is identical to the exhaustive search; only the cost changes.

Two kinds of literal are **held back** in the author's order, because their
position is operational rather than logical:

- **Deferred (evaluable)** literals — which consume bindings rather than produce them.
  `sentex/deferred-predicates` names fifteen: `evaluate`, `lessThan`, `greaterThan`,
  `different`, `unknown`, the five quantity comparisons, and the five aggregation
  operators.
- The **recursive** literal of a recursive rule. Reordering it could turn a
  right-recursive rule left-recursive, which the backward chainers cannot execute.

## Symmetric arguments sorted — ground literals only

A *ground* `(siblingOf Bob Ann)` and `(siblingOf Ann Bob)` store as one sentex. A
literal holding a variable is a **pattern** (a query, or an antecedent about to be
matched) and is never reordered: variables sort last, so sorting one would move its
ground argument into slot 1 and miss the stored fact.

Order-insensitive *lookup* is handled at match time instead — `res/raw-match`,
`core/sentexes-matching`, and `kb/find-sentex-handle` probe **both argument orders** for a
symmetric predicate. That also keeps a fact asserted *before* its `(symmetric P)`
declaration reachable, and makes re-asserting its mirror resolve to it rather than
duplicate. Sorting needs the taxonomy, so every store/lookup builds its sentex
through `res/kb-sentex` (which supplies `:symmetric?`).

## Comparison siblings folded

`greaterThan` is stored as `lessThan` with reversed arguments
(`sentex/comparison-siblings`), so only the `<` direction is ever stored; a
`greaterThan` *goal* is still answerable.

## Comparison chains collapsed

`lessThan` is **variable arity**, and chains in a rule merge: `(lessThan ?a ?b)` +
`(lessThan ?b ?c)` ⇒ `(lessThan ?a ?b ?c)`. A branch (`?a<?b`, `?a<?c`) is left
alone.

## Rule wrappers become fields

`(set/forwardRule (implies …))` is not data *about* a rule — it is how the rule's
direction is written, so like `not`/`implies` it canonicalizes **into the record**:
`:direction` (`:forward`/`:backward`/`:inert`/`:both`, `:both` for a bare
`implies`) and `:defeasible` (from `set/defaultRule`). Wrappers may nest — a
defeasible forward rule — and never reach the stored sentence. The `:direction`
opt on `assert` and `assert-rule` is just the programmatic spelling: it wraps, and
the wrapper becomes the field.

Neither slot is in the identity key, so re-asserting with a different wrapper
resolves to the **one** sentex. Where the two spellings disagree, the slot is then
resolved from **content**: the least restrictive direction (`:inert` is the bottom,
`:forward` and `:backward` join to `:both`), and strict over defeasible — a rule
somebody also stated without `set/defaultRule` is one they stated as holding
outright. Both resolutions are commutative and idempotent, which is what the pair
has to be: keying the slot on which assertion arrived first would let the same two
assertions in the two orders reach two sets of beliefs, and order independence is
not negotiable ([nmtms.md](nmtms.md)).

## Result

So rules identical up to **variable names, antecedent order, symmetric argument
order, and comparison direction** all dedup to one handle — with one carve-out the
hold-back above states: a *deferred* literal and the *recursive* literal keep the
author's relative order, since their position is operational, so two spellings that
differ only in where those sit are two handles by design.

## See also

- [docs/indexing.md](indexing.md) — how the canonical form reaches the trie key.
- [docs/storage.md](storage.md) — the `AtomicSentex` / `RuleSentex` record shapes.

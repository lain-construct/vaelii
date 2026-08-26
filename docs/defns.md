# Definitional collection relations

- **Covers:** `defnNecessary` / `defnSufficient` / `defnIff` — tying a collection's
  membership to a defining condition on the member `?x`, expanded into ordinary forward
  rules at assert so the entailment inherits indexing, TMS support, retraction and
  belief-following.
- **Not here:** the argument-type declarations `arg` / `genlArg` a term is checked and
  entailed against → [argtypes.md](argtypes.md); carrying a stated claim across a
  transitive relation → [inherit.md](inherit.md); the `genl` / `disjoint` collection
  hierarchy itself → [taxonomy.md](taxonomy.md); a rule whose consequent is a rule →
  [generators.md](generators.md).
- **Assumes:** forward rules, `implies`, justification, defeat-class, `genlCx` context
  visibility → [glossary.md](glossary.md), [inference.md](inference.md),
  [contexts.md](contexts.md).

A collection is a unary predicate whose instances are its members: `(bachelor Tom)` says
Tom is a bachelor. `genl` relates collections to one another and `disjoint` separates
them, but neither says what it *takes* to be a member. These three relations do, by
naming a **condition on the member** and pointing it in one of two directions.

```clojure
(defnNecessary  bachelor (unmarried ?x))   ; member => condition
(defnSufficient bachelor (unmarried ?x))   ; condition => member
(defnIff        bachelor (unmarried ?x))   ; both
```

The member is the distinguished variable **`?x`**. The condition is any sentence
mentioning it — a single literal, a conjunction, a negation — and a condition that never
names `?x` is refused, because it says nothing about membership.

## They expand into forward rules

Each `defn*` fact is stored like any other fact, and *what it means* is a forward rule
materialized beside it:

| assertion | expands to |
|---|---|
| `(defnNecessary Coll C)` | `(implies (Coll ?x) C)` |
| `(defnSufficient Coll C)` | `(implies C (Coll ?x))` |
| `(defnIff Coll C)` | both |

So `(defnNecessary bachelor (unmarried ?x))` beside `(bachelor Tom)` derives
`(unmarried Tom)`; `(defnSufficient bachelor (unmarried ?x))` beside `(unmarried Tom)`
derives `(bachelor Tom)`; and `defnIff` is exactly the conjunction of the two, no more.

```clojure
(defnNecessary bachelor (unmarried ?x))
(bachelor Tom)
(v/ask? kb '(unmarried Tom) 'CxUniverse)               ; => true
(v/sentexes-matching kb '(unmarried Tom) 'CxUniverse)  ; => the derived sentex
```

The expansion is **into the existing machinery**, not a prover of its own. The companion
rule is an ordinary rule sentex: it is indexed by its antecedent and consequent
predicates, forward-chained from the same agenda, and placed in the maximal context that
sees both it and the facts it fired on. A conjunctive necessary condition
`(and (male ?x) (unmarried ?x))` polycanonicalizes into one rule per conjunct like any
conjunctive consequent, and a sufficient conjunction becomes a conjunctive rule body that
needs every conjunct met. A **disjunctive** sufficient condition becomes a rule body that
disjoins, polycanonicalized into one companion rule per alternative — which is how "a pet
is a dog or a cat" is written ([canonicalization.md](canonicalization.md)).

## The rule is derived, so retraction and belief follow it

The companion rule is **justified by the `defn*` fact alone** — the mint a generator
makes for a stamped rule (`chain/mint-rule`), minus the join bindings. It is not a
premise: nobody asserted it, and it stands only while the `defn*` fact it rests on is
believed.

```clojure
(def dh (v/assert kb '(defnNecessary bachelor (unmarried ?x)) 'CxUniverse))
(v/assert kb '(bachelor Tom) 'CxUniverse)
(v/ask? kb '(unmarried Tom) 'CxUniverse)   ; => true
(v/retract! kb dh)
(v/ask? kb '(unmarried Tom) 'CxUniverse)   ; => false — the rule went OUT with the fact
```

Everything a derived rule gets for free follows from that one justification:

- **Retraction** of the `defn*` fact withdraws the rule and, with it, every conclusion the
  rule licensed — the JTMS relabel reaches them, nothing has to hunt them down.
- **Belief-following.** Defeat or retract the `defn*` fact and the rule stops firing; assert
  it again and the conclusions return. A `:default` `defn*` makes a `:default` rule
  (`conferred-class` caps the mint at the fact's own class), so a stronger contradicting
  belief can defeat what it concludes.
- **Recovery.** The rule and its justification live in the record store, so `recover`
  rebuilds the entailment from the store exactly as the running KB held it.

## Order independence and context scoping

The definition and its members may arrive in either order. When the `defn*` fact is
asserted, the companion rule is seeded onto the agenda and fires over the facts already
stored; when a member arrives later, it triggers the already-indexed rule. The same
knowledge yields the same beliefs whichever came first.

The rule is stored in the `defn*` fact's own context, so it fires only on facts that
context can see up the `genlCx` cone, and its conclusions land where the reasons meet. A
definition in one context does not reach a member stated in a sibling context it cannot
see.

## Open-world: what these do not do

The reading is **open-world**, and the boundary is worth stating as an absence. A
`defn*` relation licenses the two positive rules above and nothing else. In particular
there is **no closed-world membership completion**: nothing concludes that a thing *is
not* a member, and condition-absence draws no negation.

- A thing the condition is merely silent about is **neither** a member nor a non-member.
  Under `(defnIff bachelor (unmarried ?x))`, a `Tom` mentioned nowhere yields neither
  `(bachelor Tom)` nor `(not (bachelor Tom))`, and neither `(unmarried Tom)` nor its
  negation.
- `defnSufficient` never fires on a condition it cannot see met. Failing to derive
  `(unmarried Tom)` is not evidence that Tom is married, so it is not evidence that Tom is
  not a bachelor.
- `defnIff` is the conjunction of the necessary and sufficient rules — the "and nothing
  else is a member" a closed reading would add is not among them.

A modeller who wants a negative conclusion writes it as knowledge: an `(unknown …)`
antecedent for negation as failure ([naf.md](naf.md)), or a `disjoint` declaration and an
explicit `not` for a genuine exclusion ([taxonomy.md](taxonomy.md)). The `defn*` relations
stay on the positive side of that line.

## The vocabulary

`defnNecessary` / `defnSufficient` / `defnIff` are declared in `CxCore` as binary
predicates. The first argument names a collection (a kind, so `genlArg … 1 thing`); the
second is the condition sentence, a term (`arg … 2 thing`). They relate a kind to a
sentence, so they are honestly mixed and marked neither `instanceRelationPredicate` nor
`typeRelationPredicate`, the way `result` is ([argtypes.md](argtypes.md)).

The condition carries the member variable `?x`, so a `defn*` fact is not ground — and it
is exempted from the ground check the way a schematic equation is
([equational.md](equational.md)): it is stored to retract and belief-follow, and the
variable belongs to the rule the fact expands into, where `check-range-restricted`
governs it.

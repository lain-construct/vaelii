# 31. Definitions

- **Covers:** stating a type's membership condition with `defnNecessary`, `defnSufficient`
  and `defnIff`; the forward rules a definition expands into; a condition built from
  computed predicates; the open-world reading and the one negative answer a definition
  gives; a `:monotonic` definition deciding a literal value at the argument check; and the
  audit that finds a definition whose two halves disagree.
- **Not here:** stating a term's comment as facts and rules in general →
  [ch. 7](07-comments.md); the `genl` parent and the differentia of a type →
  [ch. 9](09-differentia.md), [ch. 10](10-parent.md); argument-type declarations →
  [ch. 18](18-argument-types.md); a negative conclusion drawn from absence →
  [ch. 32](32-negation.md).
- **Assumes:** [ch. 18](18-argument-types.md), [ch. 24](24-strength.md),
  [ch. 29](29-rules.md).

A type is a unary predicate, and `genl` places it among other types. Neither says what it
takes to be a member. The three `defn*` relations do: each names a type and a condition
on the member, written over the variable `?x`, and points the condition in one direction
or both.

| sentence | reading | expands to |
|---|---|---|
| `(defnNecessary T C)` | every member satisfies `C` | `(implies (T ?x) C)` |
| `(defnSufficient T C)` | whatever satisfies `C` is a member | `(implies C (T ?x))` |
| `(defnIff T C)` | both | both rules, nothing more |

## Necessary, sufficient or both

*The definitional form of **represent the definition***

**Practice.** When a type's comment states a condition every member meets, state it as a
`defnNecessary`. When the comment states a condition that makes a thing a member, state
it as a `defnSufficient`. Write the condition over `?x` and over no other free variable.
When the condition is a single type literal, state a `genl` edge instead.

**Example.** `core.txt` defines each sign-refined integer type both ways:

```clojure
(defnSufficient positive_integer (and (integer ?x) (greaterThan ?x 0)))
(defnNecessary  positive_integer (and (integer ?x) (greaterThan ?x 0)))
```

**Why.**

- Logical: a necessary condition and a sufficient one are different claims. Every
  positive integer is greater than zero, and every integer greater than zero is a
  positive integer; a type whose comment states only the first has a necessary condition
  and no sufficient one. Stating each direction the meaning has, and no direction it
  lacks, keeps the KB from concluding membership for a thing that merely meets an
  obligation of members.
- Engine: a condition that does not mention `?x` is refused at assert with
  `:type :not-well-formed`. Such a condition says nothing about the member, and expands to
  a rule that concludes its consequent for every member (necessary) or a rule that is not
  range-restricted (sufficient).
- Maintenance: a reviewer identifies a `defn*` fact as a definition from its functor, and
  the query-time provers, the argument check and `kb-integrity` treat it as one. They
  treat a hand-written rule with the same content as a rule.

**Why not the other ways.** A `defnNecessary` whose condition is one type literal says
what a `genl` edge says. The edge is held in the cached `genl` closure and answers a
membership in the supertype by subsumption, with nothing stored per member. The
definition expands to a forward rule that stores one derived membership per member, and
`disjointness-audit`, `direct-genls` and every separation check read the edge, not the
rule. A sufficient condition stated only because it is true, with no reader that needs
the membership, is paid on every load: `core.txt`'s note on the exact arity classes
records that a sufficient condition for `binary_predicate` from an arity of 2 and
predicate membership, with its five siblings, would add 36 memberships and 748 justifications to the shipped starter
and 600 ms to a 3.2 s load, and the file states no such sentence.

**Audit.** For each sentence of a new type's comment that states a membership condition,
the block holds the `defn*` fact in the direction the sentence states, or a `genl` edge
for a single-literal condition.

## The expansion is a derived rule

**Practice.** State a definition whose condition reads stored predicates in the context
whose facts it should reach, at the strength its truth has. Let the expansion produce the
rules; do not also write them.

**Why.**

- Engine: the companion rule is justified by the `defn*` fact alone, as a generator's
  minted rule is. Retracting the fact takes the rule out, and the JTMS relabel takes out
  every conclusion the rule licensed. A `:default` definition mints a `:default` rule,
  because the mint's strength is capped at the fact's own class, so a monotonic contrary
  defeats what the definition concludes. A conjunctive necessary condition splits into one
  rule per conjunct, and a disjunctive sufficient condition into one rule per
  alternative ([ch. 29](29-rules.md)).
- Context: the companion rule is stored in the definition's own context and fires only on
  facts that context sees. A definition in one middle context does not reach a member
  stated in a sibling context.
- Order independence: asserting the definition seeds its rule over the facts already
  stored, and a member arriving later triggers the indexed rule, so the two arrive in
  either order with the same beliefs.

**Why not the other ways.** A hand-written rule beside the definition is a second source
for the same conclusions. Retracting the definition then leaves the hand-written rule
concluding, and `kb-integrity`'s `:definition-inconsistencies` and the definition provers
never see it.

**Audit.** `git grep` the change for a rule whose antecedent and consequent restate a
`defn*` fact in the same file, and drop it.

## A computed condition

**Practice.** When every conjunct of the condition is computed (a value kind such as
`integer` or `string`, a comparison, `matchesPattern`), state the condition as a
`defnSufficient` and a `defnNecessary` pair, as `core.txt` does, rather than as one
`defnIff`.

**Why.**

- Engine: a computed predicate has no stored extent, so no conjunct of such a condition
  binds `?x`, and the sufficient half expands to no forward rule. Membership is answered
  where the question is asked. `DefnSufficientProver` takes a ground goal `(T a)`,
  substitutes `a` into the sufficient conditions of `T` and of each type below `T`, and
  evaluates them at level 6, the registry without rule expansion. `DefnNecessaryNegationProver`
  answers a ground `(not (T a))` from a necessary condition of `T` or of a type above it
  that evaluates false for `a`.
- Engine: both provers read the bare `defnSufficient` and `defnNecessary` facts only. A
  `defnIff` over a computed condition is read by the argument check, which takes it as
  both halves, and by neither prover, so `(positive_integer 7)` would have no query-time
  answer under it.
- Logical: the pair states the same two claims a `defnIff` states, so the choice changes
  no meaning.

**Why not the other ways.** A forward rule cannot fire on a condition nothing stores.
Asserting the computed memberships as facts (`(positive_integer 7)` and so on) stores one
sentex per value for a set the evaluables already decide.

**Audit.** For each `defnIff` in the change, check whether a conjunct of its condition is
a stored predicate. When none is, restate the definition as the bare pair.

## Open world, and the one negative answer

**Practice.** Read a definition as open-world. When an application needs a negative
conclusion from the absence of a condition, state the negation as knowledge: an
`unknown` antecedent, or a `disjoint` declaration and a stated `not`
([ch. 32](32-negation.md)).

**Why.**

- Logical: a `defnIff` is the conjunction of its two rules, and neither rule says "and
  nothing else is a member". A thing the KB is silent about is neither a member nor a
  non-member, and failing to derive the condition is no evidence that the condition fails
  (**truth, not provability**).
- Engine: the one negative answer comes from a necessary condition that positively
  evaluates false. `DefnNecessaryNegationProver` climbs the reflexive `genl` ancestor set
  and answers `(not (T a))` at the first necessary that fails for `a`. The test is
  two-valued on the condition, a type with no necessary anywhere above it makes the
  prover inapplicable, and the answer is computed at query time with nothing stored. A
  KB that states `(T a)` against a failing necessary keeps both, and `argue` reports
  `:contradiction`.

**Why not the other ways.** A closed reading would conclude non-membership from a
missing condition fact, and the arrival of that fact would withdraw the conclusion. Each
negative would then state what the KB had not yet been told, not what holds.

**Audit.** For each negative conclusion the change expects from a definition, name the
necessary condition that fails, or the `unknown` or `disjoint` that states it.

## A definition at the argument check

**Practice.** When an argument position takes literal values of a type the KB defines,
state the type's definition at `:monotonic` with every conjunct evaluable, so the
argument check decides each value by the definition.

**Example.** A composed definition of a temporary string type, with an argument
declaration that reads it:

```clojure composed
(set/monotonic (defnSufficient tmp_zip_code (matchesPattern ?x "\\d{5}")))
(set/monotonic (defnNecessary tmp_zip_code (matchesPattern ?x "\\d{5}")))
(arg tmpPostalCodeOf 2 tmp_zip_code)
```

**Why.** An argument declaration judges a literal value by its kind, so a type with no
`genl` edge to a value kind convicts every value under it. A `:monotonic` definition
decides first, in this order: a failing necessary of a strict supertype convicts; else a
sufficient of the type or a subtype, true on the value, admits; else the type's own
failing necessary convicts; else the value's kind decides. A `:default` definition is
defeasible, so it decides nothing, and a conjunct naming a stored predicate cannot be
tested on a literal and decides nothing either. A value the check convicts is held inert,
not refused.

**Why not the other ways.** A `genl` edge from the type to `string` admits every string,
so the declaration would admit a value the pattern rejects.

**Audit.** For each argument position typed by a defined type, confirm the definition's
strength with `find-sentexes` and that each conjunct is evaluable.

## The two halves agree

**Practice.** Run `kb-integrity` over a finite set of candidate values for every defined
type the change adds or edits, and resolve each `:definition-inconsistencies` finding.

**Why.** A finding is a `[type term]` pair for which a sufficient condition of the type or
a subtype passes and the type's own necessary condition fails, so the definition provers
answer both `(T a)` and `(not (T a))`. The category covers every type a visible
`defnSufficient` names and each type above it, and reads only.

**Audit.** The `:definition-inconsistencies` category is empty for the change's
candidate terms, or each finding has its fix in the diff.

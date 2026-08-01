# Measures: the NAUT-evaluating quantity prover

A **measure** is a NAUT — an `unreifiableFunction` application that stays *structural*
so its magnitude and unit are readable ([nat.md](nat.md)):

```clojure
(QuantityFn 5 Kilogram)            ; a point measure — 5 kilograms
(QuantityIntervalFn 1 2 Meter)     ; an interval measure — [1, 2] metres
```

`QuantityProver` (`vaelii.impl.provers`) answers five comparisons over two ground
measures by **normalizing** each against the KB's `dimensionOf` / `conversionFactor`
table and comparing:

```clojure
(sameQuantity M1 M2)
(quantityLessThan M1 M2)          (quantityGreaterThan M1 M2)
(quantityLessThanOrEqual M1 M2)   (quantityGreaterThanOrEqual M1 M2)
```

Nothing is stored or asserted. A comparison is a **computed** result, never an
asserted equality — the equality closure ([equality.md](equality.md)) refuses numbers
and compounds, so `sameQuantity` deliberately routes nowhere near it.

## The table

Two ordinary stored facts drive normalization, both read through
`res/matches-visible` (belief- and context-filtered):

```clojure
(dimensionOf Kilogram Mass)            ; Kilogram measures the Mass dimension
(conversionFactor Gram Kilogram 0.001) ; one Gram = 0.001 of the base unit Kilogram
```

Put them in a context every querent sees (e.g. `UniverseContext`) so the prover finds
them from any asking context.

**Three dimensions ship filled in.** `kb/upper/MeasureContext.txt` states Length in
`Meter`, Mass in `Kilogram` and Duration in `Second`, with the ordinary units of each,
and `UniverseContext` sees it — so a KB that loads the starter compares measures without
declaring anything first. The test for a shipped unit is that its factor is a
*definition*: a minute is sixty seconds by stipulation, where how heavy a particular
thing is, is a measurement and belongs wherever that thing's facts do. A KB measuring
something else states its own units the same way, and a `starter-test` case holds the
shipped ones to converting direct-to-base within one dimension.

## `normalize-quantity`

`(normalize-quantity kb measure context)` → `[dimension lo-base hi-base]`.

- **Dimension** is `(dimensionOf U ?d)`, or **the unit `U` itself** when the unit
  declares none. So two measures in the *same unit* are always comparable (their
  dimension is that unit), while two distinct undeclared units are not (their
  dimensions differ). A declared `dimensionOf` is what lets separate units share one
  dimension and compare.
- **Base magnitude** is `N × (conversionFactor U ?base ?factor)`, the factor defaulting
  to `1` when the unit declares none (it is then its own base). Conversion is
  **direct-to-base** — one multiply, no chaining — so every unit of a dimension must
  convert to a *single* base unit for the magnitudes to line up.
- A point `(QuantityFn N U)` has `lo-base = hi-base`; an interval keeps both bounds.

### A declaration the KB disagrees with itself about

Both reads take the binding every believed, visible match **agrees** on. Restating one
declaration in several contexts of the cone is not a disagreement — the matches carry the
same bindings and collapse to one. Two declarations that differ are: the unit then falls
back to being its own dimension and its own base, exactly as an undeclared unit does, and
compares only against itself.

Reading the first match instead would answer whichever the index yields, and that is a
handle order — the same knowledge loaded in the other order would convert by the other
factor and give a different number out of the same KB, which is the one thing the engine
does not allow. So a doubly-stated reading is declined rather than adjudicated, the rule
`duration/interval-length` follows for two lengths and `stp/endpoints-of` for two starts.

The base and the factor are **one** reading, taken together: a base from one declaration
and a factor from another would convert into a unit nothing said it converts to, and
`base-unit-of` — which decides the unit a computed answer is *rendered* in — would then
disagree with the arithmetic that produced it.

## Comparison semantics

Comparisons hold only **within one dimension**. A dimension mismatch (`5 Kilogram` vs
`5 Meter`) is never equal or comparable — every comparison fails, and none throws.

The interval reading is **necessary** (definite): a comparison holds only when it holds
of every point of each interval. For points (`lo = hi`) it collapses to ordinary number
comparison:

| goal | holds iff |
|------|-----------|
| `sameQuantity A B` | `A.lo = B.lo` and `A.hi = B.hi` |
| `quantityLessThan A B` | `A.hi < B.lo` |
| `quantityGreaterThan A B` | `A.lo > B.hi` |
| `quantityLessThanOrEqual A B` | `A.hi ≤ B.lo` |
| `quantityGreaterThanOrEqual A B` | `A.lo ≥ B.hi` |

So `[1,2] < 5` holds, `[1,4] < [3,6]` does not (they overlap), and `[1,2] ≤ 2` holds
while `[1,2] < 2` does not.

## Float policy: an epsilon tolerance

Cross-unit normalization multiplies a magnitude by a stored (usually floating-point)
factor, so exact `=` would make `5 Kilogram` and `5000 Gram` unequal on a last-bit
rounding difference. `provers/*quantity-tolerance*` (default `1e-9`, absolute) is the
slack: two base magnitudes are **equal** when they differ by at most it, and strict
`<` / `>` demand a gap **wider** than it — so exactly one of `<`, `=`, `>` holds for
any pair. Rebind the dynamic var for a coarser or finer policy.

## Check-only, and deferred in rules

The prover is **check-only**: it claims a comparison only when *both* arguments are
ground measures, so `(sameQuantity ?x M)` is refused — not enumerated — and appears in
no query plan. It reports `cost :lookup` and `completeness 100` (a comparison is never
a stored fact and no rule concludes one, so it is the sole complete method and the
dispatcher runs it alone).

The five comparisons are **deferred predicates** (`vaelii.impl.sentex/deferred-predicates`),
so in a rule antecedent the planner pins each after the literal that binds its measure
variable — like `evaluate` / `lessThan`:

```clojure
(implies (and (mass ?o ?q)
              (quantityGreaterThan ?q (QuantityFn 100 Kilogram)))
         (heavy ?o))
```

`(mass ?o ?q)` binds `?q` to a stored measure; the comparison is then computed against
it. Being deferred is *all* they share with the arithmetic comparisons — they are kept
out of `comparison-siblings` and `chained-comparisons`: `sameQuantity` is symmetric, not
directional, and a `quantityLessThan` chain crosses units, so folding one would smuggle
in a normalization the prover has not run.

## Where it lives

- `vaelii.impl.provers` — `QuantityProver`, `normalize-quantity`, `measure-comparisons`,
  `*quantity-tolerance*`. Registered in `default-provers`, so every KB has it.
- `resources/kb/upper/MeasureContext.txt` — the vocabulary: `QuantityFn` /
  `QuantityIntervalFn` (`unreifiableFunction`), `dimensionOf` / `conversionFactor` (the
  table predicates), and the five comparisons, each documented by a comment sentex. An
  *upper* context, not the vocabulary head: measurement is subject matter, and only the
  grammar it is declared in (`unreifiableFunction`, `binaryPredicate`, …) is CoreContext's.
- `vaelii.impl.sentex/deferred-predicates` — the five comparisons, for rule-antecedent
  planning.

## Out of scope

- Interval *arithmetic* (total or overlap duration) — that is `vaelii.impl.duration`
  ([duration.md](duration.md)), which reads `normalize-quantity` and this tolerance but
  adds nothing to either.
- Derived-unit algebra (`m/s`, `kg·m`) and transitive conversion chains.
- Binding mode: `(sameQuantity ?x M)` enumerates nothing; it is refused.

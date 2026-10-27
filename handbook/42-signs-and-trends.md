# 42. Signs and trends

- **Covers:** the sign vocabulary `measure.txt` ships (`signOf`, `trendOf`,
  `derivativeOf`, `qualitativeSum`, `qualitativeDifference`, `qualitativeProduct`,
  `greaterInMagnitudeThan`); the term a sign is stated of; which sign sentences an author
  states and which the sign prover derives; stating how a quantity changes when no figure
  is known; a dependence of one rate on another; and where sign facts sit relative to
  figures, time and contexts.
- **Not here:** measures, units and the comparison of two figures →
  [ch. 38](38-quantities.md); what holds at a moment → [ch. 35](35-change-over-time.md)
  and [ch. 39](39-time.md); how long an interval lasts → [ch. 40](40-durations.md); the
  sign tables, the fixpoint and the support a derived sign records →
  [sign.md](../docs/sign.md).
- **Assumes:** [ch. 4](04-economy.md) (**state it once**), [ch. 18](18-argument-types.md),
  [ch. 19](19-relation-properties.md), [ch. 23](23-contexts.md),
  [ch. 32](32-negation.md) (a closed extent), [ch. 39](39-time.md) (a time slice).

A common-sense KB rarely knows how fast a tap runs, and usually knows that the tap runs and
that the drain empties. The sign vocabulary states that knowledge. A quantity is negative,
zero or positive; three relations say which quantities add, subtract and multiply into
which; and the sign prover composes them into signs nobody stated. The layer holds no
figures.

## Name the quantity
*Name the quantity, not the thing*

**Practice.** Mint a term for the magnitude a sign is about: the inflow of a tap, the level
of the water in a tub, the temperature of a body. State signs and trends of that term, and
never of the tap, the tub or the body.

**Example.** `measure.txt` types every position of the vocabulary `quantity`, and places
`quantity` beside the measures:

```clojure
(arg signOf 1 quantity)
(arg signOf 2 sign_value)
(arg derivativeOf 1 quantity)
(arg derivativeOf 2 quantity)
(genl quantity aspatial)
(genl quantity temporal)
(set/monotonic (disjoint quantity situation))
```

The `comment` on `quantity` ends "A quantity is not a measure: a measure is a figure in a
unit, and a quantity is what a measure would measure."

**Why.**

- *Logical.* A sign is a property of one magnitude. A tap has several (the flow, the
  water's temperature, the pressure behind it), and a sign stated of the tap does not say
  which of them is positive.
- *Engine.* Under the entailing reading of `arg` ([ch. 18](18-argument-types.md)),
  `(signOf X S)` derives `(quantity X)`. `quantity` is below `aspatial`, and `core.txt`'s
  monotonic `(partition thing spatial aspatial)` separates it from every spatial type. A
  tub in the quantity position is therefore a definitional clash: `try-assert` refuses
  `(signOf TmpTub SignPositive)` over a believed `(container TmpTub)` with
  `:definitional-clash`, and `assert` stores the fact and places the nogood.
- *Engine.* The three values `SignNegative`, `SignZero` and `SignPositive` are the only
  members of `sign_value`, and `measure.txt` closes the extent with
  `(closed_extent_predicate sign_value)`. The prover reads them as jointly exhaustive and
  pairwise disjoint, so a set of possible signs that excludes `SignPositive` answers
  `(not (trendOf Q SignPositive))` by refutation ([ch. 32](32-negation.md)).

**Why not the other ways.** A sign stated of the object makes the object a quantity,
which clashes for every tangible object. A unary type per object and magnitude
(`tap_running`) states the same knowledge in a form the sign prover does not read, so no
sum, product or trend is ever composed from it.

**Audit.** For each term the change puts in a quantity position, `ask?` `(quantity X)` in
the change's context and review that the name says which magnitude the term is. A
`try-assert` of each new sign fact reports a clash with the term's other types.

## State the inputs
*State the inputs, and let the prover derive the composed sign*

**Practice.** State the signs known from observation or from what the quantity is, the
arithmetic relations between quantities, and a `greaterInMagnitudeThan` between the two
addends of each sum whose addends have opposite signs. Register the prover with
`(v/add-reasoner kb :sign)`. Do not state a sign that the relations already determine.

**Example.** A composed bath, its inflow faster than its outflow:

```clojure composed
(signOf TmpInflow SignPositive)
(signOf TmpOutflow SignNegative)
(qualitativeSum TmpInflow TmpOutflow TmpNetFlow)
(greaterInMagnitudeThan TmpInflow TmpOutflow)
```

`(signOf TmpNetFlow SignPositive)` is answered. Without the comparison, all three signs
remain possible for the net flow, and no sign goal about it is answered.

**Why.**

- *Engine.* The prover reads every believed sign fact, relation and comparison visible
  from the asking context into one reading. The reading narrows each quantity's set of
  possible signs until nothing changes, and the prover answers `(signOf Q S)` only when
  the set is exactly `S`. A positive plus a negative leaves all three values; a stated
  comparison gives the sum the larger addend's sign. The prover never chooses between the
  three.
- *Engine.* A derived sign carries the handles it rests on: the addends' signs, the
  relation, and the comparison when the comparison decided the result. A forward rule
  that fired on the derived sign is withdrawn when the comparison is retracted
  (`a-forward-rule-resting-on-a-derived-sign-is-withdrawn-with-the-comparison`).
- *Engine.* A stated sign that disagrees with a derived one empties a set of possible
  signs. The reading is then inconsistent, a `:sign-inconsistency` entry naming the
  emptied quantities goes to `(v/violations kb)`, and no sign goal in that context is
  answered, the stated ones included.
- *Engine.* The reading consults only stored comparisons. `greaterInMagnitudeThan` is
  declared `transitive`, so `ask?` answers A against C from A against B and B against C,
  and a sum of A and C stays ambiguous all the same.
- *Engine.* Without the registered prover, a KB stores and retrieves the sign facts as
  ordinary facts and composes none of them.

**Why not the other ways.** A sign stated for the net flow by hand records the conclusion
without its reasons: retracting the comparison leaves the stated sign standing, and a
later change to an addend turns it into a contradiction that leaves every sign goal in
the context unanswered
(**state it once**). A default-strength sign written to fill the ambiguous entry decides a
question the KB holds no information on; the comparison states the information.

**Audit.** `ask?` each sign the change expects to be composed, and for each sum among them
name the stated comparison between its addends. After the change, read
`(v/violations kb)` for a `:sign-inconsistency` entry.

## One rate per quantity
*The derivativeOf edge names the whole rate*

**Practice.** State `(derivativeOf R Q)` for the one net rate at which Q changes. When
several flows change Q, state each flow as a quantity, state their sum as the net rate,
and state one `derivativeOf` from the sum. When the rate has no name worth minting, state
`trendOf` of Q directly. State the rate of a sum as a sum of the rates.

**Example.** The bath of the previous section, with its level:

```clojure composed
(qualitativeSum TmpInflow TmpOutflow TmpNetFlow)
(derivativeOf TmpNetFlow TmpLevel)
```

`(trendOf TmpLevel SignPositive)` is answered. The `comment` on `derivativeOf` gives the
same shape: "(derivativeOf NetInflow WaterLevel) says the net inflow is how fast the water
level rises."

**Why.**

- *Engine.* `(trendOf Q S)` is the sign of Q's rate, and the prover carries the value in
  both directions along the edge. A rate with a known sign gives the quantity's trend, and
  a stated trend gives the rate's sign, which can then be an addend of another sum.
- *Engine.* Because the edge runs from the trend to the rate, two rates declared of one
  quantity take one sign. A positive inflow and a negative outflow each declared
  `derivativeOf` the level make the reading inconsistent, and the violation names the
  two flows and the level. A flow contributes to the rate, and the sum of the flows is
  the rate.
- *Engine.* No rule infers rate arithmetic from quantity arithmetic. `d(A+B) = dA + dB`
  holds, and `d(A×B)` is not a function of `dA` and `dB`, so the rate of a sum is a
  `qualitativeSum` of the rates that the author states.
- *Engine.* Arithmetic runs from the inputs to the result only. A sum's sign never gives
  an addend's sign, and the `derivativeOf` edge is the one constraint that runs both
  ways.

**Why not the other ways.** A `derivativeOf` from each flow to the level states that
each flow is the whole rate, and the KB reports the contradiction above. A `trendOf`
stated beside a rate whose sign is known restates the edge (**state it once**).

**Audit.** For each quantity the change names as the second argument of `derivativeOf`,
`query` `(derivativeOf ?r Q)`. More than one answer is a finding, unless the rates are
one rate under two names.

## A dependence between two rates
*A rate that scales another is a product*

**Practice.** When one quantity changes at a rate that follows another quantity's rate,
state the dependence as a `qualitativeProduct` of the source rate and a coefficient with a
stated sign. Use a negative coefficient for an inverse dependence. The sign vocabulary
has no influence or proportionality relation, and a dependence that is not a sum, a
difference or a product has no form in it.

**Example.** A composed body that warms while it gains heat:

```clojure composed
(derivativeOf TmpHeatRate TmpHeat)
(derivativeOf TmpTemperatureRate TmpTemperature)
(signOf TmpCoefficient SignPositive)
(qualitativeProduct TmpCoefficient TmpHeatRate TmpTemperatureRate)
(trendOf TmpHeat SignPositive)
```

`(trendOf TmpTemperature SignPositive)` is answered, and so is
`(not (trendOf TmpTemperature SignNegative))`.

**Why.**

- *Engine.* The stated trend gives the heat rate a positive sign across the first edge,
  the product of two positives is positive, and the second edge makes the temperature
  rising. A product is never ambiguous, so no comparison is needed, and a heat rate of
  `SignZero` gives a steady temperature.
- *Engine.* The dependence runs one way. A stated trend of the temperature gives its
  rate a sign, and no reverse arithmetic reaches the heat rate from the product.
- *Logical.* The coefficient is a quantity like the others and may vary while its sign
  holds. The product therefore claims only that the temperature's rate is zero exactly
  when the heat rate is, and otherwise has the heat rate's sign.

**Why not the other ways.** A forward rule from one trend to the other also runs: the
prover reads a rule-concluded `trendOf` into its reading. One rule covers one sign value,
so the dependence takes three rules, and the three restate the product table (**DRY**,
[ch. 4](04-economy.md)). A `derivativeOf` from the heat rate to the temperature states that
the heat rate is the temperature's rate of change, and the two differ in dimension.

**Audit.** For each product the change uses as a dependence, confirm a stated sign on the
coefficient, and `ask?` the dependent trend under each sign of the source. Review.

## Signs, figures and time
*A sign holds in a context, not at a moment*

**Practice.** State a sign or a trend without a time argument, in the context that holds
the situation it describes. When a quantity's trend differs between phases of one
situation, name each phase's time, and state each phase's facts in the time slice of the
situation at that time ([ch. 39](39-time.md#time-from-the-slice)). State the facts every
phase shares in the slice of the whole situation's time, and the `subintervalOf` edge from
each phase's time to it. When a figure is known, state the measure
([ch. 38](38-quantities.md)), and state the sign beside it only where sign reasoning reads
it.

**Example.** A composed bath that fills and then drains. The slice of the bath's whole time
holds the two flows' signs, their sum and the `derivativeOf` edge; each phase's slice
states one comparison:

```clojure composed
(monad_context CxTmpBath)
(subintervalOf TmpFilling TmpBathTime)
(subintervalOf TmpDraining TmpBathTime)
(meets TmpFilling TmpDraining)
(ist (CxTimeFn CxTmpBath TmpBathTime) (derivativeOf TmpNetFlow TmpLevel))
(ist (CxTimeFn CxTmpBath TmpFilling) (greaterInMagnitudeThan TmpInflow TmpOutflow))
(ist (CxTimeFn CxTmpBath TmpDraining) (greaterInMagnitudeThan TmpOutflow TmpInflow))
```

The first four sentences are stated in CxUniverse. The signs and the sum go in the whole
time's slice beside the `derivativeOf` edge. `(trendOf TmpLevel SignPositive)` is
answered in the filling slice, `SignNegative` in the draining slice, and no trend in the
slice of the whole time.

**Why.**

- *Engine.* The prover builds one reading per asking context from the facts visible there
  ([ch. 23](23-contexts.md)). A phase's slice sees the slice of the whole time through
  the stated `subintervalOf`, and the two phases' slices see nothing of each other, so
  sibling phases answer different trends from one shared theory.
- *Engine.* A slice does not see its monad: the shared facts stated in `CxTmpBath` itself
  are not read from a phase's slice
  ([ch. 39](39-time.md#time-from-the-slice), in development).
- *Engine.* A trend says nothing about when. The event calculus of
  [ch. 35](35-change-over-time.md) and the sign prover are not connected: a fluent built
  for a rising level is a term the prover never reads, and no shipped rule joins a sign
  fact to `initiates` or `terminates`.
- *Engine.* An inconsistent reading leaves every sign goal in its context unanswered. A
  slice of its own keeps one phase's contradiction out of the other phases' answers.
- *Engine.* The measure layer and the sign layer do not meet. A measure is never read into
  a sign, and a sign is never read out as a measure.

**Why not the other ways.** Both comparisons stated in one context are a cycle of an
asymmetric relation, which the KB reports as a clash. A phase context of the author's own
has no time, so nothing relates it to the phase's time or to a slice inside that time. A
trend carried inside a fluent
reaches `holdsAt` and no sum or edge. A sign left to be derived from a stated measure is
never derived.

**Audit.** For each context the change adds sign facts to, read `(v/violations kb)` for
`:sign-inconsistency`, and `ask?` each expected trend from each phase's slice.

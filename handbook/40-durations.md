# 40. Durations

- **Covers:** stating how long a thing lasts with `length`; which durations are stated
  and which are computed; asking `totalDuration` and `overlapDuration`; what an overlap
  needs before it is a figure.
- **Not here:** the measure terms, the units and the unit table →
  [ch. 38](38-quantities.md); the Allen relations and the metric gap between two
  instants → [ch. 39](39-time.md); the prover's bounds arithmetic and support →
  [duration.md](../docs/duration.md).
- **Assumes:** [ch. 4](04-economy.md), [ch. 38](38-quantities.md),
  [ch. 39](39-time.md).

`time.txt` gives an interval one stated duration, `length`, and two computed ones,
`totalDuration` and `overlapDuration`. The `:duration` reasoner computes both from the
stored lengths, the Allen relations still possible between two intervals, and the metric
gaps between their instants.

## One length per interval

**Practice.** State how long a thing lasts as `(length X M)`, with `M` a `QuantityFn`
term when the figure is known and a `QuantityIntervalFn` term when only bounds are known.
Name `X` by a symbol. State one length per thing in the contexts that read it.

**Example.** `time.txt` declares the predicate, and its `comment` says "An interval's one
primitive duration and the only quantitative fact stated about it":

```clojure
(set/monotonic (instance_relation_predicate length))
(arg length 1 temporal)
(arg length 2 measure)
```

`measure.txt` places the units a duration is written in:

```clojure
(dimensionOf Hour Duration)
(conversionFactor Hour Second 3600)
```

A composed length, for a nap known to last one to two hours:

```clojure composed
(length TmpNap (QuantityIntervalFn 1 2 Hour))
```

**Why.**

- *Engine.* The reasoner reads each `length` match whose measure is a structural measure
  term, normalizes it through the unit table, and carries it as `[lo hi]` bounds. A
  measure named by a symbol is skipped (**a figure carries its unit**,
  [ch. 38](38-quantities.md)).
- *Engine.* One length stated in two units, or in two contexts one context sees, is one
  length once normalized, in any order of arrival. Two lengths that differ once
  normalized give the thing no length, and every total over it has no answer.
- *Engine.* An interval argument of `totalDuration` or `overlapDuration` must be a
  symbol, so a calendar term has no computed duration. Nothing converts its fields to a
  magnitude.
- *Logical.* An unknown length is no length. A component with none stated gives a total
  no answer, because zero is a claim the source did not make.

**Why not the other ways.** A point figure for a length known only within bounds states
a precision the source lacks, and every total over it inherits that precision. A second,
narrower length beside a wider one is a disagreement, not a refinement: retract the
wider one.

**Audit.** With `:duration` registered, ask `(totalDuration (list X) ?d)` for each thing
the change gives a length. Each answers one measure; no answer names a missing length, a
second length that disagrees, or a measure named by a symbol.

## Computed, never stated

**Practice.** Do not assert `totalDuration` or `overlapDuration`. Register `:duration`,
state the lengths, and ask, in a goal or a rule antecedent. Ask with an open measure to
bind the answer, or with a measure in any unit of `Duration` to check it.

**Example.** The registration and a composed check, over two temporaries whose lengths
are stated in hours and minutes:

```clojure
(v/add-reasoner kb :duration)
```

```clojure composed
(totalDuration (list TmpTalk TmpPanel) (QuantityFn 150 Minute))
```

The `comment` on `totalDuration` writes its first argument as one `list` term:

```clojure
(totalDuration (list ?interval1 ?interval2 …) ?duration)
```

**Why.**

- *Engine.* `assert` refuses either predicate with `:not-well-formed`, because the
  reasoner never reads a stored one (`duration_test`'s `neither-duration-is-assertible`).
- *Engine.* An open measure binds the answer in the dimension's base unit, `Second` for
  `Duration`. A measure in hours or minutes is compared after normalization, so
  `(QuantityFn 2.5 Hour)` and `(QuantityFn 9000 Second)` check against one total.
- *Engine.* Bounds add separately: a length of one to two hours plus thirty minutes is
  `(QuantityIntervalFn 5400 9000 Second)`. Lengths in two dimensions have no total.
- *Engine.* The reasoner names the `length` facts and the unit rows each answer read, so
  a forward rule that joins on a total is withdrawn when one of them is retracted, and a
  length arriving after the rule re-joins it.

**Why not the other ways.** A stored total is a second record of the lengths that falls
out of date when one of them changes (**state it once**, [ch. 4](04-economy.md)).

**Audit.** `git grep -nE '\((totalDuration|overlapDuration) '` over the change's data
files returns only goals and rule antecedents.

## What makes an overlap a figure

**Practice.** For an overlap to be answered, state both intervals' lengths. For the
answer to be a figure and not a range, also state the Allen relation the source fixes
between them, or place their instants with `startOf`, `endOf` and `temporalDistance`
([ch. 39](39-time.md)). The metric network does not read `length`, so an interval whose
span the metric network needs also gets a `temporalDistance` between its own two
instants.

**Example.** A composed set after `duration_test`'s
`a-metric-network-turns-an-indefinite-overlap-into-a-figure`: a two hour lecture, and a
thirty minute alarm drill that begins 105 minutes into it:

```clojure composed
(length TmpLecture (QuantityFn 2 Hour))
(length TmpDrill (QuantityFn 30 Minute))
(startOf TmpLecture TmpLectureStart)
(endOf TmpLecture TmpLectureEnd)
(startOf TmpDrill TmpDrillStart)
(endOf TmpDrill TmpDrillEnd)
(temporalDistance TmpLectureStart TmpLectureEnd (QuantityFn 2 Hour))
(temporalDistance TmpDrillStart TmpDrillEnd (QuantityFn 30 Minute))
(temporalDistance TmpLectureStart TmpDrillStart (QuantityFn 105 Minute))
```

`(overlapDuration TmpLecture TmpDrill ?d)` binds `(QuantityFn 900 Second)`. With the two
lengths alone it binds `(QuantityIntervalFn 0 1800 Second)`.

**Why.**

- *Engine.* The qualitative bound reads the Allen relations still possible. Every one
  `temporallyDisjoint` gives zero; every one under `subintervalOf` gives the first
  length; every one under `hasSubinterval` gives the second; any other set gives zero up
  to the shorter length.
- *Engine.* The metric network bounds the shared stretch from the four gaps between the
  two intervals' instants, and the reasoner intersects that bound with the qualitative
  one when the dimensions match. The metric bound only narrows, so endpoint facts with no
  `temporalDistance` change nothing.
- *Engine.* The metric bound narrows the answer and does not replace a length: with every
  gap fixed and a `length` missing, `overlapDuration` has no answer.
- *Engine.* An inconsistent Allen network leaves no relation possible between the two,
  and gives no overlap at all.

**Why not the other ways.** An overlap figure the source gives directly has no predicate
to be stated in, since `overlapDuration` is computed; state the relation or the gaps that
produce it. A `temporalDistance` across an interval's own instants that disagrees with its
`length` gives two spans for one interval, and nothing reports the disagreement.

**Audit.** For each interval the change places metrically, ask `(temporalDistance S E ?d)`
between its own instants with `:metric-time` registered and compare the answer with
`(totalDuration (list X) ?d)`. For each pair whose overlap the source fixes,
`overlapDuration` binds a `QuantityFn`.

# Metric time — the simple temporal problem

`vaelii.impl.stp` is the quantitative layer under [time.md](time.md). Allen's algebra says
*that* one meeting ended before another began; the point algebra says the same about two
moments. Neither says **how long** the gap was, and neither can tell you that a train
leaving at the hour and arriving ninety minutes later cannot also arrive within the hour.

A **simple temporal problem** is a set of bounds on the gaps between timepoints,

```
lo ≤ t(Q) − t(P) ≤ hi
```

closed by all-pairs shortest paths over the distance graph they describe. The closure gives
the tightest gap the constraints entail between *any* two instants, including pairs nobody
wrote a constraint for, and a **negative cycle** is the proof that no assignment of times
satisfies them all.

## Why it is not a relation algebra

[qcn.md](qcn.md)'s engine takes an algebra as a parameter, and this is deliberately not one.
There is no finite set of jointly-exhaustive base relations, and there is no composition
table: the constraint on a pair is an interval of the reals, composition is addition, and
tightening is `min`. Forcing that shape through a table-driven path-consistency loop would
buy nothing and hide the algorithm.

What it *does* borrow is the discipline. `vaelii.impl.stp` is split down the middle in the
same place `qcn` is:

| Half | Knows about |
|------|-------------|
| the algorithm | pure data. A network is `{[p q] → [lo hi]}` and a closure is a function of it |
| the KB half | measures, the unit table, belief, context, the violations ledger, the prover |

So the closure is testable with no KB in sight, and memoizable on the network *value*, for
exactly the reason `qcn`'s pass is.

## The network and the closure

A **network** is `{[p q] → [lo hi]}`, both directions stored — `[q p]` holds `[-hi -lo]` —
and an unrecorded pair is `unbounded`, `[-∞ ∞]`. `narrow` intersects a constraint into it
(`[max of the los, min of the his]`), which is commutative and associative, so a network is
a function of the constraints alone and never of the order they arrived in.

`close` builds the distance graph — an edge `p → q` of weight `hi`, which is exactly
`t(q) − t(p) ≤ hi`, and the reverse edge of weight `-lo` — runs Floyd–Warshall over it, and
reads the result back as bounds. Two ways it answers `:inconsistent`:

* a **negative cycle**, which the closed diagonal reports: `d[p][p] < 0` says a chain of
  gaps leads from an instant back to itself having lost time.
* a constraint **unsatisfiable as written**, which no path would visit: bounds that cross
  (`lo > hi`), or a non-zero gap from an instant to itself. Both are the metric echo of
  `qcn/unsatisfiable-as-given?`, and both are checked before the pass for the same reason —
  otherwise the verdict on one self-contradicting fact would depend on how many *other*
  instants happened to be present.

As with `qcn`, passing every node the network mentions is the **caller's** obligation, and
passing extra ones is always safe: an isolated node has a finite edge in neither direction,
so it can tighten no pair and lie on no cycle.

### Both verdicts are read to the tolerance

A magnitude reaches the network multiplied by a stored conversion factor, so two spellings
of one figure arrive a last bit apart: `1.1 Hour` normalizes to 3960.0000000000005 seconds
and `66 Minute` to 3960. Held to an exact comparison, a KB that states one gap in both
units intersects them into `lo > hi` and is unsatisfiable — over two facts its own
`sameQuantity` calls equal, and with every metric goal in the context refused as the price.

So there are two lines, and they catch different things.

* **Each stated magnitude is snapped to the tolerance grid on the way in**
  (`provers/round-magnitude`), which is the same call `duration` makes on a stored `length`
  before comparing it. A separation and a duration are written the same way, so they are
  read to the same grid, and the pair above becomes one constraint.
* **`unsatisfiable-as-given?` and `negative-cycle-nodes` read to
  `provers/*quantity-tolerance*`**, the epsilon the measure comparisons themselves use, for
  the noise a *chain* accumulates rather than one a conversion introduced: ten tenths of a
  second are each exact and sum to 0.9999999999999999, which against a stated second is a
  cycle of −1.1e-16. No snapping at the boundary sees that one, because every input to it
  was already on the grid.

`point-possibilities` reads the same band when it decides a sign, which is what stops one
network from being satisfiable and its orderings undecidable at once. A contradiction wider
than the epsilon is still a contradiction: the band is what a conversion can lose, not a
licence.

## Constraints are measures

There is no numeric syntax here. A stated constraint is the ordinary ternary fact

```clojure
(temporalDistance Departure Arrival (QuantityFn 90 Minute))        ; exactly 90 minutes
(temporalDistance Departure Arrival (QuantityIntervalFn 1 2 Hour)) ; somewhere in between
```

with the measure structural NATs of [quantity.md](quantity.md), and a **negative** magnitude saying
the second instant falls first. Every magnitude normalizes through
`provers/normalize-quantity` against the KB's `dimensionOf` / `conversionFactor` table, so
constraints stated in minutes and in hours compose without anything being said about it, and
the answer is rendered back in the dimension's **base unit** — read out of the same table
the normalization used, so nothing separate can disagree with the unit the arithmetic
happened in. That is the contract [duration.md](duration.md) follows, so a separation and a
duration are written the same way and compare directly.

Constraints spanning **more than one dimension** are refused rather than mixed: `problem`
returns nil, and no metric goal is answered. Gaps in metres are not durations, and summing
them would produce a number that means nothing — the same gate `totalDuration` applies to
its components.

That refusal is **reported** to the `(violations kb)` ledger as
`:metric-temporal-mixed-dimensions`, naming the context, the dimensions and the base units
they would have been summed in. Its reach is what earns the entry: `totalDuration` refusing
a mismatched sum withdraws one goal, while this withdraws every metric goal in the context —
including gaps stated outright, in the dimension that was never in question — and it is
usually one mis-spelt unit that does it. One entry per KB and context, so a query loop says
it once.

## Bind or check

`TemporalDistanceProver` answers `(temporalDistance P Q M)` for ground `P` and `Q`:

* **bind** — an open `M` takes the tightest bound entailed, rendered as a point
  `(QuantityFn …)` when the bounds coincide and a `(QuantityIntervalFn …)` when they do not.
  Both bounds must be finite: a half-bounded gap is real knowledge but not a measure, and
  there is no honest structural NAT for it, so the goal has no answer rather than a fabricated one.
* **check** — a ground `M` is **entailed** exactly when the derived bound is *contained* in
  it. A stated bound is a weaker claim than a tighter derived one, so the derived one
  implies it: after the closure pins `P → Q` at 13 minutes, both `(QuantityFn 780 Second)`
  and the original loose `(QuantityIntervalFn 10 20 Minute)` are answered, and anything
  tighter than 13 minutes is not.

`cost` is `:compute` (a closure over the stored constraints before the first answer),
`est-bindings` is 1 (a computation has at most one answer), and `completeness` is 100 — the
answer is a property of the whole set of constraints rather than of any one stored fact, and
it entails every stated bound it is contained in, so unioning a raw fact match in would add
nothing.

The prover is **opt-in**; the vocabulary is not.

```clojure
(v/add-reasoner kb :metric-time)
```

## An unsatisfiable network is reported

A negative cycle goes to the accumulating `(violations kb)` ledger as
`:metric-temporal-inconsistency`, naming the context, the unit, the instants in the network
and the ones lying on the cycle. It is deliberately **not** a `wff` check, for the metric
reading of the three reasons [qcn.md](qcn.md) gives:

* `wff` **throws**, and the constraint it would throw on is whichever arrived last. No
  single member of a negative cycle is the wrong one — the cycle is a property of the set —
  so blaming a member would make the stored KB depend on assertion order.
* the check costs an all-pairs closure, and `wff` runs per assert. Every temporal fact would
  pay an O(n³) pass to be stored.
* the prover is opt-in. A KB that never registered it would be held to an arithmetic it
  never asked to reason with.

It is recorded on the way past, once per network **per KB and context**. The closure itself
is memoized on the network *value* and is therefore shared: two contexts seeing the same
constraints, or two KBs holding them, close it once between them. A report riding on that
pass would fire for whichever asked first and leave the rest answering nothing with an empty
ledger — so the entry hangs off `observe/newly-seen?` instead, which asks whether *this* KB
has said *this* about *this* context yet. A query loop still reports once, and a change of
belief reports again. While the network is unsatisfiable **no** metric goal is answered, not
even one that was stated outright: an unsatisfiable theory is not mined for numbers.

## The bridge: startOf and endOf

```clojure
(startOf Meeting MeetingStart)
(endOf   Meeting MeetingEnd)
```

Two binary predicates naming an interval's bounding instants. With them a metric constraint
and an Allen relation are claims about the same thing, and the metric layer can say what the
qualitative one could not.

`allen-narrowing` reads the closure back as an Allen network `{[i j] → #{base relations}}`
for a caller to intersect into one read from stored facts. It runs **one way only** —
metric narrows qualitative — asserts nothing, mutates nothing, and returns a value.

The mechanism is `endpoint-signature`: each of Allen's thirteen relations forces a specific
ordering on each of the four endpoint comparisons — A's start against B's start, A's start
against B's end, A's end against B's start, A's end against B's end. A relation survives the
narrowing while every ordering its signature demands is still possible under the closure. The
thirteen signatures are distinct, so reading them is a decision rather than a filter that
could pass two, and `stp_test` derives all thirteen a second time from numeric interval
layouts — the table and the definitions share nothing, so they can only agree by both being
right.

```clojure
;; A lasts two hours, B lasts three, and B begins an hour after A ends
(stp/allen-narrowing kb ctx)   ;=> {[A B] #{:before}  [B A] #{:after}}

;; loosen the gap to "somewhere between one and five hours after A begins"
(stp/allen-narrowing kb ctx)   ;=> {[A B] #{:before :meets :overlaps} …}
```

The reading is **sound but not sharp**: the four bounds are read independently, so a
combination of them that no single assignment of times realizes is not noticed. That can
only leave a relation in that the metric network in fact excludes, never take out one it
permits — which is the direction a narrowing must err in.

Only pairs the constraints actually narrow are recorded; a pair still open to all thirteen
is the absence of a claim. An interval missing one of its bounding instants — or with one
stated of two *different* instants, which is a disagreement no reasoning should paper over —
is not read at all.

## Sharpening an overlap

`overlap-window` is the other half of the bridge and the reason
[duration.md](duration.md)'s `overlapDuration` stops guessing. The shared stretch of two
intervals runs from the later of the two starts to the earlier of the two ends,

```
overlap = max(0, min(a-end, b-end) − max(a-start, b-start))
```

and `min(x,y) − max(p,q)` is `min(x−p, x−q, y−p, y−q)` — four gaps the closure already
bounds. A minimum lies above the least of the lower bounds and below the least of the upper
ones, so both sides carry through soundly, and clamping at zero is monotone and carries
through with them.

`duration` **intersects** what comes back with the bound it computes from the stored lengths
and the qualitative relation set. Both are sound, so their intersection is; and a KB stating
no `temporalDistance` gets the qualitative answer back untouched, which is the whole of the
compatibility guarantee — the metric layer can only narrow.

## Vocabulary

`temporalDistance` (ternary), `startOf` and `endOf` (binary) are declared in
`resources/kb/upper/TimeContext.txt` beside the interval and instant relations, each with
its own `comment` sentex. Instants and intervals are ordinary individuals; nothing declares
them, and nothing here is about clocks or calendars.

## Cost

One closure is O(n³) in the **instant** count, not in the number of constraints, and it is
memoized on the network value — so a query loop over one belief state pays for it once. The
network read is **resident on the KB** under a key of this namespace's own, stamped with the
change clock exactly as a qualitative network is ([qcn.md](qcn.md), "The network is
resident, and the clock is what makes that sound"), which
is what stops a rule joining a metric antecedent from re-reading the KB once per binding —
and a settle from re-reading it once per firing.

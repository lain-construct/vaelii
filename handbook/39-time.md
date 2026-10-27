# 39. Time

- **Covers:** choosing between an interval relation and an instant relation; placing an
  event or a situation in time; Allen's thirteen relations and the derived predicates
  that name a set of them; ordering a thing's start and end with `StartFn`, `EndFn` and
  the four bound points; the calendar constructors, `InstantFn`, `IntervalBeforeFn` and
  `IntervalAfterFn`; placing a fact in a time slice with `CxTimeFn`, `time_slice_context`,
  `monad_context`, `genlMonad`, `CxTimeOfFn`/`cxTimeOf`, `CxMonadOfFn`/`cxMonadOf` and
  `TimeIntersectionFn`; what the interval, point, calendar and metric reasoners do with a
  stated relation.
- **Not here:** fluents, `happens`, `holdsAt` and inertia →
  [ch. 35](35-change-over-time.md); how long an interval lasts →
  [ch. 40](40-durations.md); the measure terms and the unit table →
  [ch. 38](38-quantities.md); the mint of a slice's `cx/` constant and the producer that
  orders slices → [context-nat.md](../docs/context-nat.md); the path-consistency engine →
  [qcn.md](../docs/qcn.md).
- **Assumes:** [ch. 4](04-economy.md), [ch. 18](18-argument-types.md),
  [ch. 20](20-events.md), [ch. 22](22-functions.md), [ch. 23](23-contexts.md),
  [ch. 32](32-negation.md).

`time.txt` declares two qualitative algebras and the terms that join them. Allen's
interval algebra relates two things that have extent, the point algebra relates two
moments, and six point functions name the moments a thing begins and ends at. A metric
layer puts measured gaps between moments. The vocabulary is loaded into CxUniverse, and
every reasoner over it is opt-in. A time slice places a fact in time by its context
rather than by a relation. The engine's account is [time.md](../docs/time.md) and
[stp.md](../docs/stp.md).

## Interval or instant

**Practice.** Relate two things that last with an Allen predicate (`before`, `meets`,
`overlaps`, `during`, `starts`, `finishes`, `intervalEqual` and their converses), and
two moments with an instant predicate (`instantBefore`, `instantEqual`, `instantAfter`).
An event, a situation and a physical object last, and are related as themselves. Between
two events or situations, state containment with `during` or `hasSubinterval`; keep
`subintervalOf` and `properSubintervalOf` for times. Use `(TimeOfFn X)` only when the
time X occupies is itself the subject of a sentence.

**Example.** `time.txt` types the families apart, and `abstract.txt` separates a time
from what happens in it:

```clojure
(arg before 1 temporal)
(arg instantBefore 1 time_point)
(arg subintervalOf 1 time_interval)
(set/monotonic (disjoint time situation))
```

The `comment` on `instantBefore` reads "A claim about moments rather than about
intervals, which is why it is spelled apart from Allen's before."

**Why.**

- *Logical.* Two things that last compare in thirteen ways, one per ordering of their
  four endpoints. Two moments compare in three ways. An event is a happening and no
  `time`, so it is no `time_interval`.
- *Engine.* Each family is read into its own constraint network, `:allen` or `:point`.
  The interval network answers `subintervalOf` and `properSubintervalOf` only over
  arguments holding no type disjoint from `time_interval`, so a stated `during` between
  two situations answers `hasSubinterval` and neither containment (`interval_test`'s
  `containment-is-answered-only-over-time-intervals`).
- *Engine.* The point reader takes a symbol argument as a thing with extent, so
  `(StartFn Noon)` of a symbol moment `Noon` is not `Noon`. A moment named by a symbol is
  related as itself.
- *Engine.* `intervalEqual` and `instantEqual` are not `equals`. Two meetings that run
  start to finish together are two meetings, and `equals` would merge them.
- *Engine.* No network reads `timeOf`. `TimeOfFn` names a time as a term
  ([ch. 22](22-functions.md)), and an ordering is still stated over the thing.

**Why not the other ways.** `before` between two moments gives each four endpoints it
does not have. `instantBefore` between two stretches loses the cases where they touch or
nest. An interval individual minted beside each event to carry its time is a second term
for one extent (**DRY**, [ch. 4](04-economy.md)). A `subintervalOf` between two events
types each as a `time_interval`, and the argument check convicts each event.

**Audit.** Run `qualitative-network` with `:point` and with `:allen` from the change's
context and read `:nodes`: each point node names a moment, and each interval node a thing
that lasts. `git grep -n subintervalOf` over the change names no event.

## the known disjunction
*State the set of relations the source fixes, and no single relation it does not*

**Practice.** When the source fixes one of the thirteen relations, state that predicate.
When it fixes only a set, state the derived predicate that names the set: `precedes`
(before or meets), `precededBy`, `subintervalOf`, `properSubintervalOf`, `hasSubinterval`,
`sharesTimeWith` or `temporallyDisjoint`, and for moments `instantNotAfter`,
`instantNotBefore` or `instantNotEqual`. State a set none of them names as a negative
fact, or as an instant relation over the endpoints. The section specializes **strongest
form** ([ch. 4](04-economy.md)) to the strongest relation the source makes true.

**Example.** `CxChange.txt` lets an input start at the moment its event ends:

```clojure
(set/forwardRule
 (implies (and (input ?e ?x))
          (instantNotAfter (StartFn ?x) (EndFn ?e))))
```

A composed set over temporaries: breakfast is over by the time lunch starts, the meeting
and the call do not overlap, and the meeting ends first:

```clojure composed
(precedes TmpBreakfast TmpLunch)
(not (overlaps TmpMeeting TmpCall))
(instantBefore (EndFn TmpMeeting) (EndFn TmpCall))
```

**Why.**

- *Logical.* The thirteen relations are jointly exhaustive and pairwise disjoint, so a
  base relation the source did not fix is false whenever another one holds. "Breakfast
  came before lunch" allows the two to touch, and Allen's `before` does not.
- *Engine.* A stated fact intersects the pair's constraint with the predicate's set.
  `(precedes A B)` leaves `#{:before :meets}`, and a second fact intersects again, in
  either order (`interval_test`'s `a-derived-assertion-constrains-without-determining`
  and `two-facts-about-one-pair-intersect`).
- *Engine.* A goal holds when every relation still possible is in its predicate's set.
  The pair above answers `precedes` and `temporallyDisjoint`, and leaves `before` open.
- *Engine.* A believed negative fact narrows the pair to the complement of the
  predicate's set ([ch. 32](32-negation.md), [qcn.md](../docs/qcn.md)). Exactly one base
  relation holds of any pair, so "not P" is a constraint.

**Why not the other ways.** A base relation stronger than the source composes into wrong
answers about pairs nobody stated, and nothing reports them until a true fact clashes
with one. A predicate minted for an unnamed set duplicates what a negative fact or an
endpoint fact states with the shipped vocabulary.

**Audit.** For each pair the change relates, compare `possible-relations` over `:allen`
(or `:point`) with what the source allows. A smaller set names a fact stated too strongly.

## date the points
*Order a thing's start and end when a moment or a date is involved*

**Practice.** When a thing is dated, compared with a moment, or has only its start or end
compared with another thing, state an instant relation over `(StartFn X)` and
`(EndFn X)`. Date against a calendar term's points, such as `(StartFn (YearFn 2009))`.
When a start or end is known only to lie in a range, or the thing has no sharp boundary,
state the range with `EarliestStartFn`, `LatestStartFn`, `EarliestEndFn` and
`LatestEndFn`.

**Example.** `abstract.txt` orders a cause against its effect on their start points:

```clojure
(set/forwardRule
 (implies (and (causes ?cause ?effect))
          (instantNotAfter (StartFn ?cause) (StartFn ?effect))))
```

A composed dating: a prize received in 2009, while an office was held:

```clojure composed
(instantNotAfter (StartFn (YearFn 2009)) (StartFn TmpPrize))
(instantNotAfter (EndFn TmpPrize) (EndFn (YearFn 2009)))
(instantNotAfter (StartFn TmpOffice) (StartFn TmpPrize))
(instantNotAfter (EndFn TmpPrize) (EndFn TmpOffice))
```

**Why.**

- *Engine.* The point network takes the point terms as nodes and adds the order the terms
  fix: `(StartFn X)` before `(EndFn X)`, each bound on its side of the point it bounds,
  and calendar points sorted by their fields. Nothing is minted. `timepoint_test`'s
  `dated-clues-stitched-together` bounds when an office began and ended from dated clues.
- *Engine.* The Allen relations between two things follow from their points, and the
  reading runs one way: a stated `(before A B)` says nothing about `(EndFn A)`.
- *Engine.* A calendar term is not a node of the interval network. A stated
  `(before TmpBreakfast (MonthFn 2000 1))` does not compose with the clock's ordering of
  January before March.
- *Engine.* With `:includes-instant` registered, `argue` answers `(includesInstant X t)`
  `:true`, `:false`, or `:unknown` for a moment inside a range a bound leaves open.
- *Logical.* "In 2009" puts the prize at or after the year's start and at or before its
  end. A prize given on the first of January `starts` the year and is not `during` it.

**Why not the other ways.** An Allen fact between a thing and a calendar term composes
with nothing the clock computes. The predicates corresponding to the bound functions
order nothing: the `implementationNote` on `earliestStartOf` says "a stated earliestStartOf
fact orders nothing". One invented date for a boundary without a sharp edge states a
precision the source lacks.

**Audit.** `qualitative-network` over `:point` reports `:consistent? true` from the
change's context. For each date the source gives, `argue` over `includesInstant` at a
moment inside the dated range answers `:true`.

## Calendar terms

**Practice.** Name a year, month or day with `YearFn`, `MonthFn`, `DayFn` or the ISO
spelling `DatetimeFn`, and a moment with the six-field `InstantFn`. Do not mint an
individual for a calendar period. Do not state a calendar term's endpoints or a relation
between two calendar terms: register `:calendar` and ask. Name the time before a moment
`W` with `(IntervalBeforeFn W)` and the time from `W` on with `(IntervalAfterFn W)`.

**Example.** `time.txt` keeps the constructors structural and types their values:

```clojure
(unreifiable_function YearFn)
(result YearFn time_interval)
(arity InstantFn 6)
(result InstantFn time_point)
```

**Why.**

- *Engine.* An unreifiable application is never minted, so its fields stay readable
  ([ch. 22](22-functions.md)). The clock computes `startOf` and `endOf` from them and
  orders two terms by comparing their fields. The answer is never stored.
- *Engine.* A term ends at the first moment of the next term at its precision.
  `(endOf (YearFn 1999) ?i)` and `(startOf (YearFn 2000) ?i)` both answer
  `(InstantFn 2000 1 1 0 0 0)`, so consecutive years `meet`. `precedes` is the relation
  "1999 came before 2000" means. `InstantFn` takes six fields always, so every moment
  has one spelling.
- *Engine.* A clock answer rests on no stored fact, so a forward rule derives nothing
  from it. An ordering goal reaches the clock only with both terms bound; the one
  variable the clock binds is the instant of a `startOf` or `endOf` goal.
- *Engine.* Every interval includes its start and excludes its end, so
  `(IntervalBeforeFn W)` and `(IntervalAfterFn W)` meet at `W`, and `W` belongs to the
  after side alone. A backward rule in `time.txt` answers `(endOf (IntervalBeforeFn W) W)`
  and `(startOf (IntervalAfterFn W) W)` when `W` is a believed `time_point`. An
  `InstantFn` term is no believed `time_point`, so for an `InstantFn` moment the bound is
  stated.

**Why not the other ways.** An individual standing for the year 2000 has no fields, so
nothing computes its endpoints or places it inside its century. A stated
`(startOf (YearFn 2000) K)` is a second answer beside the computed one
([time.md](../docs/time.md), "The calendar clock"). `happens` takes a moment, so it takes
an `InstantFn` and refuses a `DayFn` ([ch. 35](35-change-over-time.md)).

**Audit.** `git grep -nE '\((startOf|endOf) \((YearFn|MonthFn|DayFn|DatetimeFn)'` over
the change returns only goals. Review each new individual whose name spells a date.

## time from the slice
*A fact that holds for a time takes the time from its context*

**Practice.** When the source says that a fact holds over a stated time, such as a status
during one month or a membership during one year, state the fact in the time slice
`(CxTimeFn M T)`: the context `M` at the time `T`. `M` is the monad, the world, story or
theory the fact belongs to; state `(monad_context M)` of each monad. Key the slice by a
calendar term, or by a named `time_interval` whose `subintervalOf` edges to the other
named times are stated. The predicate keeps no time argument: a time-dependent predicate
takes its time from the context. A relation whose own argument is a time, as `happens`
takes the moment of an event, states the time in that argument and is not sliced. The KB
has no declaration that marks an argument as the time, so the relation's `comment` says
which argument it is.

**Example.** `time.txt` declares the slice function and the two orderings of its
applications:

```clojure
(result CxTimeFn time_slice_context)
(contextArgSubrelation CxTimeFn 1 genlMonad)
(contextArgSubrelation CxTimeFn 2 subintervalOf)
```

A composed tracker over temporaries, a status in September and another in October:

```clojure composed
(monad_context CxTmpTracker)
(ist (CxTimeFn CxTmpTracker (MonthFn 2026 9)) (tmpStatusOf TmpPr TmpDraft))
(ist (CxTimeFn CxTmpTracker (MonthFn 2026 10)) (tmpStatusOf TmpPr TmpOpen))
```

The `monad_context` sentence is stated in CxUniverse. `(ist C S)` stores `S` in the
context `C` from whichever context states it, and `assert` with the slice as its context
argument stores the same sentex. A read from October's slice, or from the slice of a day
in October that holds a fact of its own, answers `TmpOpen`. A read from September's slice
answers `TmpDraft`, and `argue` there gives `(tmpStatusOf TmpPr TmpOpen)` `:unknown`.

**Why.**

- *Logical.* A slice states what holds in the monad during its time, so "Draft in
  September" and "Open in October" are two true sentences over one predicate. Neither is
  the denial of the other.
- *Engine.* An application written in a sentex's context slot reifies to a `cx/`
  constant. `time.txt` states `(result CxTimeFn context)` in CxUniverse, so a read naming
  the application resolves to the same constant
  (`temporal_capability_test/a-read-naming-a-time-slice-answers-once-cxtimefn-is-declared`).
- *Engine.* The structural `genlCx` producer orders two slices of one monad by
  `subintervalOf` on the time: the slice at the narrower time sees what the wider one
  states, and two slices at sibling times see nothing of each other
  (`temporal_capability_test/a-fact-in-a-year-slice-holds-in-its-months-and-is-unknown-the-next-year`,
  `temporal_capability_test/sibling-month-slices-do-not-see-each-other`). A calendar term
  is ordered by its fields, and a named interval by a stated `subintervalOf`
  (`temporal_capability_test/a-fact-in-a-named-year-slice-is-visible-from-a-named-month-inside-it`).
- *Engine.* A stated `(genlMonad M1 M2)` orders two slices at one time the same way: the
  slice along `M1` sees the slice along `M2`
  (`temporal_capability_test/a-fact-in-a-super-monads-slice-holds-along-its-sub-monad-and-is-unknown-along-an-unrelated-monad`).
  A rule stated in a wider slice runs in the narrower one
  (`temporal_capability_test/a-rule-stated-in-a-year-slice-runs-in-its-month-slice`).
- *Engine.* A fact in a slice is read from that slice, from the slices at times inside
  its time, and from the slice at its time along a sub-monad. No rule carries it into a
  later slice, so a status read after its stretch is unknown, and not still current.
- *Engine.* `CxMonadOfFn` and `CxTimeOfFn` take a slice apart, with `cxMonadOf` and
  `cxTimeOf` as their predicates. A slice of a slice covers `(TimeIntersectionFn T1 T2)`,
  the time the two times share, when the inner slice is written as its `cx/` constant
  (`temporal_capability_test/a-slice-of-a-slice-covers-the-intersection-of-the-two-times`).

**Why not the other ways.** A time argument added to the predicate gives each relation its
own time, and no context ordering reads it: a read at a day has to join the argument
against the clock, and a `functional` mark compares the values of every time
([ch. 19](19-relation-properties.md#functional)). A fluent read with `holdsAt`
([ch. 35](35-change-over-time.md)) states a state that events start and end, and inertia
carries it forward past the last event; a slice states the time the source gives and
carries nothing forward. A context of the author's own for each period has no time in
it, so the producer orders it under no wider time and over no day inside it.

**Audit.** For each predicate in the change whose truth depends on the time, `git grep`
its facts, and confirm that each one sits in a slice or that the source bounds its time
nowhere. For each slice, `ask?` from it a fact of a wider slice of its monad.

*In development:* four readings of a slice are in development, each held by a red test in
`temporal_capability_test`:

- A slice sees neither its monad nor CxUniverse, so no declaration, mark, rule or
  definitional check stated there is read inside a slice
  (`a-slice-sees-its-monad-and-the-monad-does-not-see-the-slice`,
  `a-fact-stated-unsliced-holds-in-every-year-slice`). A theory a slice reads reaches it
  only from a wider slice of the same monad.
- A slice that holds no fact of its own sees nothing
  (`a-slice-nobody-wrote-into-still-inherits`).
- A slice keyed by an instant is not ordered under the slice of an interval that holds
  the instant
  (`a-fact-in-a-year-slice-holds-at-an-instant-inside-it-and-is-unknown-at-an-instant-of-the-next-year`).
- The producer reads a stated `subintervalOf` or a calendar term's fields, and no Allen
  answer, so a slice at an entailed intersection sees neither stretch
  (`partially-overlapping-slices-and-their-intersection`).

## What the reasoners do with a stated relation

**Practice.** Register the reasoners the application asks questions of. State each
relation once, at the pair the source names, and let composition relate the rest. For a
measured gap, name each interval's two instants with `startOf` and `endOf`, and state
`temporalDistance` between those instants.

**Example.** Each reasoner is registered by name:

```clojure
(v/add-reasoner kb :allen :point :calendar :includes-instant :metric-time)
```

A composed metric set after [stp.md](../docs/stp.md): a fifteen minute standup, an
hour's gap, a thirty minute review:

```clojure composed
(startOf TmpStandup TmpStandupStart)
(endOf TmpStandup TmpStandupEnd)
(startOf TmpReview TmpReviewStart)
(endOf TmpReview TmpReviewEnd)
(temporalDistance TmpStandupStart TmpStandupEnd (QuantityFn 15 Minute))
(temporalDistance TmpStandupEnd TmpReviewStart (QuantityFn 1 Hour))
(temporalDistance TmpReviewStart TmpReviewEnd (QuantityFn 30 Minute))
```

With `:allen` registered, `(before TmpStandup TmpReview)` is answered with no Allen
relation stated.

**Why.**

- *Engine.* A stated relation narrows one pair, path consistency carries the narrowing
  to the other pairs, and a goal reads the tightened network. A forward rule joining on
  an entailed relation rests on the facts the entailment used, and retracting one of
  them withdraws the conclusion.
- *Engine.* An unsatisfiable network is reported, not refused: `violations` receives a
  `:qualitative-inconsistency` or `:metric-temporal-inconsistency` entry, and no goal
  naming a node of the unsatisfiable component is answered. No single fact of a cycle is
  the wrong one, so refusing the last arrival would make the KB depend on order.
- *Engine.* The metric reasoner closes the `temporalDistance` facts by shortest paths and
  narrows the Allen network, one way. Its nodes are symbols, so a point term or an
  `InstantFn` is no node of it, and an interval is read only when both its `startOf` and
  `endOf` are stated. Gaps in two dimensions in one context are refused as a whole
  (`:metric-temporal-mixed-dimensions`, [ch. 38](38-quantities.md)).
- *Engine.* `instantBefore` and `instantAfter` are declared `transitive`, so a chain of
  orderings is answered by the closure with no reasoner registered.

**Why not the other ways.** A relation stated for a pair the network already entails is
a second source for one belief (**state it once**, [ch. 4](04-economy.md)), and it keeps
the pair related after the facts it followed from are retracted.

**Audit.** After a load, read `violations` for a temporal entry, and read
`qualitative-network` over `:allen`: `:unsatisfiable-sources` names the point or metric
facts behind an unsatisfiable component. Review each stated relation whose pair the
change also joins through a third node, and keep it only when the source states it
directly.

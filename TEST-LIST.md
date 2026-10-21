# Temporal and monad context reasoning: test list

Every test in `test/vaelii/temporal_capability_test.clj`, 85 in all: 60 **red** (asserts the behaviour vaelii ought to have, fails today, runs only under `lein test :red`) and 25 **green** (passes today, runs in the default suite). A comment follows a name only where the name doesn't say enough by itself.

The 54 numbered tests are the ones Iris's rulings of 2026-10-21 were made over. Each twin those rulings ask for is listed under its original, tagged with the rule it answers: R2 calendar ↔ reified, R3 DatetimeRangeFn ↔ named bounds, R4 shared super-monad, R5 interval ↔ point, R6 genlCx ↔ genlMonad, R7 time dimension ↔ monad dimension, R8 in a spec of CxNow. TEMPORAL-MATRIX.md has the inventory: for each numbered test and each rule, the twin, or why there is none. In the test file each twin sits next to its original.

## Time slices

1. `cxtimefn-is-declared-in-the-shipped-kb`: **red**
2. `a-write-into-a-time-slice-stores-in-a-cx-context`: green
3. `a-read-naming-a-time-slice-answers-once-cxtimefn-is-declared`: green
4. `a-fact-in-a-year-slice-is-visible-from-its-month`: green
    - R2: `a-fact-in-a-named-year-slice-is-visible-from-a-named-month-inside-it`: green
5. `a-slice-nobody-wrote-into-still-inherits`: **red**. Today a read never mints a context, so an unwritten slice sees nothing.
    - R2: `a-named-slice-nobody-wrote-into-still-inherits`: **red**
6. `a-fact-in-a-year-slice-holds-in-its-months-and-is-unknown-the-next-year`: green
    - R2: `a-fact-in-a-named-year-slice-holds-in-a-named-month-and-is-unknown-the-named-next-year`: green
7. `a-fact-stated-unsliced-holds-in-every-year-slice`: **red**. "Eternally" means stated unsliced, in CxUniverse.
8. `a-slice-along-a-monad-under-cxwell-sees-cxwell-and-not-the-reverse`: **red**
9. `sibling-month-slices-do-not-see-each-other`: green
    - R2: `sibling-named-month-slices-do-not-see-each-other`: green
10. `two-spellings-of-one-month-see-each-others-facts`: **red**. The two spellings are `(MonthFn 2000 1)` and `(DatetimeFn "2000-01")`.
    - R2: `two-names-of-one-interval-see-each-others-facts`: **red**
11. `two-spellings-of-one-month-name-one-context`: **red**. Same pair, but the test requires one `cx/` constant, not just mutual visibility.
    - R2: `two-names-of-one-interval-name-one-context`: **red**
12. `partially-overlapping-slices-and-their-intersection`: **red**. Named intervals related by Allen facts. The intersection slice has to be ordered from an *entailed* `subintervalOf`.
13. `a-narrative-in-a-time-slice-gets-the-event-calculus`: **red**. The slice should see CxChange through its monad.
    - R2: `a-narrative-dated-by-calendar-moments-in-a-time-slice-gets-the-event-calculus`: **red**
14. `a-fact-in-a-year-slice-holds-in-a-slice-keyed-by-an-instant-inside-it`: **red**. Homogeneity going downward: a slice keyed by an `InstantFn` point. Going upward doesn't hold, by design.
    - R2: `a-fact-in-a-named-year-slice-holds-in-a-slice-keyed-by-a-named-moment-inside-it`: **red**
15. `a-slice-keyed-by-an-intermittent-time-sits-between-its-pieces-and-its-whole`: **red**. Uses the weekends of 2000, ordered by `partOf` rather than `subintervalOf`.
    - R2: `a-slice-keyed-by-an-intermittent-time-sits-between-its-named-pieces-and-its-named-whole`: **red**

## Ranges (`time_interval` given by its bounds)

16. `a-fact-in-a-range-is-visible-from-a-subrange-and-from-each-calendar-term-inside-it`: **red**. A range is a named `time_interval` whose `startOf` and `endOf` are stated as `InstantFn` moments, since no shipped constructor names a range.
    - R2: `a-fact-in-a-range-bounded-by-named-moments-is-visible-from-each-named-time-inside-it`: **red**
17. `a-range-inside-a-month-sees-the-month-and-its-year`: **red**
    - R2: `a-range-bounded-by-named-moments-inside-a-named-month-sees-the-month-and-its-year`: **red**
18. `two-partially-overlapping-ranges-and-their-intersection`: **red**. Jan–Jun and Apr–Sep 2000. No relation is stated between them: the ordering comes from the bounds alone.
    - R2: `two-partially-overlapping-ranges-bounded-by-named-moments-and-their-intersection`: **red**
19. `a-range-and-a-calendar-term-with-the-same-bounds-name-one-context`: **red**
    - R2: `two-ranges-with-the-same-named-bounds-name-one-context`: **red**

## Monad

20. `a-slice-sees-its-monad-and-the-monad-does-not-see-the-slice`: **red**
21. `slices-along-two-monads-do-not-see-each-other`: green. The two monads are unrelated, with no common super-monad.
    - R2: `slices-along-two-monads-keyed-by-named-times-do-not-see-each-other`: green
22. `the-monad-vocabulary-is-declared-in-the-shipped-kb`: **red**. Covers `genlMonad`, `monad_context`, `CxTimeOfFn`/`cxTimeOf` and `CxMonadOfFn`/`cxMonadOf` (#181).
23. `a-slice-along-a-sub-monad-sees-the-same-time-along-its-super-monad`: **red**
24. `a-slice-sees-a-monad-two-genlmonad-steps-up`: **red**. `genlMonad` is transitive. This is the monad twin of entailed rather than stated containment.
25. `genlcx-between-slices-is-genlmonad-times-time-containment`: **red**. Checks all 12 ordered pairs over 2 monads × 2 times.
    - R2: `genlcx-between-slices-over-named-times-is-genlmonad-times-time-containment`: **red**
26. `sibling-sub-monads-each-see-their-super-monad-and-not-each-other`: **red**
27. `a-monad-below-two-monads-sees-both-at-the-same-time`: **red**. The monad twin of the intersection test.
28. `genlmonad-between-two-monad-contexts-is-their-genlcx`: **red**. Checks both directions.
29. `cxtimeof-and-cxmonadof-take-a-slice-apart-and-cxtimefn-puts-it-back`: **red**
30. `a-monad-context-is-its-own-monad-and-its-time-is-unbounded`: **red**
    - R2: `a-monad-context-is-its-own-monad-and-its-time-contains-named-intervals`: **red**
31. `monad-context-types-cxtimefns-first-argument`: **red**. Refuses `(CxTimeFn CxNow …)` and a CxTimeFn whose first argument is itself a slice.
32. `a-slice-of-a-slice-is-the-slice-of-its-monad-at-the-narrower-time`: **red**
    - R2: `a-slice-of-a-slice-at-a-named-narrower-time-is-the-slice-of-its-monad-there`: **red**

## CxNow and temporal projection

Here "now" is `(CxTimeOfFn CxNow)`, and it is reached only through lower-bound clock readings, `(instantNotBefore now T)`.

33. `a-fact-true-now-is-true-in-the-real-worlds-present-and-not-timelessly`: green. CxRealWorldNow sees CxNow and CxRealWorld, and nothing above CxNow sees what CxNow states.
34. `cxrealworldnow-is-the-real-world-at-the-present`: **red**. Its `cxMonadOf` is CxRealWorld and its `cxTimeOf` is now.
35. `a-later-clock-reading-supersedes-an-earlier-one`: **red**. A Saturday reading, then a Sunday one. After both, `earliestStartOf now` answers only Sunday's reading.
    - R2: `a-later-reading-at-a-named-moment-supersedes-an-earlier-one`: **red**
36. `with-no-clock-reading-the-present-is-unknown`: green, by design.
    - R2: `with-no-clock-reading-the-present-is-unknown-against-a-named-moment`: green
37. `an-exact-present-and-a-dated-present-tense-fact-are-refused-in-cxnow`: **red**. "It is 3:41" and "today is Saturday" are both refused, while a reading is accepted.
    - R2: `an-exact-present-and-a-present-tense-fact-at-named-times-are-refused-in-cxnow`: **red**
38. `age-is-derived-as-a-lower-bound-and-never-as-an-exact-value`: **red**. A person born in 1977, read at 2026-10-17, is at least 48, and 49 is unknown. A later reading raises the bound. `ageAtLeast`/`ageOf` are placeholder names.
39. `a-reading-places-now-after-a-past-year-and-inside-no-year`: **red**. There's no upper bound, so not even 2026 is known to contain now.
    - R2: `a-reading-at-a-named-moment-places-now-after-a-named-past-year-and-inside-no-named-year`: **red**
40. `a-past-slice-of-the-real-world-sees-the-real-world-and-not-what-holds-now`: **red**
41. `an-eternal-fact-is-visible-from-now-and-from-every-slice`: **red**
42. `a-fluent-started-in-a-past-slice-holds-now`: **red**. Projection by inertia. A plain fact from 2000 is not projected.
    - R2: `a-fluent-started-at-a-named-moment-in-a-past-named-slice-holds-now`: **red**
43. `a-fluent-ended-after-the-past-slice-does-not-hold-now`: **red**. The fluent is ended in 2005, before the reading.
    - R2: `a-fluent-ended-at-a-named-moment-before-the-reading-does-not-hold-now`: **red**
44. `a-fluent-ended-after-the-reading-is-not-known-to-hold-now`: **red**. The fluent is ended in 2030, after the reading, so whether it holds now is unknown.
    - R2: `a-fluent-ended-at-a-named-moment-after-the-reading-is-not-known-to-hold-now`: **red**
45. `projection-from-now-into-a-dated-future-slice-is-unknown-with-only-lower-bounds`: green, by design. Under lower bounds no dated slice is known to lie after now. This is an open question for the spec.
    - R2: `projection-from-now-into-a-named-future-slice-is-unknown-with-only-lower-bounds`: green

## CxChange

46. `a-state-that-goes-draft-ready-draft-follows-both-transitions`: green
    - R2: `a-state-dated-by-calendar-moments-goes-draft-ready-draft-and-follows-both-transitions`: green
47. `clipped-reads-an-order-the-point-prover-entails-once-it-is-registered`: green

## Provers

48. `the-calendar-clock-is-opt-in`: green
49. `the-instant-inclusion-reader-is-opt-in`: green
    - R2: `the-instant-inclusion-reader-is-opt-in-for-calendar-terms`: green

## Limits docs/time.md lists, now asserted as they ought to work

50. `a-stated-allen-relation-constrains-the-points`: **red**. From `(before A B)` it should follow that A's end comes before B's start.
    - R2: `a-stated-allen-relation-between-calendar-terms-constrains-their-points`: green
51. `a-calendar-term-is-a-node-of-the-allen-network`: **red**
    - R2: `a-stated-relation-composes-with-a-stated-relation-between-named-months`: green
52. `a-conjunction-that-binds-the-calendar-term-elsewhere-answers`: **red**. The planner should run the stored literal before the open calendar one.
    - R2: `a-conjunction-over-a-named-month-binds-it-from-the-stored-fact`: green
53. `a-forward-rule-fires-on-a-clock-answer`: **red**
    - R2: `a-forward-rule-fires-on-a-stated-subinterval`: green
54. `metric-gap-and-length-for-calendar-terms`: **red**

## Pinned limits (green because the limit is intended)

- 36 and 45 above. Both follow from Iris's ruling that "now" is reached only through lower bounds.
- 48 and 49, plus the without-`:point` half of 47. The temporal provers are opt-in by design (docs/time.md).
- 6 (unknown in 2001), 9 and 21 pin isolation that is correct: sibling times and unrelated monads see nothing of each other.
- `happens` at a day (`common_sense_test.clj:665`) stays a correct-by-design limit and isn't in this namespace.

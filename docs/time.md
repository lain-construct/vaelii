# Temporal reasoning — intervals, instants, and metric time

- **Covers:** Allen's thirteen interval relations and the three-relation point
  algebra, the two qualitative temporal algebras, and their composition tables.
- **Not here:** the generic path-consistency engine both algebras run on →
  [qcn.md](qcn.md); how long an interval lasts, and how long two overlap →
  [duration.md](duration.md); the numeric gap between two instants →
  [stp.md](stp.md).
- **Assumes:** base relation, relation algebra, constraint network →
  [glossary.md](glossary.md).

Time is the one subject in this tree with layers. Four namespaces, most qualitative first:

| Namespace | Unit | Says | Doc |
|-----------|------|------|-----|
| `vaelii.impl.interval` | intervals | how two stretches of time are ordered and overlap | this page |
| `vaelii.impl.point` | instants | which of two moments came first | this page |
| `vaelii.impl.stp` | instants | how *far apart* two moments are, in real units | [stp.md](stp.md) |
| `vaelii.impl.duration` | intervals | how *long* one lasts, and how long two overlap | [duration.md](duration.md) |

The first two are relation algebras over the constraint-network engine in [qcn.md](qcn.md).
The engine, the reader, the entailment reading and the prover shape are all documented there
and are identical for both; this page is the two algebras. The bottom two put numbers on
them, and `startOf` / `endOf` are what let the numbers and the orderings be about the same
thing.

Every prover here is **opt-in**; none of the vocabulary is.

## The interval algebra (`vaelii.impl.interval`)

The unit is an **interval**, not an instant. A meeting, a reign, a journey — something
with a start and an end — so two of them can meet, overlap or nest, which is exactly the
structure a point calculus throws away. The interval relations are declared `(argIsa …
temporal_thing)` and the instant relations `(argIsa … time_point)`, `time_point` sitting
under `temporal_thing`, so `startOf` and `endOf` bridge the two by declaration as well as
by meaning. A temporal relation between two predicates is refused rather than stored.
Nothing here is about clocks or calendars — only order and containment.

How *long* an interval is, and how long two of them overlap, is the quantitative half:
[duration.md](duration.md), which consumes the relation sets this page produces.

## The thirteen base relations

Jointly exhaustive and pairwise disjoint, so exactly one holds of any two intervals.
Writing an interval as `[start end]` with `start < end`, each is a claim about how the
four endpoints compare:

| Keyword | Predicate | Endpoints | Converse |
|---------|-----------|-----------|----------|
| `:before` | `before` | `a-end < b-start` | `:after` |
| `:meets` | `meets` | `a-end = b-start` | `:met-by` |
| `:overlaps` | `overlaps` | `a-start < b-start < a-end < b-end` | `:overlapped-by` |
| `:finished-by` | `finishedBy` | `a-start < b-start`, `a-end = b-end` | `:finishes` |
| `:contains` | `contains` | `a-start < b-start`, `a-end > b-end` | `:during` |
| `:starts` | `starts` | `a-start = b-start`, `a-end < b-end` | `:started-by` |
| `:equal` | `intervalEqual` | `a-start = b-start`, `a-end = b-end` | itself |
| `:started-by` | `startedBy` | `a-start = b-start`, `a-end > b-end` | `:starts` |
| `:during` | `during` | `a-start > b-start`, `a-end < b-end` | `:contains` |
| `:finishes` | `finishes` | `a-start > b-start`, `a-end = b-end` | `:finished-by` |
| `:overlapped-by` | `overlappedBy` | `b-start < a-start < b-end < a-end` | `:overlaps` |
| `:met-by` | `metBy` | `a-start = b-end` | `:meets` |
| `:after` | `after` | `a-start > b-end` | `:before` |

`:equal` is the algebra's identity and its own converse; the other twelve are six converse
pairs. `intervalEqual` is deliberately not spelled `equals`: it is a claim about extent in
time, not about the identity of two terms, so it must not reach the equality closure —
two distinct meetings can run start to finish together without being one meeting.

Seven **derived** predicates each name a disjunction:

| Predicate | Denotation |
|-----------|-----------|
| `precedes` | before, meets |
| `precededBy` | after, met-by |
| `subintervalOf` | during, starts, finishes, equal |
| `properSubintervalOf` | during, starts, finishes |
| `hasSubinterval` | contains, started-by, finished-by, equal |
| `sharesTimeWith` | the nine relations under which two intervals share time |
| `temporallyDisjoint` | before, after, meets, met-by |

`precedes` is the ordering that does not care whether the two touch — the thing people
usually mean by "before". `subintervalOf` contains `:equal`, so it holds of an interval
and itself, where `properSubintervalOf` does not. The last two are exact complements.

All twenty are declared `binaryPredicate` in `resources/kb/upper/CxTime.txt`, beside the
six instant predicates and the metric ones, each with its own `comment` sentex — an **upper**
context rather than the vocabulary head, because they are *about* time and CxCore holds
only the grammar they are stated in.

## The composition table, and why it is checked

`allen-composition` is the canonical 13×13 table: `[r1 r2]` gives the relations possible
between A and C given `r1`(A,B) and `r2`(B,C). `compose` lifts it to relation *sets* by
union — a disjunction on either side admits every combination.

Unlike the cardinal directions, which compute composition from two independent axis
projections and so cannot disagree with themselves, this table is **transcribed**. A
mistyped entry would not crash and would not return nothing: it would be a wrong
entailment, reported with full confidence, about a pair nobody asserted anything for.
Nothing downstream could catch it.

So the table is written twice. The source holds the table; `interval_test` holds the
thirteen relations as their **endpoint inequalities** and derives the whole table from
them, by laying out three intervals every way three intervals can be laid out and
recording which outer relation each layout admits. Six points suffice: a layout is a weak
ordering of six endpoints, so it needs at most six distinct values. The test asserts the
derived table equals the transcribed one, entry for entry. The two representations share
nothing, so they can only agree by both being right — and the derivation caught a real
transcription error on the first run.

The table is written out of thirteen named blocks rather than 169 loose sets, because that
is what its entries are. Composing two relations pins some of the four endpoint
comparisons between the outer intervals and leaves the rest free; each block is the set of
relations agreeing on what got pinned. `ends-first` is the five relations with
`a-end < c-end`, `same-start` the three with `a-start = c-start`, `concurrent` the nine
that share any time at all. An entry therefore says *which comparison survived*, and can
be read back against the endpoint definitions instead of merely trusted.

Only three entries are the whole universe, and they are the same shape twice over: two
intervals positioned against a third that constrains neither against the other. A before B
with C after B says nothing — both sit on the far side of B, in either order — and neither
does A during B with B containing C, where A and C are both loose inside B.

## Reading the KB, and reading an answer back

`core/qualitative-network kb :allen ctx` reads every asserted interval relation visible
from a context into a network, and the registered `:allen` prover answers a goal by
entailment; both are exactly the shape [qcn.md](qcn.md) describes. So `(before A B)` and `(before B C)` entail `(before A C)`,
and `(during A B)` with `(during B C)` entails `(during A C)` and the weaker
`(subintervalOf A C)` and `(sharesTimeWith A C)` with it.

Where the derived predicates earn their place is a network that pins something without
pinning a base relation. `(meets A B)` and `(metBy B D)` force A and D to end at the same
moment and say nothing about where they start, leaving `#{:finishes :finished-by :equal}`:
no base predicate is entailed, and `sharesTimeWith` is.

`core/possible-relations kb :allen ctx i1 i2` is the algebra read directly rather than
through a goal — the base relations still possible between two intervals, `#{}` when the
network is inconsistent. That is the call for a consumer that needs to know *how much* is
pinned down rather than whether one named relation is entailed: a singleton is a pinned
ordering, and several members are a genuinely open one.

For one concrete arrangement rather than the sets — a timeline to draw, an example to show —
`vaelii.impl.scenario` picks a single relation per pair out of the tightened network. It is
calculus-generic, so it runs over the point algebra below and the spatial ones alike. See
[scenario.md](scenario.md).

## The point algebra (`vaelii.impl.point`)

The other unit, and the smaller one. A moment has no extent, so the only question about two
instants is which came first — three base relations, jointly exhaustive and pairwise
disjoint:

| Keyword | Predicate | Holds when | Converse |
|---------|-----------|-----------|----------|
| `:before` | `instantBefore` | `t(a) < t(b)` | `:after` |
| `:equal` | `instantEqual` | `t(a) = t(b)` | itself |
| `:after` | `instantAfter` | `t(a) > t(b)` | `:before` |

Three **derived** predicates, each the complement of one base relation — and over a
jointly-exhaustive triple a complement *is* a negation, so the names are literal:

| Predicate | Denotation | Reads as |
|-----------|-----------|----------|
| `instantNotAfter` | before, equal | at or before, the ≤ of time |
| `instantNotBefore` | after, equal | at or after, the ≥ |
| `instantNotEqual` | before, after | a different moment |

With them the vocabulary names every disjunction the algebra can express bar the universe,
which is the absence of a claim and needs no name.

Every name carries the `instant` prefix because `before` and `after` already belong to the
intervals, and a moment ordered against a moment is a different claim from a stretch ordered
against a stretch. `instantEqual` is not `equals` for the reason `intervalEqual` is not: it
is a claim about time, not about the identity of two terms.

The composition table is nine entries, and only two of them lose information — a before b
with b after c puts both a and c on the far side of b, in either order, so nothing at all
follows. Everything else is a singleton, which is why a chain of strict orderings composes to
a strict ordering however long it is. `point_test` derives all nine a second time from
numeric instants.

For three relations path consistency is not merely sound but **complete**: the point
algebra's full disjunctive form is tractable, and a network of it that survives the pass has
a model. So an emptied constraint means genuine unsatisfiability — a cycle of strict
`instantBefore` facts is a reportable contradiction and not a suspicion.

**The same algebra appears twice in this tree.** `vaelii.impl.orientation` composes two
independent one-dimensional projections to get the nine cardinal directions, and each
projection is exactly these three relations under the spellings `:lt` / `:eq` / `:gt`. The
table is duplicated rather than shared: there the three relations are a position on an axis
and a private detail of a nine-relation algebra, here they are an order in time with their
own vocabulary. Nine identical entries are cheaper than the coupling, and either copy is
checkable against its own definitions.

## Where the layers meet

`(startOf I P)` and `(endOf I P)` name an interval's two bounding instants. They are what
lets a metric constraint stated over instants narrow an Allen relation between intervals, and
what lets `overlapDuration` compute a real overlap instead of a bound. Both directions of
that seam live in [stp.md](stp.md), and it runs one way only: metric narrows qualitative.

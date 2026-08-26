# Temporal reasoning — intervals, instants, and metric time

- **Covers:** Allen's thirteen interval relations and the three-relation point
  algebra, the two qualitative temporal algebras, their composition tables, the three
  calendar constructors that *name* an interval for them to relate, the clock that reads a
  calendar term's two bounding **instants** out of its fields, and the shipped event
  calculus that says what holds when.
- **Not here:** the generic path-consistency engine both algebras run on →
  [qcn.md](qcn.md); how long an interval lasts, and how long two overlap →
  [duration.md](duration.md); the numeric gap between two instants →
  [stp.md](stp.md); how a calendar term keys a **context** rather than filling an argument
  → [context-nat.md](context-nat.md).
- **Assumes:** base relation, relation algebra, constraint network, fluent, inertia →
  [glossary.md](glossary.md); negation as failure, which inertia is stated with →
  [naf.md](naf.md).

Time is the one subject in this tree with layers. Five namespaces, most qualitative first:

| Namespace | Unit | Says | Doc |
|-----------|------|------|-----|
| `vaelii.impl.interval` | intervals | how two stretches of time are ordered and overlap | this page |
| `vaelii.impl.point` | instants | which of two moments came first | this page |
| `vaelii.impl.calendar` | both | where a calendar term begins and ends, and how two of them are ordered | this page |
| `vaelii.impl.stp` | instants | how *far apart* two moments are, in real units | [stp.md](stp.md) |
| `vaelii.impl.duration` | intervals | how *long* one lasts, and how long two overlap | [duration.md](duration.md) |

The first two are relation algebras over the constraint-network engine in [qcn.md](qcn.md).
The engine, the reader, the entailment reading and the prover shape are all documented there
and are identical for both; this page is the two algebras. The bottom two put numbers on
them, and `startOf` / `endOf` are what let the numbers and the orderings be about the same
thing. The middle one is where those two endpoints stop having to be stated: a calendar
term carries its own, and the clock reads them off its fields.

Every prover here is **opt-in**; none of the vocabulary is. One thing about instants does
answer without a prover: `instantBefore` and `instantAfter` are declared **transitive** in
`CxTime`, so a chain of strict orderings composes off the taxonomy alone
([taxonomy.md](taxonomy.md)) — and a forward join reads it, which is what `CxChange`'s
inertia is built on. What the network adds over that is everything a walk over edges
cannot reach: an ordering through an `instantEqual`, the three derived relations, and an
unsatisfiable network reported as a contradiction.

## The interval algebra (`vaelii.impl.interval`)

The unit is an **interval**, not an instant. A meeting, a reign, a journey — something
with a start and an end — so two of them can meet, overlap or nest, which is exactly the
structure a point calculus throws away. The interval relations are declared `(arg …
temporal_thing)` and the instant relations `(arg … time_point)`, `time_point` sitting
under `temporal_thing`, so `startOf` and `endOf` bridge the two by declaration as well as
by meaning. A temporal relation between two predicates is refused rather than stored.
The algebra itself knows nothing of clocks or calendars — only order and containment; the
calendar constructors below *name* intervals for it, and compute no relation of their own.

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
nothing, so they can only agree by both being right — which is what makes a mistyped cell
a test failure rather than a wrong answer.

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

**The same algebra appears twice in this tree.** `vaelii.impl.projection` builds a
nine-relation algebra out of two independent one-dimensional projections — the cardinal
directions and the relative frame are both that shape ([space.md](space.md)) — and each
projection is exactly these three relations under the spellings `:lt` / `:eq` / `:gt`. The
table is duplicated rather than shared: there the three relations are a position on an axis
and an implementation detail of the two nine-relation algebras built over them, here they
are an order in time with their own vocabulary. Nine identical entries are cheaper than the
coupling, and either copy is checkable against its own definitions.

## Naming an interval: the calendar constructors

Everything above relates intervals a KB has *names* for — `Breakfast`, `Reign2`. Three
constructors give a name to the interval a calendar already picks out:

```clojure
(YearFn 2000)        ; the whole of 2000
(MonthFn 2000 1)     ; its January
(DayFn 2000 1 15)    ; the fifteenth of that January
```

Each takes one integer field per argument, coarsest first, so **its arity is its
precision**, and each is an `unreifiableFunction` — the application stays structural, so
the fields are readable inside the term rather than collapsed into an opaque constant. Each
declares `(result … temporal_thing)`, which is what makes a calendar term an ordinary
argument of `before`, `during` or `subintervalOf` and **not** of `instantBefore`: a year is
a stretch, not a moment.

Their reason for existing is the containment: a reader can see from the fields alone that
January 2000 sits inside 2000 and that February sits inside neither. That is what
[context-nat.md](context-nat.md) turns into a computed `genlCx` edge, so a fact asserted
for the year is visible from the month with nobody stating the edge — the one way this
engine time-indexes a fact. `vaelii.impl.datetime` reads a calendar term and a
reduced-precision ISO string (`(DatetimeFn "2000-01")`) to the same field vector, so the
two spellings name the same intervals and order against each other.

A calendar term's **endpoints** are computed rather than stated: `(YearFn 2000)` begins at
`(InstantFn 2000 1 1 0 0 0)` and ends at `(InstantFn 2001 1 1 0 0 0)`, and a prover answers
`startOf` / `endOf` from the fields with nothing stored. That is what puts a calendar term
in the point algebra as well as the interval one, and it is [The calendar
clock](#the-calendar-clock) below. `Breakfast` is unchanged — an ordinary interval has no
fields to read, so its endpoints are still the facts somebody states.

## Change over time: events, fluents, and inertia

The algebras above order time. `CxChange` is what makes time *carry* anything: a simple
event calculus, shipped as a **middle theory** — four rules over vocabulary `CxTime`
declares, and data rather than code, so it is read and edited like the rest of the
ontology. It lives here rather than on a page of its own for that reason: a theory the KB
states in its own representation is not a subsystem.

A narrative states four things and nothing else:

```clojure
(happens CatFallsAsleep ThreeOClock)                      ; an event, at a moment
(initiates CatFallsAsleep (AsleepFn Whiskers) ThreeOClock) ; what it starts
(terminates CatWakes (AsleepFn Whiskers) FiveOClock)       ; what it stops
(initially (IndoorsFn Whiskers))                           ; what was already the case
```

Two questions follow, and neither is ever stated. `(clipped T1 F T2)` — was `F` ended
between the two moments? `(holdsAt F T)` — is `F` the case at `T`? The second is
**inertia**, and it is one line of negation as failure:

```clojure
(set/backwardRule
  (implies (and (happens ?e ?t1) (initiates ?e ?f ?t1) (instantBefore ?t1 ?t2)
                (unknown (clipped ?t1 ?f ?t2)))
           (holdsAt ?f ?t2)))
```

So the cat is asleep at four because something put it to sleep at three and nothing woke
it in between, and it is not asleep at six because something did.

**A fluent is a term, not a sentence.** `(AsleepFn Whiskers)` is a reified NAT — one
constant per subject, the bounded shape [nat.md](nat.md) reserves `reifiableFunction` for
— which keeps `holdsAt` an ordinary binary predicate over two terms. A quoted sentence
would put a *mention* in argument position and have to be held opaque to identity
congruence to mean anything; the term does not.

### The two directions, and why each is what it is

`clipped` and `clippedBefore` are left to chain **forward**. That is not a preference: an
`(unknown S)` antecedent is answered over the registry, which **expands no rule**
([naf.md](naf.md)), so a `set/backwardRule` `clipped` would be invisible to the one
antecedent that exists to consult it — and every fluent would persist for ever, silently.
Forward, it is a stored fact the registry reads, and the extent it materializes is bounded
by the terminating events times the instant pairs the narrative actually wrote down.

`holdsAt` is **backward**. A fluent holds at every moment between its start and its end, so
forward chaining would store one fact per moment per fluent — an extent nothing bounds, for
a question anybody can ask directly. Ask it with `query` / `prove` rather than `ask`: level
6 is the registry and expands no rule, and `holdsAt` is a rule ([levels.md](levels.md)).

`clipped` is its own predicate rather than a conjunction inside the `unknown` for a third
reason: `unknown` takes **one literal**, and a conjunction under it would be read as
independent ground checks sharing no witness. Naming the condition keeps it one literal and
keeps its meaning.

### Stratified, and admitted as written

Simple event calculus is **predicate-stratified**: `holdsAt` depends negatively on
`clipped` and `clippedBefore`, and neither of those depends on `holdsAt` at all. The
assert-time check is predicate-level ([exceptions.md](exceptions.md), "Stratification"), so
it admits the theory as written — nothing had to be shaped around it, and a cycle through
negation would have been refused rather than quietly answered.

Inertia is **undercutting**, like an `exceptWhen` and unlike a defeat: a clipped fluent has
no conclusion for the KB to arbitrate. So an event heard of *later* that terminates a
fluent simply takes the answer back, and retracting that event gives it again — order
independence on a question with no stored answer.

### What `clipped` can see

`instantBefore` and `instantAfter` are declared **transitive** in `CxTime`, and a forward
join over an antecedent on a transitive predicate reads the closure as well as the stored
edges ([taxonomy.md](taxonomy.md), [inference.md](inference.md)). So a narrative writes
down the consecutive links and `clipped` sees the order they imply: three o'clock before
six follows from three-before-four, four-before-five and five-before-six, and the derived
`clipped` rests on those three edges — retract any of them and it goes.

What `clipped` still cannot see is an ordering **no stored edge carries**. The walk crosses
believed stored `instantBefore` edges (and the spellings `genl` and `inverse` make
equivalent); a bound the constraint network narrowed to `:before` without anybody stating
it is a prover answer over a network, and is not one of them. The calculus is opt-in
besides.

A calendar moment is the second case of that, and it is the same case. A narrative may be
written at computed instants — `(happens RexSleeps (InstantFn 2000 1 15 15 0 0))` is an
ordinary `happens`, `(InstantFn …)` being a `time_point` where a calendar term is not —
and it then needs its `instantBefore` edges written down exactly as an afternoon of named
moments does. The calendar clock supplies none of them, and **both** halves of the theory
stop at the same place, which is what keeps the pair honest rather than half-sighted:
`clipped`'s forward join and inertia's backward one each reach `instantBefore` with one
end **open** — "what happened before six", not "is three before six" — and an open end is
what the clock refuses (["What the clock does not reach"](#what-the-clock-does-not-reach)).
So a fluent is never reported as persisting past an event the clock could have ordered but
the narrative did not. State the links, and the whole theory reads them: `clipped` fires
over `InstantFn` moments, `holdsAt` answers, and retracting a link takes both back.

An event happens at a **moment**, so a calendar term is not one: `(happens E (DayFn 2000 1
15))` is refused by the argument check, a day being a `temporal_thing` and `happens`'
second argument a `time_point`. `(happens E (InstantFn 2000 1 15 0 0 0))` is the moment
that day begins, and `(startOf (DayFn 2000 1 15) ?i)` is how to name it.

### Two readings of one cat, on purpose

`CxBiology` already says an animal is awake unless it is known to be asleep — a default
with an exception, and no notion of time at all. The same cat's afternoon written as events
and fluents answers *when*. Neither derives the other, and the pair is what the timeless
reading costs: `weightOf` and `heightOf` are `functional` precisely because nothing in them
says when ([quantity.md](quantity.md)), and a fluent is what that would take.

## Where the layers meet

`(startOf I P)` and `(endOf I P)` name an interval's two bounding instants. They are what
lets a metric constraint stated over instants narrow an Allen relation between intervals, and
what lets `overlapDuration` compute a real overlap instead of a bound. Both directions of
that seam live in [stp.md](stp.md), and it runs one way only: metric narrows qualitative.

The narrowing is **wired**, not offered: the interval algebra declares it as its calculus's
second reader ([qcn.md](qcn.md), "A network can have a second reader"), so a KB that writes
down two meetings' endpoints and the gap between them answers `(before Standup Review)` off
the measures with no interval relation stated. The entailment names the constraints, the
endpoint facts and the unit rows behind it, so a forward rule resting on it is withdrawn
when any of them is retracted — an ordinary firing, on a relation nobody stored. It is the
only calculus of the six with a narrowing; the other five read stored facts alone.

### The calendar clock

The seam above runs on facts. For a **calendar** term it runs on arithmetic instead:
`(YearFn 2000)` says which year it is, and a year has a first moment whatever anybody
wrote down. `vaelii.impl.calendar` is the prover that reads them, registered by name like
every other reasoner here (`add-reasoner kb :calendar`) and answering three families:

```clojure
(startOf (YearFn 2000) ?i)      ; ?i = (InstantFn 2000 1 1 0 0 0)
(endOf   (YearFn 2000) ?i)      ; ?i = (InstantFn 2001 1 1 0 0 0)
(instantBefore (InstantFn 1999 6 1 0 0 0) (InstantFn 2000 1 1 0 0 0))
(during (MonthFn 2000 3) (YearFn 2000))
```

**A moment is `(InstantFn Y M D h m s)` — six integer fields, always.** It is a
`time_point` where the calendar constructors are `temporal_thing`s, declared in `CxTime`
beside them and `unreifiableFunction` for their reason: the fields are what the ordering
reads. Six fields and not a reduced-precision spelling, because a term is identified by
its shape and one moment must have exactly **one** term — `"2000-01-01T00:00:00"` and
`"2000-1-1T0:0:0"` are two shapes for one moment where six integers are one. That is also
why it is not `DatetimeFn` at full precision: `(DatetimeFn "2000-01-01T00:00:00")` denotes
the one-*second* interval, the whole `DatetimeFn` / `YearFn` / `MonthFn` / `DayFn` family
naming stretches, and a stretch is not the moment that opens it.

**The convention is half-open, `[start, end)`.** A term's end is the *first* moment of
the next term at the same precision, so the end of 1999 and the start of 2000 are the same
term:

```clojure
(endOf   (YearFn 1999) ?i)      ; ?i = (InstantFn 2000 1 1 0 0 0)
(startOf (YearFn 2000) ?i)      ; ?i = (InstantFn 2000 1 1 0 0 0)   — the same term
```

The alternative — the end of 2000 being the *last representable* moment inside it — has to
name a smallest tick before it can name anything, so the end of a year would move when
somebody read the clock more finely, and the two terms above would be a second apart
instead of identical. Half-open needs no tick.

What follows from it is the one thing to read before writing a rule over calendar terms:
**consecutive calendar terms `meet`, they are not `before`.** Allen's `before` is strict
and requires a gap, and there is no gap between 1999 and 2000.

| Goal | Holds | Why |
|------|-------|-----|
| `(meets (YearFn 1999) (YearFn 2000))` | yes | 1999's end *is* 2000's start |
| `(precedes (YearFn 1999) (YearFn 2000))` | yes | `precedes` is before-or-meets |
| `(before (YearFn 1999) (YearFn 2000))` | **no** | no gap; `precedes` is the ordering meant |
| `(before (YearFn 1999) (YearFn 2001))` | yes | 2000 is the gap |
| `(during (MonthFn 2000 3) (YearFn 2000))` | yes | March sits inside with room either side |
| `(starts (MonthFn 2000 1) (YearFn 2000))` | yes | same start, earlier end |
| `(finishes (MonthFn 2000 12) (YearFn 2000))` | yes | same end, later start |
| `(subintervalOf (MonthFn 2000 1) (YearFn 2000))` | yes | the disjunction over all three |
| `(intervalEqual (MonthFn 2000 1) (DatetimeFn "2000-01"))` | yes | one interval, two spellings |

`precedes` is what "1999 comes before 2000" means in this vocabulary, and the page already
says so where the derived relations are listed: it is the ordering that does not care
whether the two touch.

**The relation is read from the fields, not through the endpoints.** Two calendar terms'
bounds fix which of the thirteen holds, so the prover classifies it directly — four
comparisons of two six-field vectors, against a network build and a path-consistency pass.
The endpoints stay answerable because they are what joins this to the metric layer and to
the point algebra, not because the interval relation needs them. Two of the thirteen never
come out: the calendar's terms are aligned, so two of them nest, coincide, touch or are
disjoint, and neither `overlaps` nor `overlappedBy` can hold between a year, a month and a
day.

**Answered, never stored.** No sentex, no handle, no justification, no minted constant —
so a computed endpoint is not a belief, needs no retraction, and leaves no orphan for the
NAT sweep ([nat.md](nat.md)). The prover implements `Prover` and *not*
`SupportingProver`, which is the exact claim that its answer reads nothing stored and no
retraction can invalidate it ([inference.md](inference.md), "What a computed answer rests
on"). So `why` has no handle to show and is not the door: a computed relation is explained
by `query … {:proof? true}`, where it reads as a `:leaf`, and by this page — the term and
the convention are the whole of what it rests on. Order independence and locality are
free for the same reason: there is no state to accumulate and nothing to relabel.

**Cost, and what it claims.** `:lookup` — a bounded ground computation on at most six
integers per term, with no closure, no network and no index read. `est-bindings` is 1: a
check has the one empty solution or none, and an endpoint is a function of its interval.
`completeness` is **50** — it *augments*. A KB may state `startOf` facts about a calendar
term or interval relations between two of them, and the calculus provers entail more from
what it stated than the fields alone say, so the registry unions this in cheapest-first
rather than running it alone:

```clojure
(v/assert kb '(startOf (YearFn 2000) MillenniumMidnight) 'CxUniverse)
(v/ask kb '(startOf (YearFn 2000) ?i) 'CxUniverse)
;; => ({?i MillenniumMidnight} {?i (InstantFn 2000 1 1 0 0 0)})
```

The guard in the other direction is `provers/shadowing-channels`' fourth channel,
**`:calendar`**: a term's field structure is a source no fact-reading prover has, so a goal
naming a calendar term moves the interval or point calculus off the sole-prover path and
into the union, however complete it correctly claims to be over the network it reads
([inference.md](inference.md), "Running alone takes two conditions"). `query-plan` shows
it as `:guarded-by #{:calendar}`.

**Scoping** is one cached, belief-following taxonomy read, taken only after the goal's own
structural test has passed: `(transitive instantBefore)` is `CxTime`'s declaration and
nothing else states it, so the clock answers exactly where the vocabulary its goals are
written in can be seen.

**It agrees with the context ordering, and neither does the other's job.**
[context-nat.md](context-nat.md) orders time-keyed **contexts** by field nesting, so that a
fact stated for the year is visible from the month; the clock answers **sentences** about
the terms. The two readings coincide exactly — `datetime/subinterval?` holds of `a` and `b`
precisely when the Allen relation between them is one of `subintervalOf`'s four — because
`b`'s fields being a prefix of `a`'s is the same claim as `a`'s bounds lying inside `b`'s.
Nothing is computed twice: the context producer never asks the clock, the clock never
materializes a `genlCx` edge, and the one thing they share is the field reader in
`vaelii.impl.datetime`.

#### What the clock does not reach

- **Both terms must be bound.** An open variable on either side of an interval relation or
  an instant ordering asks the clock to enumerate the calendar, which is not an answer but
  a process that does not come back — so `applicable?` refuses it, exactly as the point
  algebra answers nothing for a pair of open variables. The one variable it binds is a
  `startOf` / `endOf` **result**, which is a function of the interval and so exactly one
  term. There is no set of stored calendar terms to enumerate instead, and enumerating the
  ones a KB happens to mention would make the relation between two calendar terms a
  function of the store, which it is not.
- **So a conjunction has to reach it ground, and the join planner does not know that.**
  `[(holiday ?m) (during ?m (YearFn 2000))]` answers nothing: the planner costs a literal
  by the stored facts it matches ([inference.md](inference.md), "The cost model"), a KB
  storing no `during` facts counts zero, and the `during` literal is therefore placed first
  — where its open argument answers nothing and the generator that would have bound it
  never runs. Ask the relation of two terms already in hand. The same shape and the same
  guidance hold for a transitive walk, which also answers nothing with both ends open.
- **A calendar relation is not a constraint in the interval network.** The clock answers a
  goal about a *pair*; it does not fold its relations into the Allen network the way the
  metric narrowing does, because the terms it speaks of appear in no stored fact and so are
  nodes of no network. So a stated `(before Breakfast (MonthFn 2000 1))` does not compose
  with the clock's `(before (MonthFn 2000 1) (MonthFn 2000 3))` to answer
  `(before Breakfast (MonthFn 2000 3))`.
- **A forward join cannot reach it**, and the mechanism says why: a prover answers a
  forward antecedent only through `chain/solve-computed`, which drops an answer with
  **empty** support rather than building a justification that names the rule alone while
  looking as though it named facts. The clock's support is empty by construction. So a
  calendar relation discharges a rule antecedent under `query` at a `:max-depth`, where the
  leaf is the registry, and derives nothing forward.
- **`temporalDistance` does not follow.** The metric prover's nodes are atomic terms
  (`stp/node-term?`), and a calendar term and an `InstantFn` moment are both structural, so
  neither is a node in a metric network — the gap between two calendar terms is not asked
  of the clock and is not answered by the numbers either. Nothing here converts a field
  vector to a magnitude ([stp.md](stp.md), [duration.md](duration.md)).
- **Three edges of the calendar itself.** A term whose end would leave the four-digit year
  has no endpoints, so `(endOf (YearFn 9999) ?i)` answers nothing — one moment past the
  last year ISO 8601 spells. A date the calendar does not have is stricter here than in the
  containment reader, which bounds a day at 31 whatever the month: `(DayFn 2000 2 30)`
  still nests inside February by fields and simply has no endpoints. And leap seconds are
  not represented — a minute is sixty seconds, which is what a proleptic Gregorian calendar
  of six fields can say.

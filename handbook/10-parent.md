# 10. The parent

- **Covers:** choosing a type's parent as the tightest true one; finding it by walking down
  from a known parent; and keeping the direct specs of `thing` few and broad.
- **Not here:** relating the new type to its siblings → [ch. 11](11-siblings.md); the
  separations a parent's position decides → [ch. 13](13-disjointness.md); a cover that
  installs a parent edge → [ch. 14](14-covers.md).
- **Assumes:** [ch. 6](06-definitional-block.md), [ch. 9](09-differentia.md).

A type's `genl` edges place it in the closure, and the closure decides what the engine
does with the type: which rules fire on its members, which separations reach it, and which
argument declarations it satisfies. The parent is therefore the edge that carries most of
a type's meaning, and every edge above it follows from it.

## tightest parent

*Parent types: the tightest true one*

**genlPrinciple:** strongest form · **specPrinciple:** walk down, broad under thing

**Practice.** Choose the closest existing parent, not a broad one that happens to be true.
If nothing closer exists and the type settles on a broad parent, say so in the type's
comment or in a `;;` note beside the edge, and name the parent it is waiting for. The KB
has no marker for a provisional edge, so the note is the record.

**Example.** abstract.txt places `hollow` under `spatiotemporal` and `mechanism` under
`tangible`, and each comment says why the parent is not one level lower:

```clojure
(genl hollow spatiotemporal)
(genl mechanism tangible)
```

`hollow`'s comment ends "Spatiotemporal rather than tangible, since a cave is a space in
rock and is made of nothing." `mechanism`'s comment ends "Most mechanisms are made, but
not all: a juvenile Issus planthopper grows interlocking gears on its hind legs." Each
names the counterexample that rules out the spec below the chosen parent.

**Why.**

- **Logic.** Every supertype of the tightest parent is a supertype of the type, so the
  tightest true edge entails every looser one. A looser edge entails less: it leaves out
  the properties of the parents between, and each of those is a true claim the KB does not
  hold.
- **Engine.** A rule on a parent fires on every member of every type below it, through the
  `genl` closure, and a separation declared on a parent reaches every type below it. A type
  placed too high misses the rules and the separations of the parents it was not placed
  under: `hollow` placed directly under `thing` would not be separated from `aspatial` or
  `atemporal`, and `disjointness-audit` would read those pairs as `:unknown` instead of
  `:disjoint`. A type placed too low claims members it does not have, and the separations
  of the wrong parent then place true memberships as nogoods: `hollow` placed under
  `tangible` would make a cave's membership in `hollow` clash with a statement that the
  cave is `intangible`.
- **Maintenance.** A tight parent is where a later reviewer looks for the type. A broad one
  makes the type an outlier among the specs of a broad node, where nobody compares it with
  its real siblings.

**Why not the other ways.** A broad parent chosen because it is safely true trades every
rule and separation of the parents in between for the certainty of the one edge. A parent
chosen one level too low, for the typical member, breaks on the counterexample the comment
should have named.

**Audit.** For each new type, run **walk down** from its stated parent, and check that the
comment or a note names the counterexample that rules out each direct spec of the parent.
`min-genls` answers the type's position from below after the change: a stated parent that
`min-genls` leaves out has a tighter parent beside it, and the stated edge restates the
closure (**state it once**, [ch. 4](04-economy.md)).

## walk down

*Tighten genls by walking down*

**genlPrinciple:** tightest parent

**Practice.** Start at the type's current parent and read that parent's direct specs from
the KB. For each, ask whether every member of the type is a member of that spec, in the
real world. If one passes, the type moves under it, and the walk recurses from there. Stop
when no direct spec passes. Query the direct specs from the KB rather than recalling them.

**Example.** The walk for `hollow` starts at `thing`. Every hollow thing has a location in
the physical space of our universe and in time, so the walk passes `spatial`, then
`physical`, and reaches `spatiotemporal`, which core.txt places below `physical` and
`temporal`:

```clojure
(genl physical spatial)
(genl spatiotemporal physical)
(genl spatiotemporal temporal)
(genl tangible spatiotemporal)
```

The next direct spec is `tangible`, and a cave fails it: the walk stops at
`spatiotemporal`. The KB answers each step:

```clojure
(v/direct-specs kb 'spatiotemporal 'CxUniverse)
(v/direct-genls kb 'hollow 'CxUniverse)
(v/min-genls kb 'hollow 'CxUniverse)
```

**Why.**

- **Logic.** The question at each step is a universal claim about the type's members: every
  member of the type is a member of the spec. The counterexample that fails a step is a
  real member outside the spec, and it is the case the comment records.
- **Engine.** `direct-specs` and `direct-genls` read one `genl` edge in the closure, from
  the context given, whatever installed the edge: a stated `genl`, or a `covering`,
  `separating` or `partition` that names the type as a part. A spec installed by a cover
  is therefore in the list, though no `(genl …)` sentence names it, and a text search of
  the files misses it. `min-genls` reads every believed edge and drops a direct parent that
  another direct parent sits below, so it answers where the type sits now.
- **Maintenance.** The specs of a node change as the KB grows. A walk run from memory finds
  the specs of an older KB, and a walk run from the KB finds the current ones.

**Why not the other ways.** Choosing the parent by searching for a term with a similar
name finds a term with a similar name, not the tightest true parent. Choosing it by
walking up from a typical member finds the typical member's types, which include
properties the atypical members lack.

**Audit.** The change records the walk for each new type: each direct spec tried and the
counterexample that failed it. A reviewer reruns `direct-specs` on the stated parent and
checks that each spec in the answer appears in the record.

## broad under thing

*Few direct specs of thing, all broad*

**genlPrinciple:** tightest parent

**Practice.** Very few types should be direct specs of `thing`, and those should be very
broad. A narrow type directly under `thing` usually means a missing intermediate parent,
and the missing parent also hides separations the type would inherit. Tighten it with
**walk down**. Every type is a spec of `thing`, so a type with no path to `thing` is a
defect.

**Example.** core.txt divides `thing` by four partitions, each along one axis:

```clojure
(set/monotonic (partition thing tangible intangible))
(set/monotonic (partition thing spatial aspatial))
(set/monotonic (partition thing temporal atemporal))
(set/monotonic (partition thing causal acausal))
```

| axis | parts | the note in core.txt |
|---|---|---|
| mass | `tangible`, `intangible` | "A thing has mass or it does not" |
| location in some space | `spatial`, `aspatial` | "A thing either has a location in some space or is aspatial" |
| location in time | `temporal`, `atemporal` | "and is either in time or atemporal" |
| ability to be a cause | `causal`, `acausal` | "A thing either can be a cause or cannot, and a cause is in time" |

The parts cross: a region of space is `intangible` and `spatial`, and a number is `aspatial`
and `atemporal`. Below the axes, core.txt partitions `temporal` once more, into
`uninterrupted` and `intermittent`:

```clojure
(set/monotonic (partition temporal uninterrupted intermittent))
```

A new type is placed under one part on each axis it decides, as `hollow` is under
`spatiotemporal`, and so below `spatial` and `temporal`.

**Why.**

- **Logic.** A direct spec of `thing` claims nothing except that its members exist. Each
  partition part claims one fact about every member, and a type under a part inherits the
  fact.
- **Engine.** A partition records the separation and the coverage both. The separation
  makes the two parts of each axis disjoint, and the disjointness reaches every type below
  each part, so a type under `tangible` is separated from every type under `intangible`
  with no declaration of its own. A type placed directly under `thing` inherits no
  separation, and its pairs with the rest of the hierarchy read `:unknown` in
  `disjointness-audit`. The coverage is what the cover inference reads: an instance of
  `thing` denied one part is concluded an instance of the other.
- **Maintenance.** A short list of broad direct specs of `thing` makes the top of the
  hierarchy readable as a set of axes. A long list of narrow ones is a list of types whose
  placement nobody finished.

**Why not the other ways.** A narrow type under `thing` is true, since every type is a spec
of `thing`, and that edge entails nothing else about its members. A type left with no
parent at all is outside the closure: rules on `thing`'s parts never reach it, and the
audits that read the closure cannot place it.

**Audit.**

- `kb-integrity` over the new types reports `:not-under-thing` for a type declared
  `unary_predicate` with no `genl` path to `thing`, read from the audit context. The pass reads
  only the candidate set it is given.
- `kb-integrity` reports `:implicit-genl` for an edge a cover forces: a type under the
  whole that is separated from every part but one belongs under the remaining part. core.txt
  states one such edge with the reason beside it: "The partition of thing into tangible and
  intangible does not derive a genl edge from the disjointness, so the edge is stated."

  ```clojure
  (set/monotonic (genl situation intangible))
  ```

- `kb-quality`'s `:taxonomy` reading counts the type names with any `genl` edge
  (`:edged`) and the ones that reach the root (`:rooted`); `:islands` is the difference,
  the types whose edges lead into a disconnected part of the hierarchy.
- `direct-specs` on `thing` lists its direct specs, and each new entry in the list needs a
  reason it is as broad as the four axes.

# Resource-bounded / anytime inference

- **Covers:** the budget a query runs under
  (`:max-ms`/`:max-results`/`:max-cost`/`:max-depth`/`:max-term-growth`),
  the partial-result contract `ask-within`/`prove-within` return, and what `resume` continues.
- **Not here:** the chainers and prover registry a budget bounds → [inference.md](inference.md);
  the lookup-to-query stack whose laziness the budget spends → [levels.md](levels.md).
- **Assumes:** sentex, prover, backward chaining → [glossary.md](glossary.md).

`vaelii.impl.budget`, surfaced as `core/ask-within`, `core/prove-within`, and
`core/resume`.

A large KB has queries that do not terminate usefully: the transitive closure is
huge, a backward search fans out, an existence check would scan an extent. The
engine's answer is not a faster search — it is a **bounded** one that returns what
it found, says whether it ran dry or was cut short, and can be continued. That is
the *anytime* contract: an answer available at any moment, improving with more
time.

## The one idea: bound a lazy stream, keep the tail

Every query path in this engine is **lazy** — `ask`, `query`, the level stack
all yield one solution at a time, paying per result consumed (see
[levels.md](levels.md), [inference.md](inference.md)). So resource-bounding is not
new machinery threaded through every prover; it is the **consumer-side** discipline
of realizing a lazy answer stream under a bound. And resumption falls out for free:
the *unrealized tail is the continuation*. Hold it, and continuing is realizing
more of it.

`prove` is the one eager engine (a DFS returning a vector). It is made bounded and
resumable the same way, with the same contract — there the **goal stack is the
continuation** rather than a lazy tail.

**The node engine's state is a value.** Routed to by `core/*query-engine*`
([inference.md](inference.md)), it stops between two node expansions and what it leaves
behind is an **agenda** — a frontier, a node registry, a claimed-key set — rather than a
continuation closure. `inference/search-within` drives it under a budget and checks the
bounds **before every node expansion**, not between yielded results: one pull of its
lazy result stream (`search-seq`) steps until a node yields, so a wide unproductive
frontier — a converging rule graph under a generous depth — would otherwise run whole
before a deadline held between results was seen. The session is the continuation, and
`:resume` drives the same session further; solutions an expansion completed past a
`:max-results` cap head the next step rather than being dropped, so a cap of *n* returns
exactly *n*.

Which node it stops *on* is the one thing a bound makes visible. An exhaustive run
expands the same nodes under every ordering, so the node engine's tacticians
([inference.md](inference.md)) can only pay here — time to the first *k* answers, or
answers before a deadline. Two of its modes are outside this contract and say so:
`:first-result?` reduces the answer set rather than reordering it, and a **portfolio** is
driven to completion before its racers can be unioned, so it has no partial answer to
hand back. `prove-within` drives the ordinary stream.

**A bounded run does not poison the literal cache.** `matches-visible` answers are
cached ([inference.md](inference.md)), and a cached stream accumulates as its consumer
pulls but stores only at the moment the *source* runs dry — never when the consumer
stops. So a run cut short by `:max-results`, a deadline, or a bare `take` stores
nothing, and a later unbounded ask for the same literal cannot be served that run's
prefix as though it were the whole extent. Realize-and-store is a decision the source
makes by ending, not one the consumer makes by leaving.

## The budget

A budget is a map of optional bounds; any subset, and `nil` / `{}` means unbounded.

| key | meaning | honored by |
|-----|---------|-----------|
| `:max-ms` | wall-clock milliseconds — a soft deadline | `ask-within`, `prove-within` |
| `:max-results` | stop after this many solutions | both |
| `:max-cost` | a qualitative prover-cost ceiling (a tier keyword) | `ask-within` |
| `:max-depth` | transformation (rule-expansion) depth | `prove-within` |
| `:max-term-growth` | how far a rule may grow a subgoal's nesting | `prove-within` |

`:max-ms` is checked **between** yielded solutions — the honest granularity is one
solution, so a single blocking pull (a closure fixpoint, one deep proof) is not
interrupted mid-flight. This matches the engine's existing candor that "a closure
has no partial answer"; it is a real limit, stated rather than hidden. `:max-cost`
is the complement that keeps *per-solution* latency bounded — see below.

## The partial-result contract

`collect` (and `prove-within`) return one shape:

```clojure
{:results    [ … ]        ; the solutions realized in THIS step (a vector)
 :status     :complete    ; the source ran dry — the answer is exhaustive
             ;; | :timeout   :max-ms elapsed, the source not yet dry
             ;; | :capped    :max-results reached, the source not yet dry
 :count      n            ; (count :results)
 :elapsed-ms ms           ; wall-clock spent in this step
 :resume     <fn | nil>}  ; nil iff :complete; else (budget -> partial result)
```

`:complete` is the load-bearing one and it is exact: it is reported only when the
source was pulled and ended. The other two are the honest negation of that rather than
a claim that work remains — `collect` stops *before* pulling past its bound, since
deciding whether a tail exists means realizing one more element than the cap allows.
So `{:max-results 3}` over a source of exactly three answers reports `:capped` with a
continuation, and driving that continuation yields `:complete` with no results. That
is one extra step, never a wrong answer, and it is the price of a cap that reads
exactly *n*.

`:results` are **per step, not cumulative** — concatenate across steps for the
whole answer. `:resume` is a one-argument function taking a fresh budget, so each
continuation is independently budgeted; `core/resume` calls it (and returns a
`:complete` result unchanged, so a drive loop terminates cleanly):

```clojure
(loop [r (v/ask-within kb goal ctx {:max-results 20})]
  (handle (:results r))
  (when (:resume r) (recur (v/resume r {:max-results 20}))))
```

A bounded run is a **strict prefix** of the unbounded stream, so concatenating
`:results` across `resume` reconstructs exactly what `ask` / `prove` would have
returned (`budget_test` pins this, dedup included).

The continuation captures an in-memory lazy tail (or the DFS goal stack), so
resumption is **in-process only** — it does not survive a restart, and holding a
partial pins its captured state in the heap. This sits under the single-writer
contract (see [storage.md](storage.md)); a cross-restart resume would need the
search state serialized, which it is not.

## `:max-cost` — the qualitative bound

The prover cost model is **qualitative**, not a per-prover time estimate
[why qualitative](defenses.md#qualitative-cost-tiers-over-time-estimates) — a `cost`
tier answering one question, *is the answer something you look up, compute, or search
for?* (`vaelii.impl.provers/cost-tiers`):

```
:lookup  <  :compute  <  :search
```

- `:lookup` — a bounded single-step retrieval: an O(1) ground test (reflexive,
  `evaluate`, `different`, the evaluable and quantity comparisons), a cached closure /
  metadata read (genl/genlCx transitivity, disjointness, predicate-type,
  arg-type), or one index hit (facts, symmetric, inverse). All three are one bounded
  step, lazy to the first result, and no decision turns on which of the three it is, so
  they fold into one tier. Twelve of the shipped provers sit here.
- `:compute` — work over stored facts before the first answer, and five provers claim
  it: a declared-`transitive` predicate walking its closure, `transitiveInArg`, `unknown`,
  `thereExists`, and the aggregates. Those last three are the ones `{:max-cost :lookup}`
  is really about, since a `count` is a census of a whole extent and closed-world
  negation is a query run to exhaustion.
- `:search` — recursive backward chaining, open-ended proof search. **Unoccupied**, and
  by construction: no member of the registry expands a rule, so nothing `ask` dispatches
  opens a proof search — an application prover added through `add-prover` can claim it
  [why the tier stays](defenses.md#qualitative-cost-tiers-over-time-estimates). Rule
  expansion itself is priced by the engine that does it, as `:max-depth` below, which is
  a bound rather than a tier.

The union path already orders applicable provers by this tier (cheapest first, so a
consumer taking one answer never pays for a closure when a lookup answers).
`:max-cost` turns the tier into a **ceiling**: `ask-within` drops every prover above
it *before* the stream is built. So `{:max-cost :lookup}` runs bounded retrieval only —
no closure fixpoint, no `unknown`, no `thereExists`, no aggregate — and, `:search` being
empty, `:compute` and `:search` both keep the whole registry. A goal answerable only by
a dropped tier simply yields nothing (an honest empty, not a hang). Combined with `:max-ms` it is a genuine anytime
strategy: *cheap tiers only, and stop at N milliseconds*.

A value that is not one of the three tiers is **refused** (`:type :unknown-option`), not
read as no ceiling
[why refuse](defenses.md#refusing-an-unrecognized-cost-ceiling).

`:max-cost` is an `ask` concept — `prove` runs only facts and rules — so
`prove-within` ignores it and uses `:max-depth` to bound the search instead.

## `:max-depth` — bounding transformation, not the stack

`prove-within`'s `:max-depth` bounds **rule-expansion** depth: each DFS frame
carries the number of rule expansions taken to reach it, a fact match keeps that
depth, a rule expansion increments it. `{:max-depth 0}` permits no rule expansion
at all (facts only); `{:max-depth 1}` allows a single-hop rule like grandparentOf
but no recursion. Unlike `:max-ms` / `:max-results` it is a **pruning** bound, not
a suspending one: the depth-bounded search still runs to `:complete` (its space is
genuinely exhausted under the bound), so you widen it by re-running with a larger
depth rather than by `resume`. It is the analogue of Cyc's
`:max-transformation-depth`, distinct from forward chaining's `:max-depth`
(recursion-detection cap) though named alike.

## `:max-term-growth` — the other termination guard

The DFS's second guard is a ceiling on how far a **rule** may grow a subgoal's
compound nesting past what its own derivation path has already met
(`res/default-max-term-growth`, 8 — the mechanism is
[inference.md](inference.md), "Backward chaining"). It is a pruning bound like
`:max-depth`, and it is on whether the caller names one or not: a rule that wraps a
function around a head variable asks a fresh goal per expansion, so without a ceiling
the search does not return at all. What the budget key buys is **raising** it, for a KB
whose derivations legitimately build terms deeper than the allowance —
`{:max-term-growth 40}`. The node-engine arm ignores it, terminating on `:max-depth`
instead.

## What it is not

- **No mid-solution interruption.** The deadline is checked between yielded
  solutions; a single expensive `solve` (a large closure) runs to its own
  completion. `:max-cost` is the lever for that case — exclude the expensive tier
  rather than interrupt it.
- **No estimate-based admission control.** The budget spends *real* time, never a
  per-prover estimate
  [why qualitative](defenses.md#qualitative-cost-tiers-over-time-estimates);
  `:max-cost` is the tier-based version, and there is no finer gate reading a
  prover's `est-bindings` against the remaining budget.
- **No cross-process / cross-restart resume.** The continuation is heap state.

## Where it plugs in

The budget layer adds no engine of its own. `ask-within` runs `ask` over a possibly
cost-filtered registry and `collect`s the lazy result; `prove-within` runs the same DFS
through `res/prove-from`, which is the resumable core `prove` itself delegates to, and
wraps its batch in the same contract — or, routed to the node engine, drives a session
through `inference/search-within`, which builds the same contract per expansion. Both
normalize their goal through
`prepare-goal-for-read`, the same step `ask` / `prove` / `sentexes-matching` take — a
reifiable NAT reified to the constant it denotes, a merge-retired term rewritten to
its representative. That is what "same answers as `ask`" rests on, and a read path
that skipped it would not answer *wrongly*, it would answer **emptily**, which reads
exactly like a KB that was never told.

The budget is a thin, testable layer over machinery that is lazy underneath it — which
is why it is small.

What a budget bounds is the *search*: how long it runs, how many results it collects,
how deep it goes. It does not allocate effort **between** proof branches — no estimate
decides which branch deserves the remaining time — so a budget spent on an unproductive
branch is spent.

# Labeling: `do/` imperatives and brave/cautious solve

How the ASP backend is reached from the KB, and why it is reached by *asking* rather
than by the engine deciding on its own.

## Why a caller has to ask

`vaelii.impl.asp.label` classifies a `Program` into `:true` / `:supportable` /
`:false` by brave/cautious enumeration, and materializes a labeling as a
specialization context. Nothing routes a KB to it on its own, and that is the
engine's stance rather than an oversight.

A coexisting `P`/`¬P` pair at `:default` is a **represented dilemma**
(docs/exceptions.md): both sides stay believed, `contradictions` hands over both
handles with both sides' justifications, and the engine arbitrates nothing. So
`settle` builds no `Program`, and `core/last-program` — which `label/classify` reads —
is **nil in exactly the cases where labeling is interesting**.

`asp_label_test`'s preamble names the bridge: *"an application that wants to rank a
dilemma can still do so through this machinery — it just has to ask for it rather than
have the engine decide behind its back."*

`do/labeling` is that asking.

## The `do/` channel

Imperatives enter through `assert`, as a virtual functor in the `do/` namespace, and
are **never stored**. The precedent is `ist`: a form given to `assert` that is not a
fact about the world but an instruction about what to do with one.

| namespace | meaning | example |
|---|---|---|
| `set/` | set a field on the enclosed rule | `(set/forwardRule (implies …))` |
| `do/` | perform an action; store nothing | `(do/labeling LabelContext)` |

Why the assert channel at all, when this could be a plain function call:

* One API. A labeling can be written into a seed EDN alongside the ontology it
  labels, and replayed by the same loader.
* It is *about* the KB in the KB's own language, which is the same argument that put
  the vocabulary's documentation in `comment` sentexes.
* The return value stays a handle (or a vector of them), because what labeling
  actually does is assert — a `genlContext` edge and a set of `ist` copies.

### The one hard constraint: never inside a fixpoint

A `do/` form is refused as a rule antecedent, a rule consequent, an `exceptWhen`
query, and anything derived. This is not tidiness. Forward chaining is a fixpoint
whose defining property is that the same knowledge in any order yields the same
beliefs; an imperative that runs *during* it would execute a number of times that
depends on firing order, and would mutate the KB the fixpoint is still computing over.
Order independence and locality are the two invariants the whole TMS is built on
(docs/nmtms.md), and a side effect inside the fixpoint breaks both at once.

So `do/` is legal only as a top-level `assert`, where it happens once, after settling,
at a point the caller chose. It throws `:type :not-assertible` anywhere else.

## `(do/labeling Ctx)`

Four steps, in an order the imperative fixes so a caller cannot get it wrong:

1. **Build a `Program` from the current dilemmas.** Not from `last-program` — see
   above, that is nil here. `contradictions` supplies the nogoods, their members are
   the contested assumptions, and `contested-content` supplies what each asserts.
   Known-true content is never contested, so it enters as `:fixed` background exactly
   as it would have from `settle`.
2. **Classify** brave/cautious over the optimal answer sets.
3. **Record** the `Program` in the KB's `:program` slot, so `last-program` and
   `label/classify` answer about this labeling afterwards. `settle` never writes that
   slot for a dilemma — it builds no Program for one — so nothing is overwritten.
4. **Materialize** one optimal labeling into `Ctx` and return the handles.

Classification runs *before* materialization because materializing entrenches:
what it writes are ordinary assertions, and an assertion is evidence, so the recorded
side ends up in a second nogood against its rival. A tie that classifies
`:supportable` on both sides classifies `:true`/`:false` once labeled. That is not a
bug — it is what recording a choice means — but it means the classification must be
taken first. Making the imperative do both in one call is how that ordering stops
being a thing a caller has to remember.

### Where the labeling comes from, and why it differs from `label-context`

`label/label-context` reads the labeling from the **TMS**, and `label.clj`'s namespace
docstring is emphatic about refusing to re-solve: *"A re-solve would usually agree, and
'usually' is not a property worth building on."*

`do/labeling` on a dilemma reads it from the **solve**. That is not a reversal. Both
follow the same rule — *report what actually decided it* — applied to two different
situations:

| situation | who decided | so read from |
|---|---|---|
| a tie `settle` arbitrated | the engine committed to one side | the TMS |
| a dilemma `settle` declined | nobody; **both sides are IN** | the solve |

Reading current belief for a dilemma would copy *both* sides of the contradiction
into the labeling context, which just recreates the dilemma one level down. There is
no committed answer to be faithful to, so the solve is the only thing that decides.

### `Ctx` inherits, and the labeling is recorded by strengthening

`Ctx` is a `genlContext` specialization of the base, and each kept assumption is
re-asserted inside it at `:monotonic`. Nothing needs to be said about the side that
lost: the strengthened copy out-ranks it and `decide-nogood` defeats the strictly
weaker member. So `Ctx` is a **world** — the uncontested background is inherited, and
the contested atoms are decided within it.

Both halves of that are load-bearing, and the two neighbouring designs are the
argument:

* **A copy at `:default`** merely ties with the side it is supposed to beat, so it
  reports a second dilemma instead of deciding the first — `contradictions` **1 to 2**,
  and a second labeling would report it three times. Entrenchment is correct for
  `label-context`, where the loser is already defeated and the copy meets no live
  rival; here both sides are IN and a tying copy walks straight into a fresh nogood.
* **A detached `Ctx`** avoids that double-report and leaves the base bit-for-bit
  untouched, but then holds only the labeled literals and inherits no background — a
  record to read rather than a world to query.

The `:monotonic` copy into an inheriting context takes `contradictions` from **1 to
0**: the dilemma is decided rather than duplicated.

### The commitment is global, and that is the trade

Belief in this TMS is a property of a *datum*, not of a datum-in-a-context. So
strengthening inside `Ctx` defeats the losing side **everywhere** — the base KB stops
reporting the dilemma and the loser goes OUT for every context, not only under `Ctx`.

This is the one place where "the KB represents dilemmas, it does not solve them"
bends, and it bends deliberately:

* The engine still refuses to arbitrate **on its own**. `settle` decides no
  default/default clash; the commitment happens only because a caller wrote the
  imperative.
* It is undoable. `retract!` on the returned handles revives the dilemma, both sides
  IN and `contradictions` back to 1.

The cost is that rival labelings are compared **sequentially** — label, inspect,
retract, label again — rather than side by side. Holding two at once requires belief
to be relative to a context, which is exactly what an ATMS's per-datum assumption
labels give you and what this TMS does not have. The difference is in the truth
maintenance, not in the labeling.

### The labeling solve and the classification solves must agree

`do/labeling` runs **three** solves: brave and cautious for the classification, and one
more for the labeling itself. The third is irreducible — brave and cautious give the
union and the intersection of the optima, and neither is a single answer set — so the
labeling has to be solved for separately.

Separate solves have to be *reconciled*. `classify-program` needs to enumerate optima,
which only ASP does, so it goes straight to the backend and ignores `(:solver kb)`. A
labeling taken from the installed solver — on a default KB, the greedy `local-solver` —
would answer from a different search procedure, and the two diverge in practice.
Measured on two nogoods sharing a member, where greedy spends two defeats and the
optimum spends one:

```
stub  defeats {2,3} -> labels {1}     classification: {:true {2,3} :false {1}}
ASP   defeats {1}   -> labels {2,3}
```

The stub's labeling keeps an assumption holding in **no** optimum and drops two
holding in **every** one. Under commit semantics that materializes an impossible world
and globally defeats the atoms classification calls forced.

Two things hold them together. The labeling solve uses the **ASP edge solver whenever a
backend is reachable**, deliberately bypassing `(:solver kb)` so both answers come from
one search procedure; with no backend the two degrade together, since `classify-program`
then claims nothing and any labeling satisfies it. And the invariant is **checked before
committing** rather than assumed:

```
:true ⊆ labeled        :false ∩ labeled = ∅
```

A violation throws `:type :labeling-inconsistent`. Refusing to commit is the right
failure: an impossible labeling entrenched as monotonic assertions is much worse than
an error.

The nogoods the engine builds have two members apiece — a `P`/`¬P` pair, a definitional
clash — and greedy cannot diverge from optimal on a plain pair, so no sequence of
`assert`s reaches the check. It is pinned at the `Program` level instead, where a
divergence can be handed to it directly.

### One caveat about which level you ask at

`Ctx` is consistent at level 3 (`:visible`) — the belief-filtered view of stored
facts — and that is the level at which "is this world consistent" means anything.

Two neighbouring levels will mislead you:

* **`sentexes-matching` (level 2) is context-exact.** It does not show inherited facts at all, so
  it reports the background missing from `Ctx` even though `Ctx` sees it.
* **`ask` (level 7) re-derives.** Backward chaining will prove the defeated side again
  from the rule that concluded it, so `ask` answers *both* sides. This is not something
  labeling introduces — it happens in the base context too, and is a standing
  disagreement between `ask` and belief.

### Why an arbitrary pick is legitimate here

The engine refuses to arbitrate a dilemma because doing so silently would destroy the
thing an application wants to rank. Three things make the same pick acceptable when it
comes through `do/labeling`:

* **It was asked for.** The caller wrote the imperative.
* **It is reversible.** Retracting the returned handles revives the dilemma exactly as
  it was, so the commitment is a move that can be taken back rather than knowledge
  destroyed. This is checked, not assumed.
* **It is one of several, and says so.** The classification recorded alongside it
  marks every side `:supportable` that genuinely was, so the context is legible as one
  choice among the optima rather than as the answer. Rival answer sets can be built as
  sibling contexts and compared.

### Determinism

Which optimum is materialized may not depend on assertion order, on handle ids, or on
solver nondeterminism — the engine-wide invariant (docs/nmtms.md) does not get an
exception for being inside a solver. The choice is keyed on **content**, through the
same `solve/content-key` that orders the stub solver, and the ASP encoding's
three-level objective already ends in a content-keyed tiebreak for this reason.

### Without an ASP backend

`local-solver` produces one labeling deterministically but cannot enumerate optima. So
on a plain build:

* materialization works — the stub's pick is well-defined and content-keyed;
* classification reports every contested assumption `:supportable`, which is honest
  (each *is* one of several) and never overclaims `:true`.

A build without clingo behaves like one with it, minus the ability to distinguish
forced from arbitrary — which is precisely the thing enumeration buys.

## Naming

No `!`. Labeling creates a context and asserts into it; retracting the handles it
returns undoes it. The `!` convention marks operations that *lose* knowledge, and this
only adds.

## Status

`labeling_test` covers this channel in 13 tests: the `do/` channel itself, the
dilemma-to-`Program` bridge (`label/dilemma-program`), the solve-sourced labeling, and
`label/label-dilemmas`. `label/classify-program`, `label/label-context`,
`edge/edge-solver` and the clingo/clasp backends are `asp_label_test` /
`asp_edge_test`'s subject.

Limits, none of them silent:

* **One labeling at a time**, because belief is global — the trade above.
* **`ask` disagrees with belief about a defeated conclusion** — the caveat above. It
  holds in the base context too; a labeled context is only where you are most likely
  to trip over it.
* **`label-context` and `label-dilemmas` overlap.** The former materializes a labeling
  the engine committed to and reads the TMS; the latter commits to one and reads the
  solve. Both are correct for their situation, and the table above says which is
  which.

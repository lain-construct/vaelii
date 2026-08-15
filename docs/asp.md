# The ASP backend

- **Covers:** how the edge solver renders a contested `Program` to ASPIF and solves it
  with clingo or clasp, deterministically.
- **Not here:** the assumption-rule and constraint vocabulary that builds a `Program` in
  the first place → [solving.md](solving.md); committing one labeling of a dilemma into
  base belief → [labeling.md](labeling.md); writing for this engine when answer set
  programming is the language you already think in, which is the paradigm rather than
  this machinery → [from-asp.md](from-asp.md).
- **Assumes:** edge solver, nogood, brave/cautious → [glossary.md](glossary.md).

The real answer-set solver behind the edge-solver seam. Two layers: a
general-purpose ASP toolkit that
knows nothing about vaelii, and one namespace that renders a
[`Program`](nmtms.md) to it.

```
vaelii.impl.solve/Solver          the seam  (docs/nmtms.md)
  └── vaelii.impl.asp.edge        Program  ->  ASPIF,  answer set -> {:defeat :violated}
        └── vaelii.impl.asp.solver          backend selection
              ├── vaelii.impl.asp.clingo    in-process libclingo, via JNA
              └── vaelii.impl.asp.clasp     subprocess, ASPIF on stdin
        └── vaelii.impl.asp.aspif           the emitter
        └── vaelii.impl.asp.atoms           atom ids and labels

vaelii.impl.asp.label             brave/cautious classification; labeling contexts
```

## Installing it

Nothing uses it until you say so — `local-solver` remains the default, so a build
without clingo behaves exactly as before.

```clojure
(v/set-solver kb :asp)
```

The name is the whole of it — `set-solver` resolves the backend at runtime, so a caller
needs nothing from `vaelii.impl.asp.*` and nothing here reaches the load path of a KB
that never asks. `edge-solver` degrades rather than fails. With no backend reachable it delegates to
`solve/local-solver`, so installing it is always safe, and `(solver/available?)` tells
you whether the selected backend can solve in this environment. Which of the two runs is
not exposed: it is a routing decision the solver makes per program, from the config, from
whether libclingo loaded, and from the program's size.

## Getting a solver

Either backend is enough; both is better.

```sh
brew install clingo          # provides the clingo binary, libclingo, and clasp
lein with-profile +with-clingo test     # points JNA at /opt/homebrew/lib
```

- **clingo** runs in-process through raw JNA — no JNI, no generated bindings, no
  clingo Java library. Fastest for small programs, which is the common case here.
- **clasp** is a subprocess taking ASPIF on stdin and returning JSON. It is the
  deliberate fallback for long-running processes, where an in-process native crash
  would take the JVM with it.

`solver.clj` picks per program size (`VAELII_CLINGO_MAX_BYTES`, default 3000 bytes:
clingo below, clasp above) and loads the clingo namespace lazily via
`requiring-resolve`, so JNA stays genuinely optional. Force one with
`-Dvaelii.asp.solver=clingo|clasp` or `VAELII_ASP_SOLVER`.

### Why size picks the backend

In-process clingo saves the subprocess fork — about 4× faster cold on a small program —
and pays a steeper per-solve slope that loses at scale. The driver is I/O and marshaling
rather than model count: libclingo's `load_aspif` reads a `FILE`, so an in-process solve
still writes the whole ASPIF to a temp file and re-parses it, and only the ~5 ms fork is
actually avoided; it then JNA-marshals every witness symbol back across the JNI boundary.
Both costs scale with program and witness **size**, in every mode rather than only under
brave/cautious enumeration — which is what makes byte length a sound cross-mode proxy, and
one cutoff enough for all of them.

Measured: classify crosses over around 2.9 KB (closure around 80), and a large `:label`
solve also loses in-process — clasp 471 ms against clingo 673 ms. Hence the 3000-byte
default.

The cutoff is AUTO-mode only; an explicit `VAELII_ASP_SOLVER=clingo` uses clingo whatever
the size. Rerouting a large program to clasp is safe because a program is only ever plain
ASP, which both backends answer identically. And the cutoff yields to availability: on a
machine with libclingo loaded and no `clasp` executable, AUTO keeps large programs
in-process too — a slower solve is a cost regression, where routing to a binary the
machine does not have would be a refusal `available?` had promised away. The clasp probe
forks a process to answer, so it is made once per JVM.

## The encoding

A contested assumption becomes a **choice atom**: true means believed, false means
defeated. Known-true (`:fixed`) members of a contradiction get no atom at all —
they hold by assumption, which is what makes them background rather than something
the solver decides.

A contradiction becomes a violation atom derived from its contested members, plus a
**weak** constraint minimizing it:

```
v :- a_h1, a_h2, ...        # every contested member holds
#minimize { 1@level : v }   # violating this costs, it does not make the program UNSAT
```

Weak rather than hard is the point: a contradiction that cannot be satisfied is
*reported*, not thrown. That is the soft-and-prioritized contract from
[nmtms.md](nmtms.md), expressed directly in the object language.

### The objective

Higher ASPIF minimize priorities dominate lower ones, so the levels read
most-significant first:

| level | minimizes | why |
|---|---|---|
| `2 + rank(p)` | violation atoms | satisfy contradictions, caller priority first |
| `1` | defeated assumptions | give up as little belief as possible |
| `0` | a content-keyed weight | break what remains, *stably* |

Caller priorities are mapped through their ascending rank rather than used as levels
directly, so any integers work and none can collide with the two fixed levels below.

Level 1 is where this beats the stub. The stub walks contradictions in order and
defeats one member of each; ASP optimizes globally, so where two nogoods share a
member it finds the one-atom cover instead of defeating two things.

### Determinism

A tie between equally-good answer sets has no principled winner, but it must not
depend on the order the knowledge arrived — the engine-wide invariant in
[nmtms.md](nmtms.md). Three things enforce it:

- Atom ids are allocated in `solve/content-key` order, not handle order.
- Rule bodies are sorted by atom id; `:nogood` is a set, and an unsorted body would
  render in hash order.
- Level 0 makes defeating the greatest content-key cheapest, mirroring the stub.

`asp_edge_test` pins the three directly, on hand-built configurations whose handles are
swapped so that a handle-keyed allocation would render a different program from a
content-keyed one. It separately runs all 24 orderings of a Nixon diamond through a KB
with `edge-solver` installed and demands one distinct outcome — but that permutation
answers a different question, since the engine routes a plain rebuttal to no solver at
all (below): what it catches is whether the mere *presence* of a backend perturbs the
result, which is the assertion `order_independence_test` makes for the stub.

## Classification: what was forced, what was a coin toss

`vaelii.impl.asp.label` answers a question the TMS cannot. After `settle` resolves a
tie one side is IN and the other OUT — but that flattens two different situations. A
belief can be IN because *every* consistent labeling keeps it, or because the solver
had two equally good options and took one. `in?` reads the same either way.

Asking for all optimal answer sets instead of one separates them:

| class | in every optimum | in some optimum | meaning |
|---|---|---|---|
| `:true` | yes | yes | forced — no consistent labeling gives it up |
| `:supportable` | no | yes | arbitrary — the current belief is one of several |
| `:false` | no | no | excluded — no consistent labeling holds it |

```clojure
(label/classify kb)             ; -> {:true #{h} :supportable #{h} :false #{h}}
```

Where two nogoods share a member, that member is `:false` and its partners `:true` —
dropping the shared one costs a single defeat, so every optimum does it.

**`classify` reads the last `Program` the engine built, and a plain rebuttal builds
none.** The engine does not arbitrate a coexisting `P`/`¬P` pair at `:default`: that is a
represented dilemma, both sides stay IN, and `settle` never reaches the solver. So
`last-program` is nil and `classify` answers `{:true #{} :supportable #{} :false #{}}` —
empty sets, not two `:supportable` handles. A Nixon diamond is exactly that shape, which
makes it the illustration `classify` cannot be shown with: to classify one, commit to a
labeling first with `do/labeling` ([labeling.md](labeling.md)), which is the mechanism
that does build a program from a dilemma. `asp_edge_test`'s
`the-asp-solver-does-not-decide-a-nixon-diamond` pins the absence.

### Two things keep this honest

**The tiebreak comes off.** The level-0 content-keyed objective exists to make an
arbitrary choice *stable*, not to express anything about the world. Left in, it makes
the optimum unique, and every tie would classify as forced. `classify` translates
with `{:tiebreak? false}` so it sees the real set of optima.

**The program is read, not recomputed.** Resolving a tie erases its own evidence: the
defeated side stops matching, so the nogood is no longer derivable from the KB. A
classification built by re-scanning would find nothing contested and report false
certainty. `core/last-program` records what the solver was actually asked, which is
why the KB carries it.

### Concert with the TMS

Two invariants, held by construction and pinned in `asp_label_test`:

```
:true  ⊆ believed          cautious holds in the committed model, which is an optimum
:false ∩ believed = ∅      excluded holds in no optimum, including that one
:supportable               either way — that is what makes it supportable
```

A contradiction settled by *strength* rather than arbitration never builds a program
at all (`decide-nogood` defeats the weaker side directly), so `classify` correctly
reports nothing arbitrary.

Without a backend, `classify` reports every contested assumption `:supportable`. Each
genuinely *is* one of several options, so this understates rather than overclaims.

## Labeling contexts

`label-context` materializes one labeling as a specialization context:

```clojure
(label/label-context kb 'CxNixonA 'CxUniverse)
;; -> {:context CxNixonA :handles [10]}
```

`ctx` sees `base` through `genlCx`, so it inherits the whole KB; what it adds is
an explicit, queryable record of one arbitration. Two labelings of the same tie can
be built as sibling contexts and compared.

The labeling is read from the **TMS**, not from a fresh solve — it records what the
engine committed to, rather than what a second solve might independently choose. A
re-solve would usually agree, and "usually" is not a property to build on.

### It entrenches what it records

Worth knowing before using it: what `label-context` writes are ordinary assertions,
and an assertion is evidence. The recorded side gains a second nogood against its
rival, which makes defeating the rival strictly cheaper than defeating the record. So
a tie that classified `:supportable` on both sides classifies `:true`/`:false`
afterwards.

Belief does not move — the losing side was already OUT — but it stops *looking*
arbitrary, because it no longer is: something now asserts the choice. **Classify
before you label.** Retracting the returned handles reopens the tie.

## Why `:violated` comes back empty

It looks like a gap and is not. An irreducible known-true clash never reaches a
solver: `settle/settle`'s `decide-nogood` classifies it as *hard* and reports it
directly, and `solve/program` drops any nogood with no contested member. What does
arrive always has a contested member, and defeating that member always satisfies it.

The `:doomed` path in `edge.clj` is therefore defensive. It costs nothing and stays
correct if nogoods ever grow beyond today's `S` vs `(not S)` pairs.

## Where the ASP layer stops

What the engine encodes is the contradiction edge and nothing above it: `edge.clj`
translates one settle's nogoods into a program, and `label.clj` classifies and labels
what comes back. There is no multi-context classification, no cardinality grounding
and no multi-shot solving — a solve is one program, built from one region, answered
once.

There is also **no CSP layer**: a program carries no integer constraints, so nothing
emits clingcon theory atoms and a numeric bound reaches the solver only as the handles a
nogood names. Metric bounds are `vaelii.impl.stp`'s, closed by shortest paths outside the
solver entirely ([stp.md](stp.md)).

## Tests

- `asp_aspif_test` — the lower layer. The wire format is pinned *literally*, because
  ASPIF is an external contract with clingo and clasp: a silent encoding change is
  not a refactor, it is a different program. Semantics are then checked by solving.
- `asp_edge_test` — the translation and the `Solver` contract: minimal defeat,
  priority order, deterministic rendering, and the permutation sweep above.
- `asp_label_test` — classification and labeling, every KB-level case re-checking
  the two TMS invariants rather than only the classification itself.

A test that needs a solver skips when no backend is reachable, rather than silently
asserting the stub's behaviour and proving nothing — the whole of `asp_label_test` and
nearly all of `asp_edge_test`. `asp_aspif_test` gates only the tests that solve: the
wire format and the atom table are checkable without a backend, so those always run.

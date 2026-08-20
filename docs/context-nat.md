# Reified-NAT contexts and structural genlCx

- **Covers:** how a `Cx*Fn` function application reifies to a **context** — a `cx/`
  constant a sentex can be stored in and a `genlCx` node — and how a declared argument
  ordering makes one such context a computed **spec** of another with nobody asserting the
  edge.
- **Not here:** object-denoting NATs, which reify to a `nat/` constant that is a *term* and
  never a context → [nat.md](nat.md); the `genlCx` closure the produced edges feed →
  [contexts.md](contexts.md); the lexical conventions the roles rest on →
  [naming.md](naming.md).
- **Assumes:** sentex, context, `genlCx`, reification, the `termOfUnit` map →
  [glossary.md](glossary.md), [nat.md](nat.md), [contexts.md](contexts.md).

A context is normally a `Cx`-prefixed name — `CxTime`, `CxUniverse`. A **reified-NAT
context** is denoted instead by a function application: `(CxTimeFn CxMonad (DatetimeFn
"2000"))` is "the year 2000, along the `CxMonad` dimension". The value of it is that the
context hierarchy can then be **computed**: `(CxTimeFn CxMonad (DatetimeFn "2000-01"))` is a
*spec* (sub-)context of the year — January 2000 is inside 2000 — so a fact asserted in the
year is visible from the month, and **nobody asserts that `genlCx` edge**. This is the
shape Cyc gives a context keyed by a term (its `MtTimeWithGranularityDimFn` and kin).

Two records earlier established the opposite for *object* NATs: a `nat/` constant is a
term, refused as a context by the naming and `genlCx` well-formedness gates
([nat.md](nat.md)). Context NATs are the deliberate exception, carried by a distinct
namespace so the refusal stays exact.

## The representation: reify the outer function, keep the argument structural

A `Cx*Fn` is declared `(contextDenotingFunction CxTimeFn)`. A ground application reifies —
like any NAT, *before* the index sees it — but to an opaque **`cx/`**-namespaced constant
rather than a `nat/` one:

```clojure
(assert kb '(holiday NewYear) '(CxTimeFn CxMonad (DatetimeFn "2000")))
;; stored: the sentex's context slot is a bare symbol  cx/g42
;; map:    (termOfUnit cx/g42 (CxTimeFn CxMonad (DatetimeFn "2000")))
```

Only the **outer** function reifies. Its arguments are left alone by the mint, so an
`unreifiableFunction` argument — `(DatetimeFn "2000")` — stays **structural inside the
stored expression**, exactly as `(QuantityFn 5 Meter)` does in an object NAT
([nat.md](nat.md), reifiable vs unreifiable). That is what lets the producer below read the
time term's shape to decide containment: reifying it away would collapse `"2000"` into an
opaque atom and lose the very structure the ordering needs.

Reifying the outer function is what keeps **"a context slot is a bare symbol"** true
everywhere — the trie index, `sentexes-in-context`, `matches-visible`, the `genlCx` graph
nodes all key on a symbol, and none of them changes. The alternative, a compound in the
context slot, would touch every one of those; the reified constant is one token by the time
they see it.

### The `cx/` namespace carries the context role

Role-reading is **spelling-only** and never consults belief ([naming.md](naming.md)), so a
reified context cannot be marked a context by a `(context K)` fact a `context?` would have
to look up. It is marked by its **namespace**: `naming/context?` is true for a `cx/` symbol
as it is for a `Cx…` name, and false for a `nat/` object constant. `term-role` follows, and
so — because they call `context?` — do the two gates that refuse an object NAT:

- `wff/genlCx-problems` admits a `cx/` constant as a `genlCx` argument;
- `naming/problems*` admits it as a sentex's context slot.

`nat/reified-nat-symbol?` recognizes both namespaces (everything that asks "is this an
opaque reified constant" — display, the `K → E` lookup — wants both); `reified-context-symbol?`
and `reified-object-symbol?` are the discriminants where the kind matters (the mint's
namespace choice, and the orphan sweep below).

### Write and read are symmetric

The context slot is *not* on the sentence-reify walk — it is a separate argument to
`assert` — so `maybe-reify-context` reifies it explicitly: on the write path (`assert`,
minting) and on every read door (`ist-goal`, dedup-only, never minting). A query scoped to
`(CxTimeFn …)` therefore resolves to the same `cx/` constant the write minted and meets the
facts stored there; a never-seen NAT context resolves to the `no-match` sentinel and the
read is scoped to nothing, answering empty rather than minting a context to ask about.

## The structural genlCx producer

`(contextArgSubrelation F pos R)` declares the ordering: two `F`-contexts identical except
at argument `pos` are ordered by the sub-relation `R` on that argument — the one whose
argument is `R`-**below** the other's is the spec, and `genlCx` the more general.

```clojure
(assert kb '(contextDenotingFunction CxTimeFn) 'CxUniverse)
(assert kb '(unreifiableFunction DatetimeFn) 'CxUniverse)
(assert kb '(contextArgSubrelation CxTimeFn 2 subintervalOf) 'CxUniverse)  ; arg 2 = the datetime
```

`vaelii.impl.context-nat` reads the declarations and the context NATs of `F` from the
store, groups the contexts into **siblings** (same expression but for argument `pos`), and
for each sibling pair whose `pos` arguments stand in `R` **materializes** the `genlCx` edge.
The edge is a **justified** derived sentex, made the way `special/deduce-lift` makes a
decontextualized copy — `find-or-create-sentex`, `special/derived-sentex-added` (which
reaches the `genlCx` closure and posts the re-check triggers), then a JTMS justification
under the `contextArgSubrelation` informant. It is **never a premise anyone asserted**.

Justified is the whole point: the edge belief-follows for free. Retract a context (its
`termOfUnit` map), the declaration, or — for the stored-fact oracle below — the `R`-fact,
and the ordinary JTMS relabel withdraws the edge and `sees?` flips. Nothing hunts it down,
and the taxonomy's depth/SCC potential and witness support are the derivation path's, not a
second mechanism ([contexts.md](contexts.md), the consumers).

**Both arrival orders converge.** A declaration arriving after the contexts sweeps them
(`reconcile-function`); a context arriving after a declaration is swept when it is stored
into. The maintenance hook sits beside the correspondence reconcile at the tail of `assert`
and behind the same free in-memory reifiable gate — a `contextDenotingFunction` is a
reify-kind, so any KB with a context NAT to order already passes it, and a KB that reifies
nothing pays neither the hook nor the `any-context-subrelations?` index read.

### The bounded R oracle — no proof inside the relabel loop

The producer feeds the `genlCx` closure, which a relabel loop reads, so it may **not** start
a prover search to decide `R` ([naf.md](naf.md)). `R` is resolved only by a **bounded**
oracle:

- a registered **pure structural comparator**, keyed on the sub-relation — the datetime one
  answers `subintervalOf` between two `DatetimeFn` terms by reading their shape; or
- a **believed stored `(R a b)` fact**, when no comparator applies.

A comparator answer is a pure function of the two expressions, already carried by the
`termOfUnit` antecedents, so it contributes no extra supporter; a stored fact contributes
its own handle, so defeating it withdraws the edge.

## The datetime dimension

`vaelii.impl.datetime` is the first shipped dimension. `DatetimeFn` is an
`unreifiableFunction` taking a reduced-precision **ISO 8601** string that denotes an
*interval*: `"2000"` the year, `"2000-01"` its January, `"2000-01-15"` a day, down through
hour, minute, second. Containment is **field nesting** — a more-precise instant is inside a
less-precise one it shares every field with:

```
"2000-01"     ⊆ "2000"        ; January is inside the year
"2000-01-15"  ⊆ "2000-01"     ; the day is inside January
"2001"        ⊄ "2000"        ; different year
"2000"        ⊄ "2000-01"     ; the year is the COARSER interval, so it contains the month
```

`subinterval?` parses each string into a vector of integer fields and tests prefix
equality — pure, total (it declines any non-`DatetimeFn` term), and bounded, so the
producer may call it inside the settle loop. Fields are numeric, so `"2000-1"` and
`"2000-01"` denote the same month.

## What this does not cover

- **One dimension ships.** `DatetimeFn`/`subintervalOf` is the worked example; other
  dimensions are added by declaring a `contextDenotingFunction`, a `contextArgSubrelation`,
  and either registering a comparator or asserting the `R` facts. `YearFn`/`MonthFn` as
  structural calendar constructors reducing to a datetime are **not** built.
- **A context NAT is not orphan-swept.** An object NAT is collected when no sentence names
  it ([nat.md](nat.md)); a context's liveness is instead the facts stored *in* it (its
  context slot), which the term index does not post — so contexts are left out of the sweep
  and **persist** until torn down explicitly. Re-minting the same expression still dedups to
  the one constant.
- **The stored-fact oracle is not retroactive on its own.** A comparator dimension needs
  nothing but the contexts; a dimension resolved by stored `(R a b)` facts has its edge
  swept when a context or the declaration arrives, but an `(R a b)` fact arriving *after*
  both contexts does not itself re-trigger the producer in this version.

## Where it lives

- `vaelii.impl.nat` — `context-namespace`, the `cx/` mint path (`mint-nat!` picks the
  namespace and skips result-types for a context), `maybe-reify-context`,
  `context-denoting-ground-nat?` (what the context-slot shape check admits — a *declared,
  ground* context function, so the check does not depend on the naming policy), and the
  `reified-context-symbol?` / `reified-object-symbol?` discriminants.
- `vaelii.impl.naming` — `context?` (the `cx/` namespace).
- `vaelii.core` — the context-arg reify in `assert` and the read doors (`ist-goal`), the
  context-slot shape gate (`context-shape-problem`), the producer maintenance hook, and its
  revival re-run on `retract!` / `edit!` (`context-nat/reconcile-revivals!`).
- `vaelii.impl.special` / `wff` — the `contextDenotingFunction` prop mark and the
  `contextArgSubrelation` well-formedness check.
- `vaelii.impl.context-nat` — the producer and the comparator registry.
- `vaelii.impl.datetime` — the ISO 8601 containment comparator.
- `resources/kb/CxCore.txt` — the two declarations documented in the KB's own representation.

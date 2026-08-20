# Belief projection: what an agent holds true

- **Covers:** `(believes Agent P)` — answered by proving `P` inside `Agent`'s own
  context rather than in the asker's, so agents may disagree without the KB
  contradicting itself. `modalPredicate` / `register-modal-predicate!` open the same
  machinery to `knows`, `desires`, `intends`.
- **Not here:** a modal *logic* — no K/T/4/5 schema, and a nested `(believes A (believes B P))`
  projects only where the marker is visible — nothing by default, since an independent
  agent context cannot see the grant (see below); hypothetical worlds → [abduction.md](abduction.md).
- **Assumes:** context, `genlCx` visibility, the prover registry → [contexts.md](contexts.md),
  [glossary.md](glossary.md).

Two agents can believe contradictory things without the KB being inconsistent — that is
what a context lattice is *for*, and the engine already has the lattice. What belief
projection adds is one convention and one prover over it: no new belief primitive, no
change to the JTMS, the taxonomy or the index.

```clojure
;; Alice's beliefs are ordinary facts in Alice's own context.
(v/assert kb '(flies Tweety) 'CxAgentAlice)

(v/ask? kb '(believes Alice (flies Tweety)) 'CxWell)   ; => true
(v/ask? kb '(believes Bob   (flies Tweety)) 'CxWell)   ; => false — not Bob's context
(v/ask? kb '(flies Tweety) 'CxWell)                    ; => false — base believes nothing
```

`(believes Alice (flies Tweety))` is `(flies Tweety)` asked in `CxAgentAlice`. The agent
symbol names the context by a fixed convention — `Alice` ↦ `CxAgentAlice`
(`vaelii.impl.modal`) — and a generated name passes exactly the checks a hand-written
context name does (`naming/context?`), so nothing downstream can tell a minted agent
context from any other. A variable in the proposition binds through the projection:
`(believes Alice (flies ?x))` answers `{?x Tweety}`.

## The prover

`BeliefProjectionProver` (in `vaelii.impl.provers`, in `default-provers`) recognizes a
modal goal and sub-queries the inner sentence in the agent's context. Four decisions:

- **Applicable** to a registered modal predicate, of arity 2, whose **agent argument is
  ground** and yields a legal context name, over a sentence-shaped proposition. An
  unbound agent — `(believes ?who P)` — is *not* claimed: that would mean "search every
  agent's context", a different and far costlier operation, so it is excluded and left to
  whatever else answers it.
- **Cost** `:compute` — a projection is a sub-query through the registry, not a lookup.
- **Completeness** 50 — it *augments*. `(believes A P)` may also be a plain stored fact,
  and `believes` is a real relation you may want to assert; the fact prover stays in play,
  and a stored belief and a projected one fold to one answer rather than double-counting.
- **Solve** proves `P` in the agent's context — the agent's, never the asker's, which is
  what keeps one agent's beliefs out of another's answers.

## The headline property: contradictory agents coexist

```clojure
(v/assert kb '(flies Tweety)       'CxAgentAlice)
(v/assert kb '(not (flies Tweety)) 'CxAgentBob)

(v/ask? kb '(believes Alice (flies Tweety))       'CxWell)  ; => true
(v/ask? kb '(believes Bob   (not (flies Tweety))) 'CxWell)  ; => true
(v/conflicts kb)       ; => []  — the two share no context, so no settle ever sees a clash
(v/contradictions kb)  ; => []
```

Alice's `CxAgentAlice` and Bob's `CxAgentBob` share no `genlCx` ancestor, so no context
sees both the claim and its negation and no contradiction is raised. This is the property
no Datalog / SPARQL / DL rival can field, and it falls out of the lattice by construction
rather than being engineered here.

## Independence, and inheriting base

An agent context has **no `genlCx` edge** by default, so it is independent: the agent
believes exactly what is asserted in its context, and nothing true in base leaks in. That
is the honest default for modal use — an agent who believes a falsehood should not thereby
contradict base. To let an agent see base too, add the edge yourself:

```clojure
(v/assert kb '(green Grass) 'CxUniverse)                 ; a base fact
(v/ask? kb '(believes Alice (green Grass)) 'CxWell)      ; => false — Alice is independent
(v/assert kb '(genlCx CxAgentBob CxUniverse) 'CxUniverse); Bob opts in
(v/ask? kb '(believes Bob (green Grass)) 'CxWell)        ; => true
```

## More than one modal predicate

Which predicates project is a KB property, not a hard-coded set. `believes` ships granted
in `CxCore`; `knows`, `desires`, `intends` are the same projection under a different
predicate, and one assertion away:

```clojure
(v/register-modal-predicate! kb 'knows)   ; grants (modalPredicate knows) in CxCore
;; or scope the grant to one theory:
(v/register-modal-predicate! kb 'knows 'CxPsychology)
```

`(modalPredicate P)` is read **scoped from the asking context**, exactly as
`abduciblePredicate` is — so it is a *policy of the context that grants it*: one theory
may read `knows` modally while another, seeing the same predicate, does not. An
unregistered predicate is never projected, which is why the table is open but closed by
default.

This scoping is also what governs **nested** belief. `(believes A (believes B P))` proves
`(believes B P)` in `A`'s context, and the inner `believes` projects only if the grant is
visible *there*. An independent `CxAgentA` cannot see the `CxCore` grant, so by default the
inner `believes` is an ordinary literal and the nested query is simply false — there is no
recursion to speak of. Give `A` a `genlCx` edge that reaches the grant and the nesting
projects through. That is the whole of the nesting story: a consequence of where the marker
is visible, not a modal-logic schema.

## What is out of scope

It is **query-only**: the caller asserts an agent's beliefs into the agent
context directly, and the projector reads them back — consistent with how `unknown` /
`thereExists` are query-only operators. A belief that happens to match a base forward rule
fires it like any other fact; an independent agent context may then have nowhere to place
the conclusion, which surfaces as a harmless no-placement notice in `violations`, not a
contradiction.

Out of scope: assertion routing (asserting `(believes Alice P)` to store `P` in Alice's
context — a write that lands a *different* sentence elsewhere, for which no
retraction-symmetric form exists), agent-context lifecycle (garbage-collecting or merging
agent contexts), and modal logic proper. This is a projector, not a modal calculus.

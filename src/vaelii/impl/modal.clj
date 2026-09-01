;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.modal
  "Beliefs without new primitives.

  Two agents can believe contradictory things without the KB being inconsistent —
  that is what a context lattice is *for*, and the engine already has the lattice.
  What this namespace adds is the **projection**: a way to ask what an agent believes
  and get the answer from inside that agent's own context.

  The whole idea is one convention and one prover, over machinery that already exists:

  - **The convention** lives here — a deterministic bijection between an agent symbol
    and its context.  Agent `Alice` owns context `CxAgentAlice`; asking
    `(believes Alice P)` is answering `P` in `CxAgentAlice` rather than in the asker's
    context.  A generated name passes exactly the checks a hand-written context name
    does (`naming/context?`), so nothing downstream can tell a minted agent context
    from any other.
  - **The prover** lives in `vaelii.impl.provers` (`BeliefProjectionProver`), where the
    `Prover` protocol and the registry are — it recognizes a modal goal and sub-queries
    the inner sentence in the agent's context.

  An agent context is an **ordinary context** created through the ordinary assert path:
  the caller asserts `Alice`'s beliefs into `CxAgentAlice` and the projector reads them
  back.  Nothing here teaches the JTMS, the taxonomy or the index about agents — a
  belief is a fact in a context, and an agent context is a context like any other.

  **Which predicates project is a KB property, not a hard-coded set.**  `believes` is
  one of them, and `knows` / `desires` / `intends` are the same projection under a
  different predicate; a predicate projects exactly when `(modal_predicate P)` is
  believed where the query is asked — read context-scoped through `has-prop? :modal`,
  the way `abducible_predicate` grants abduction.  So the table is open (assert the
  marker to add one) and it is a *policy of a context* rather than a global switch.

  This is a **projector, not a modal logic**: no axiom schema (K, T, 4, 5), and no
  special handling of a nested `(believes A (believes B P))` beyond what falls out of
  the marker's own visibility.  See docs/belief.md."
  (:require [clojure.string :as str]
            [vaelii.impl.naming :as naming]))

(def agent-context-prefix
  "The prefix that turns an agent symbol into its context name.  No separator
  punctuation: `naming/context?` admits only `Cx[A-Z][A-Za-z0-9]*`, so the bench's
  `CxAgent_<a>` spelling — with an underscore — is not a legal context here.  The
  capital `A` of `Agent` is what satisfies the `[A-Z]` a context name needs right after
  `Cx`, so the agent's own initial is free to be anything alphanumeric."
  "CxAgent")

(defn context-of-agent
  "The canonical context for `agent` — `Alice` ↦ `CxAgentAlice`.  The
  forward half of the bijection; the inverse is `agent-of-context`."
  [agent]
  (symbol (str agent-context-prefix (name agent))))

(defn agent-context?
  "True iff `ctx` names an agent context — a `CxAgent…` context this convention
  minted.  A real context spelled `CxAgent…` would be read as one too: the `CxAgent`
  span is reserved for agents, the price of having no separator character available."
  [ctx]
  (and (symbol? ctx)
       (str/starts-with? (name ctx) agent-context-prefix)
       (> (count (name ctx)) (count agent-context-prefix))))

(defn agent-of-context
  "The agent an agent context belongs to — `CxAgentAlice` ↦ `Alice` — or nil when `ctx`
  is not an agent context.  The inverse of `context-of-agent`, so the two round-trip."
  [ctx]
  (when (agent-context? ctx)
    (symbol (subs (name ctx) (count agent-context-prefix)))))

(defn projectable-agent?
  "True iff `agent` can be projected to a legal, round-tripping agent context: a ground
  symbol whose generated `CxAgent…` name passes `naming/context?`.  A `?variable` agent
  fails here — its name would carry a `?`, which no context name may — so this one check
  enforces both invariants the projector rests on: **ground agent only** (an unbound
  agent has no single context to route into) and **legal name** (a minted context name
  must validate exactly as a hand-written one does)."
  [agent]
  (and (symbol? agent)
       (naming/context? (context-of-agent agent))))

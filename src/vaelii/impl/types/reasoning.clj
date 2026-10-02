;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns ^{:clojure.tools.namespace.repl/load false :clojure.tools.namespace.repl/unload false}
 vaelii.impl.types.reasoning
  "The `Reasoning` record and its readers, as a held namespace (`vaelii.impl.types.prover`
  states what that means).  A KB holds one `Reasoning` value in a volatile under its
  `:reasoning` field: the belief network, the taxonomy, and every atom a recover or a
  settle fills.  `vaelii.impl.kb/empty-reasoning` builds an empty one.

  A `Reasoning` value is not a store.  A KB's two stores, `:records` and `:index`, are
  durable and are reached through `vaelii.impl.protocols`, and both survive the process
  that wrote them.  A `Reasoning` value lives in this process alone:
  `vaelii.impl.recovery/recover` rebuilds it from the records, as `vaelii.impl.reindex`
  rebuilds the index from them.  `vaelii.impl.reasoning-image` writes one to a directory so
  that an open can install it in place of a recover, and a KB that declines the image runs
  the recover instead.

  A background rebuild's install replaces the whole value with one `vreset!`
  (`vaelii.impl.recovery`), so the belief a KB holds changes in one step.  A reader
  that must read the network and the taxonomy of one belief reads them through one
  dereference: `vaelii.impl.kb/read-view` returns a KB whose volatile holds the current
  value and is never reset, and `vaelii.core`'s public reads run against it while an
  install is pending.

  Each reader below is inlined at its call site, so `(taxonomy kb)` compiles to
  `(:taxonomy @(:reasoning kb))`: one field read, one volatile read and one field read.")

;; `solver` is not here: it is configuration the caller sets, and a rebuild shares it
;; with the KB it rebuilds (`kb/rebuild-shared`).  Everything here is empty on a new KB
;; and rebuilt by `recover`, or is a cache a missing read refills.
;;
;; `program` holds the last edge Program handed to the solver (the ASP backend in
;; vaelii.impl.asp.edge).  It is kept because belief is *self-erasing evidence*: once
;; settle defeats one side of a tie, that side stops matching, so the very nogood that
;; produced the contested set is no longer derivable from the KB.  Recomputing it after the
;; fact yields nothing.  Anything wanting to ask what the tie *was* — which beliefs were
;; forced and which were an arbitrary pick (`asp.edge/classify`) — has to read the program
;; the decision was actually made from.
;;
;; `violations` holds the definitional constraints a *derived* conclusion would have broken
;; during the last chaining run — see `place-conclusion` and `violations`.
;;
;; `recheck` is the exception re-check queue: `{rule-handle -> triggers}` for the rules
;; whose `exceptWhen` query may have flipped since the last settle, posted by the triggers
;; (a fact arriving or leaving on one of the exception's predicates, or any genl/genlCx
;; edge change) and drained by `settle`.  `triggers` is the set of sentences that moved —
;; which firings of that rule to re-evaluate — or `:all` when there is no such sentence and
;; all of them must be.  Nothing here caches whether an exception *holds* — the queue says
;; what to re-evaluate, and the re-evaluation says what is true.
;;
;; `settle-stats` is instrumentation for the exception fixpoint: `:iterations` counts the
;; passes in which the blocked set actually moved (0 = nothing blocked, 1 = one pass
;; sufficed), `:passes` the total loop passes including the confirming one, and
;; `:histogram` the distribution of `:iterations` since the last reset.
;;
;; `qcn` is where a qualitative constraint network **lives between reads**: an atom of
;; `{[calculus-name context] -> {:read … :clock n}}`, stamped with `observe/change-clock`
;; and re-derived the moment that has moved (`vaelii.impl.qcn-kb`).  Per KB rather than
;; global, because two KBs in one JVM share the clock but not their content.
;;
;; `matches` is the literal cache (`vaelii.impl.literal-cache`): an atom of
;; `{[canonical-literal context hierarchical? arg-root?] -> {:value … :clock n}}` holding
;; what `matches-visible` answered, α-renamed so two spellings of one question share an
;; entry and stamped with `observe/change-clock` so any mutation retires it.  Per KB for
;; the same reason `qcn` is.  A declared field rather than a key on the record's extension
;; map, because `matches-visible` reads it on every retrieval and an extension-map key
;; costs a hash lookup where a field costs none.  Every other field here is declared for
;; the same reason.
;;
;; `rule-antecedents` and `rule-contexts` are the rule rosters `special` bumps on every
;; rule index/unindex and reads per settle for the visibility seeds.  `solve-rules` is the
;; third, `{context -> #{handle}}` of the rules a solve reads (`rules/solve-sentex?`),
;; which `do/label` reads in place of each context's extent.  All three hold storage, not
;; belief.  None is stored, and recovery replays belief and the taxonomy rather than rule
;; indexing, so `rebuild-rule-roster!` is what refills them on a recovered, reopened or
;; forked KB.
;;
;; `excepted` is the visibility roster beside `:opposed`, and kept the same way: `{context
;; -> {except-handle -> hidden-handle}}` for the stored `(except (sentexHandle H))` facts,
;; maintained O(1) at the store and removal choke points and rebuilt by `recover`.  It
;; holds **storage**, not belief — an except's own handle is what a reader checks `in?`
;; against — for the reason `:opposed` holds storage: belief moves without a sentex
;; arriving or leaving, so a roster that tried to track it would be maintained at a choke
;; point that does not exist.  `res/excepted-handles` reads it per placement and per
;; candidate justification (docs/exceptions.md, "Visibility removal").
;;
;; `withdrawn` is the per-reader answer built from `nogood-candidates` and `excepted`,
;; `{reader -> #{handle}}`, emptied whenever either input or the network moves.  Each
;; emptying moves its generation, so a reader thread cannot install an answer computed
;; before it.
;;
;; `minted` is the mint roster, `{:by-term {x #{handle}} :by-context {context #{handle}}}`:
;; every stored `(t x)` or `(genl x t)` an `arg`, `genlArg` or `interArg` justification has
;; concluded, which `special/subsumed-mint-blocks` reads instead of the index
;; (docs/argtypes.md).  A record stays in it until it leaves the store.  Kept at the one
;; place a mint justification is added (`special/entail-arg-type`) and the one place a
;; record leaves (`integrate/sentex-removed!`), and rebuilt by `recover`.  Its `:departed`
;; is the queue of removed records that can have subsumed a mint
;; (`special/note-departure!`), which every settle drains.
;;
;; `nogood-candidates` is the candidate index of the nogood families a reader decides,
;; `{:self #{handle} :converse #{handle} :negation #{handle} … :inherited …}`: every stored
;; ground binary self tuple, every stored ground binary tuple with a stored converse, the
;; arity candidates, and the negation pairs of every body stored in both polarities, kept
;; at the store and removal choke points and rebuilt by `recover` like `:opposed`; and the
;; inherited clashes with their vantages, `{:by-set {members ngmap} :by-vantage {vantage
;; #{members}}}`, which each settle re-finds.  No verdict is stored: a reader at or below a
;; vantage decides from its own view (`vaelii.impl.decide`, docs/nmtms.md, "Nogoods decided
;; at the reader").
;; `own-readings` is what the last settle read at each context holding a handle of those
;; candidates' consequence closure, so the next settle publishes the own-context belief a
;; decided loser moved (`readings/reader-moves`).  `read-reports` is the report memo of the last reading of
;; those families' clashes (`clashes/read-clashes`).
;;
;; `kb/empty-reasoning` states what the remaining fields hold, beside the expression that
;; makes each one.
(defrecord Reasoning [tms taxonomy program violations recheck refused
                      settle-stats chain-stats opposed preserving preserved-clashes excepted
                      meta-except-count rule-antecedents rule-contexts solve-rules
                      supersessions qcn qcn-joined matches closures
                      withdrawn respell except-moves
                      minted nogood-candidates own-readings read-reports])

(defn of
  "The `Reasoning` value `kb` holds now."
  {:inline (fn [kb] `(deref (:reasoning ~kb)))}
  [kb]
  @(:reasoning kb))

(defn tms
  "`kb`'s belief network."
  {:inline (fn [kb] `(:tms (deref (:reasoning ~kb))))}
  [kb]
  (:tms @(:reasoning kb)))

(defn taxonomy
  "`kb`'s taxonomy atom."
  {:inline (fn [kb] `(:taxonomy (deref (:reasoning ~kb))))}
  [kb]
  (:taxonomy @(:reasoning kb)))

(defn program
  "`kb`'s `:program` atom."
  {:inline (fn [kb] `(:program (deref (:reasoning ~kb))))}
  [kb]
  (:program @(:reasoning kb)))

(defn violations
  "`kb`'s `:violations` atom."
  {:inline (fn [kb] `(:violations (deref (:reasoning ~kb))))}
  [kb]
  (:violations @(:reasoning kb)))

(defn recheck
  "`kb`'s `:recheck` atom."
  {:inline (fn [kb] `(:recheck (deref (:reasoning ~kb))))}
  [kb]
  (:recheck @(:reasoning kb)))

(defn refused
  "`kb`'s `:refused` atom."
  {:inline (fn [kb] `(:refused (deref (:reasoning ~kb))))}
  [kb]
  (:refused @(:reasoning kb)))

(defn settle-stats
  "`kb`'s `:settle-stats` atom."
  {:inline (fn [kb] `(:settle-stats (deref (:reasoning ~kb))))}
  [kb]
  (:settle-stats @(:reasoning kb)))

(defn chain-stats
  "`kb`'s `:chain-stats` atom."
  {:inline (fn [kb] `(:chain-stats (deref (:reasoning ~kb))))}
  [kb]
  (:chain-stats @(:reasoning kb)))

(defn opposed
  "`kb`'s `:opposed` atom."
  {:inline (fn [kb] `(:opposed (deref (:reasoning ~kb))))}
  [kb]
  (:opposed @(:reasoning kb)))

(defn nogood-candidates
  "`kb`'s `:nogood-candidates` atom."
  {:inline (fn [kb] `(:nogood-candidates (deref (:reasoning ~kb))))}
  [kb]
  (:nogood-candidates @(:reasoning kb)))

(defn read-reports
  "`kb`'s `:read-reports` atom."
  {:inline (fn [kb] `(:read-reports (deref (:reasoning ~kb))))}
  [kb]
  (:read-reports @(:reasoning kb)))

(defn own-readings
  "`kb`'s `:own-readings` atom."
  {:inline (fn [kb] `(:own-readings (deref (:reasoning ~kb))))}
  [kb]
  (:own-readings @(:reasoning kb)))

(defn preserving
  "`kb`'s `:preserving` atom."
  {:inline (fn [kb] `(:preserving (deref (:reasoning ~kb))))}
  [kb]
  (:preserving @(:reasoning kb)))

(defn preserved-clashes
  "`kb`'s `:preserved-clashes` atom."
  {:inline (fn [kb] `(:preserved-clashes (deref (:reasoning ~kb))))}
  [kb]
  (:preserved-clashes @(:reasoning kb)))

(defn excepted
  "`kb`'s `:excepted` atom."
  {:inline (fn [kb] `(:excepted (deref (:reasoning ~kb))))}
  [kb]
  (:excepted @(:reasoning kb)))

(defn withdrawn
  "`kb`'s `:withdrawn` atom."
  {:inline (fn [kb] `(:withdrawn (deref (:reasoning ~kb))))}
  [kb]
  (:withdrawn @(:reasoning kb)))

(defn meta-except-count
  "`kb`'s `:meta-except-count` atom."
  {:inline (fn [kb] `(:meta-except-count (deref (:reasoning ~kb))))}
  [kb]
  (:meta-except-count @(:reasoning kb)))

(defn rule-antecedents
  "`kb`'s `:rule-antecedents` atom."
  {:inline (fn [kb] `(:rule-antecedents (deref (:reasoning ~kb))))}
  [kb]
  (:rule-antecedents @(:reasoning kb)))

(defn rule-contexts
  "`kb`'s `:rule-contexts` atom."
  {:inline (fn [kb] `(:rule-contexts (deref (:reasoning ~kb))))}
  [kb]
  (:rule-contexts @(:reasoning kb)))

(defn solve-rules
  "`kb`'s `:solve-rules` atom."
  {:inline (fn [kb] `(:solve-rules (deref (:reasoning ~kb))))}
  [kb]
  (:solve-rules @(:reasoning kb)))

(defn minted
  "`kb`'s `:minted` atom."
  {:inline (fn [kb] `(:minted (deref (:reasoning ~kb))))}
  [kb]
  (:minted @(:reasoning kb)))

(defn supersessions
  "`kb`'s `:supersessions` atom."
  {:inline (fn [kb] `(:supersessions (deref (:reasoning ~kb))))}
  [kb]
  (:supersessions @(:reasoning kb)))

(defn respell
  "`kb`'s `:respell` atom."
  {:inline (fn [kb] `(:respell (deref (:reasoning ~kb))))}
  [kb]
  (:respell @(:reasoning kb)))

(defn except-moves
  "`kb`'s `:except-moves` atom."
  {:inline (fn [kb] `(:except-moves (deref (:reasoning ~kb))))}
  [kb]
  (:except-moves @(:reasoning kb)))

(defn qcn
  "`kb`'s `:qcn` atom."
  {:inline (fn [kb] `(:qcn (deref (:reasoning ~kb))))}
  [kb]
  (:qcn @(:reasoning kb)))

(defn qcn-joined
  "`kb`'s `:qcn-joined` atom."
  {:inline (fn [kb] `(:qcn-joined (deref (:reasoning ~kb))))}
  [kb]
  (:qcn-joined @(:reasoning kb)))

(defn matches
  "`kb`'s `:matches` atom."
  {:inline (fn [kb] `(:matches (deref (:reasoning ~kb))))}
  [kb]
  (:matches @(:reasoning kb)))

(defn closures
  "`kb`'s `:closures` atom."
  {:inline (fn [kb] `(:closures (deref (:reasoning ~kb))))}
  [kb]
  (:closures @(:reasoning kb)))

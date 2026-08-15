;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.protocols
  "Storage protocols so the record store and index store each have swappable
  implementations (in-memory by default, on-disk for durability, or an alternate KV
  store later).  The rest of the system programs against these protocols and never
  against a concrete backend.")

(defprotocol RecordStore
  "The record store — canonical sentexes and justifications, keyed by integer handle.
  The durable ground truth: everything else the KB holds is derived from it."
  (put-sentex      [store sentex] "Persist a sentex; return its handle.")
  (get-sentex       [store id]     "Fetch a sentex by handle, or nil.")
  (delete-sentex!   [store id]     "Remove a sentex record.")
  (put-justification   [store d]      "Persist a justification; return its handle.")
  (get-justification    [store id]     "Fetch a justification by handle, or nil.")
  (delete-justification! [store id]    "Remove a justification record.")
  (next-id         [store]        "Allocate the next monotonic handle — one above every
                                    handle the store holds, including one that arrived as
                                    an explicit `:id` on a put rather than from here.  A
                                    handle is an identity, so no store may issue one twice.")
  ;; provenance — an open bookkeeping map per handle (creator, creation date, and
  ;; whatever else an application layers on), kept *beside* the record rather than as
  ;; fields on it, so the sentex/justification shape never grows.  Never read by belief,
  ;; so it cannot affect order independence; torn down with the record it annotates.
  (put-provenance    [store id prov] "Persist the provenance map for handle `id` (overwrites).")
  (get-provenance    [store id]      "The provenance map for handle `id`, or nil.")
  (delete-provenance! [store id]     "Remove the provenance for handle `id`.")
  ;; enumeration + premise tracking, for recovery of the in-memory graph
  (sentex-ids       [store]           "All live sentex handles.")
  (justification-ids    [store]           "All live justification handles.")
  (mark-premise    [store id strength] "Record a handle as an asserted premise at `strength`.")
  (unmark-premise!  [store id]        "Record that a handle is no longer a premise.")
  (premise-ids      [store]           "All handles currently marked as premises.")
  (premise-strength [store id]        "The recorded assumption strength of a premise handle.")
  (clear-records!   [store]           "Remove every stored record (wipe the whole store)."))

(defprotocol IndexStore
  "The index store — the count-aware trie, the secondary root indexes, the
  rule predicate index, the exception re-check index, and the inverted term index.
  Every entry is derived from the records, so it can be thrown away and rebuilt
  (`vaelii.impl.reindex`); it needs no durability of its own."
  (index-sentex    [store sentex handle] "Insert a ground sentex handle into the trie.")
  (unindex-sentex!  [store sentex handle] "Remove a sentex handle from the trie.")
  (lookup    [store pattern]       "Handles whose path matches a full pattern.")
  (count-at  [store prefix]        "Sentex count under a path prefix.")
  (children  [store prefix]        "Child tokens registered under an interior prefix.")
  ;; How *many* children, without building them.  This is the trie's own distinct-value
  ;; count at a position — what the query planner's cost model divides by
  ;; (`vaelii.impl.plan`) — and it is asked once per literal per plan, so it must not
  ;; scale with the KB.  `(count (children …))` does: both implementations materialize
  ;; the child set to answer `children`, which turns planning a fixed conjunction into
  ;; work proportional to how many distinct values sit at that position.  Every *storage*
  ;; backend answers the cardinality without building the members — a set's count, or a
  ;; node's edge-array span — so the count is its own read rather than a projection of
  ;; them.  The **fork decorator is the exception, and knowingly**: a key the fork has
  ;; written under is no longer inherited, so its count is `(count merged-members)` and
  ;; the base's set is materialized after all (docs/overlay.md).  A fork trades this op
  ;; for the seam, on the nodes it writes.
  (count-children [store prefix]   "How many child tokens sit under an interior prefix.")
  ;; secondary roots — the trie is ordered [pred args… ctx], so it can only narrow
  ;; left-to-right.  These give extent *and* cardinality from the other directions —
  ;; by context, by functor, and by argument position — without a walk of the trie.
  ;; Cardinality is one stored count on a base store and the merge above on a fork.
  (sentexes-in-context   [store context]  "Handles of sentexes asserted in `context`.")
  (count-in-context      [store context]  "How many sentexes are in `context`.")
  (sentexes-with-functor [store pred]     "Handles of fact sentexes whose functor is `pred` (any arity, either polarity).")
  (count-with-functor    [store pred]     "How many fact sentexes have functor `pred`.")
  (sentexes-with-arg     [store pos term] "Handles of fact sentexes with `term` at 1-based argument `pos`.")
  (count-with-arg        [store pos term] "How many fact sentexes have `term` at `pos`.")
  ;; multi-column narrowing: one intersection of the functor root and every named argument
  ;; root, so a query that knows several terms narrows on all of them at once instead
  ;; of one column with the rest deferred to a post-fetch filter.  `pred` may be nil
  ;; (a variable-functor pattern); `pos-terms` is a seq of `[pos term]`.
  (sentexes-with-args    [store pred pos-terms] "Handles with functor `pred` AND each `[pos term]` — one set intersection.")
  ;; rule index: rules are sentexes indexed additionally by their predicates.  Both
  ;; predicate sets are *complete* — every rule, whatever its direction — so "what
  ;; could conclude P?" is answerable for a forward-only rule.  Direction and
  ;; defeasibility are NOT mirrored here: they live on the sentex record (the
  ;; `set/*Rule` wrapper canonicalizes into it), and chaining reads them from there.
  (index-rule   [store handle ante-preds conseq-pred] "Register a rule handle by its predicates.")
  (unindex-rule! [store handle ante-preds conseq-pred] "Deregister a rule handle.")
  (rules-by-antecedent [store pred] "Handles of rules with an antecedent on pred.")
  (rules-by-consequent [store pred] "Handles of rules concluding pred.")
  ;; exception (re-check) index: a rule carrying an `exceptWhen` is posted under every
  ;; predicate its exception query mentions, and into a roster of all such rules.  It is
  ;; at *rule* granularity, never per firing — a rule handle is already an antecedent of
  ;; every justification it licenses, so each conclusion it produced is reachable through
  ;; the existing consequence links.  It stores **no truth value**: it answers "which
  ;; rules might need re-checking", never "does the exception hold", so unlike a cached
  ;; closure it has nothing that can drift from belief.  The predicates are passed in
  ;; rather than read off the sentex, so the index does not depend on how a rule spells
  ;; its exception.
  (index-exception    [store handle preds] "Register a rule handle under each predicate its exception mentions.")
  (unindex-exception!  [store handle preds] "Deregister a rule handle from its exception predicates.")
  (rules-with-exception-on [store pred] "Handles of rules whose exception mentions pred.")
  (exception-rules         [store]      "Handles of every rule carrying an exception.")
  (exception-rule?         [store handle] "Is `handle` in the exception/watched-rule roster? (O(1) membership — the firing-path gate.)")
  ;; term (inverted) index: every sentex is findable by any term it contains.  The keys
  ;; are `sentex/index-terms` — every *symbol*, at every depth, plus each ground compound
  ;; between `sentex/*min-indexed-depth*` and `sentex/max-indexed-compound`.  So this is
  ;; exact for a symbol and, for a compound outside those bounds, holds only the sentexes
  ;; that nest it deep enough; `kb/find-sentexes` is the exact read for a compound, which
  ;; it gets from the atoms' postings plus a verify against the record.
  (sentexes-with-term  [store term]  "Handles of sentexes the term index keys by `term`.")
  (sentexes-with-terms [store terms] "Handles of sentexes keyed by all `terms` — one intersection.")
  ;; the term roster: the *names* the term index is keyed by, held as one set beside the
  ;; postings so the vocabulary can be listed and counted without walking the records.
  ;; A name enters when the first sentex mentions it and leaves with the last, derived
  ;; from the postings themselves, so the roster cannot drift from what is indexed.
  (terms      [store] "Every symbol term the index is keyed by — the KB's vocabulary, unordered.")
  (term-count [store] "How many distinct symbol terms the index is keyed by (the roster's own count, no walk).")
  ;; the portable projection.  Every index — the flat-map one, the dense one, the
  ;; columnar one with a native int-token trie — answers this protocol, so the
  ;; `[structured-key value]` entry shape is what they have in *common* rather than what
  ;; any one of them holds.  That is what a dump writes and reads back
  ;; (`vaelii.impl.io.export` / `.import`), and it is why an index written by one backend
  ;; loads into another.  A backend's own resident layout is a different artifact
  ;; entirely, and not this.
  ;;
  ;; `index-load` is bare, not `!`: it installs derived state into an *empty* index and
  ;; destroys no knowledge.  Loading over a populated one merges rather than replaces,
  ;; so the caller owes the emptiness.
  (index-entries [store]         "Every index entry as a lazy `[key value]` seq — the portable projection.")
  (index-load    [store entries] "Install `[key value]` entries into an empty index, in this store's own representation.")
  (clear-index!        [store]       "Remove every index entry (wipe the store — `reindex` rebuilds)."))

;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.integrate
  "Store mutation is the seam: the two choke points everything that stores or
  removes a sentex must pass through.

  Fourth layer of the engine stack (kb <- checks <- special <- integrate <- chain
  <- settle): the table of what each special predicate *means* lives below in
  `vaelii.impl.special`; what lives here is the guarantee that its arms — and the
  exception re-check queue they feed — are never skipped.  exceptWhen correctness
  depends on every mutation path posting a re-check.  Scattering that call across the
  mutation sites makes a missed one invisible — the failure mode is stale excepted
  conclusions, silently, and the next mutation path (a bulk load, a new merge) is one
  forgotten call from that bug.  So the sequence is stated once per direction:

    sentex-added     integrate through the table + queue the re-check — the assert
                     path's reflection of a sentex that just landed (storage and
                     indexing having happened in `kb/create-sentex`, which is the
                     store-side half of the same seam)
    sentex-removed!  disintegrate + unindex + delete the record + queue the
                     re-check — the one teardown, shared by `retract!` and the
                     excepted-conclusion sweep

  The derivation path's twin (`special/derived-sentex-added`) sits beside the table
  instead, because the equality arms are themselves derivation sites and must reach
  it from below.  The triggers that are *not* store mutations stay explicit at
  their own sites: a taxonomy edge change (posted inside the genl / genlContext
  arms — the trigger is the closure moving, not the sentex), rule indexing (posted
  in `special/index-rule-sentex` — the trigger is the rule gaining an exception to
  evaluate), and `recover` (nothing about blocking survives a restart, so it
  re-queues everything wholesale)."
  (:require [vaelii.impl.kb :as kb]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.special :as special]))

(def ^:dynamic *removed-sink*
  "A volatile holding a vector of the sentexes that have left the store, or nil — the
  default, and the removal choke point records nothing.

  What a caller needs when it must act on **the region a teardown touched** rather than
  on the whole KB.  `core`'s reified-NAT orphan sweep is the one that does: an orphaned
  constant is one some departing sentex stopped referencing, so the constants those
  sentexes named are the whole of what it has to ask about.  The removals are not all in
  one place — the dependency-directed sweep produces some, the settle that follows
  produces more (`settle/sweep-excepted!`), and the sweep's own retractions produce more
  again — so recording them where every removal already passes is what makes the
  narrowed question equal to the whole-KB one.

  A volatile rather than an atom: the engine is single-writer, and this sits on the
  teardown path."
  nil)

(defn removal-sink
  "The sink to record a teardown's removals into: the bound one when there is one, a
  fresh volatile otherwise.  **Reused rather than shadowed**, so a nested teardown
  appends to the record its caller is still reading — which is what lets the orphan
  sweep see what its own retractions removed, and so find a cascade.

  `want?` false answers **nil**, and a nil sink is the one that records nothing.  The
  record is the reified-NAT sweep's and only that sweep's, so a KB declaring no
  reifiable function has nothing to do with it — and the record is not free: it retains
  every sentex a teardown removes for as long as the teardown runs, which on a cascade
  is the whole cascade held in a vector nobody reads.  The caller passes the gate it was
  going to consult anyway (`nat/any-reifiable-functions?`), so the KBs that never reify
  pay the retention of nothing at all."
  ([] (removal-sink true))
  ([want?] (when want? (or *removed-sink* (volatile! [])))))

(defn sentex-added
  "Everything that must happen because a sentex just landed in the store as a
  premise: reflect it into the caches through the special-predicate table, and
  queue the exception re-check its arrival may have flipped.  Returns what the
  table walk returns — the `{:new :superseded :violations}` migration map for an
  equality sentex, nil otherwise.

  Runs whether or not the sentex is newly created: re-asserting an existing
  sentence re-adds premise support, which can flip belief, so the re-check must be
  posted either way (the cache adds are refcounted and idempotent)."
  [kb sentex handle]
  (let [result (special/integrate-sentex kb sentex handle)]
    (special/recheck-on-sentence kb (:sentence sentex))
    result))

(defn sentex-removed!
  "Everything that must happen because a sentex is leaving the store: reverse its
  cache effects through the table, drop it from every index, delete the record, and
  queue the exception re-check — a fact *leaving* is as much a re-check trigger as
  one arriving, since its departure may be exactly what releases some rule's
  exception.

  Records the sentex into `*removed-sink*` when one is bound, which is how a caller
  learns the region a teardown removed without every removal path having to report it."
  [kb sentex]
  ;; the removal record, for a caller scoping its own follow-up work to what left
  (when-let [sink *removed-sink*] (vswap! sink conj sentex))
  (special/disintegrate-sentex! kb sentex)
  (p/unindex-sentex! (:index kb) sentex (:id sentex))
  (p/delete-sentex! (:records kb) (:id sentex))
  ;; the remove-side seam for an incremental matcher's alpha memories, mirroring the
  ;; add in `kb/create-sentex` — a no-op unless one is engaged
  (observe/notify-remove kb sentex)
  ;; and the change clock, mirroring the same line there
  (observe/note-change)
  ;; the handle cache holds "this sentence is stored at this handle", and this is the
  ;; one event that falsifies it — so the invalidation belongs beside the removal
  ;; itself, not in the caller that happens to have a cache bound
  (observe/forget-handle! (:sentence sentex) (:context sentex))
  ;; maintain the P/¬P coincidence set (this removal may have dissolved an opposing
  ;; pair); read after `unindex-sentex!` so the departing fact is already gone
  (kb/note-opposed! kb (:sentence sentex))
  (special/recheck-on-sentence kb (:sentence sentex)))

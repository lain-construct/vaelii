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
  exception."
  [kb sentex]
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

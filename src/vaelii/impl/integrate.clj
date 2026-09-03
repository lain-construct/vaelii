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
    symmetrize-      the third direction, and the only one that moves a record
      existing       without moving a handle: a late `(symmetric P)` mark re-spelling
                     the rows stored before it and folding a mirrored pair into one
                     (see the section at the foot of this namespace)

  The derivation path's twin (`special/derived-sentex-added`) sits beside the table
  instead, because the equality arms are themselves derivation sites and must reach
  it from below.  The triggers that are *not* store mutations stay explicit at
  their own sites: a taxonomy edge change (posted inside the genl / genlCx
  arms — the trigger is the closure moving, not the sentex), rule indexing (posted
  in `special/index-rule-sentex` — the trigger is the rule gaining an exception to
  evaluate), and `recover` (nothing about blocking survives a restart, so it
  re-queues everything wholesale)."
  (:require [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.special :as special]
            [vaelii.impl.strength :as strength]
            [vaelii.impl.taxonomy :as tax]))

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
  ;; Capture the except target *before* any mutation — the sentex record is about to be
  ;; deleted, so extracting it afterward would depend on the local binding outliving
  ;; storage.  Binding here makes the before/after contract structural.
  (let [except-target (kb/except-target (:sentence sentex))]
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
    ;; ...and the visibility roster, the remove half of `kb/create-sentex`'s add.  Order
    ;; does not matter to this one — it reads the departing sentex rather than the index
    (kb/note-excepted! kb sentex false)
    ;; ...and the argument-preservation roster, the remove half of `kb/create-sentex`'s
    ;; add.  Reads the departing sentex rather than the index, so order does not matter
    ;; to this one either
    (kb/note-preserving! kb (:sentence sentex) false)
    ;; An except's departure changes the effective belief of the declaration it hid.
    ;; Run after the roster drop so the common reconcile reads the new visibility state;
    ;; report the visibility move explicitly because the exception record is already gone.
    (when except-target
      (special/reconcile-belief-change kb #{except-target} true))
    (special/recheck-on-sentence kb (:sentence sentex))))

;; ## A `symmetric` mark arriving after the facts
;;
;; The third store mutation, and the only one that moves a record without moving a
;; handle.  `(symmetric P)` is not a constraint mark — its effect is
;; **canonicalization**, the argument sort `res/kb-sentex` puts every `P` literal
;; through — so its retroactive half is not a sweep that convicts but a *storage
;; migration*: the rows stored before it have to end up spelled the way the rows stored
;; after it are, or the same knowledge in two arrival orders leaves two physical
;; sentexes for one proposition and the second retraction of the pair has nothing to
;; retract (vaelii#61).
;;
;; It lives here rather than beside the other retroactive arms in `special` because it
;; removes and re-stores records, and the store-mutation seam is this namespace's whole
;; subject.  Both callers sit above it: `core/assert-one` for a written declaration and
;; `chain/place-fact-conclusion` for a derived one, exactly as the two call
;; `special/equate-existing`.

(defn- respell!
  "Bring one stored sentex into `sentence`, its cache effects walked off the old spelling
  and back on under the new one.  The handle, the TMS node, the premise mark and every
  justification naming it are untouched, which is the whole point: nothing that rests on
  this row learns that its spelling moved, because for a re-canonicalization nothing that
  rests on it is about the spelling."
  [kb sx sentence]
  (special/disintegrate-sentex! kb sx)
  (let [sx' (kb/respell-sentex! kb sx sentence)]
    (special/integrate-sentex kb sx' (:id sx'))
    (special/recheck-on-sentence kb sentence)
    sx'))

(defn- fold-premise!
  "Give `survivor` the premise mark `doomed` carries, at the **stronger** of the two
  classes — `core/mark-premise`'s rule, and for its reason: the pair is one proposition
  asserted twice, and which of the two assertions the KB keeps must not decide how
  strongly it holds it.  A `doomed` that is not a premise leaves the survivor alone."
  [kb doomed survivor]
  (let [tms (:tms kb)]
    (when (jtms/premise? tms doomed)
      (let [s (strength/max (jtms/premise-strength tms survivor)
                            (jtms/premise-strength tms doomed))]
        (jtms/add-premise tms survivor s)
        (p/mark-premise (:records kb) survivor s)))))

(defn- fold-dependents!
  "Re-hang every justification that uses `doomed` as an antecedent on `survivor`, so the
  conclusions drawn through the row about to leave keep a witness across the fold rather
  than being swept and re-derived.  Same informant, same bindings, same strength — only
  the antecedent moves, and it moves to the row saying the same thing.

  A justification whose consequence is already `survivor` is skipped: rewritten it would
  name the survivor among its own antecedents, and a datum that grounds itself is
  groundable for ever.  Idempotent through `has-justification?`.

  Copied from the **record**, not from the network: the network keeps `graph-just`, which
  drops the firing's `:bindings` because belief never reads them — and the two things that
  do, an `exceptWhen` query and a NAF antecedent, re-evaluate per firing off the stored
  record.  A copy taken from the graph would leave the fold's justifications unable to
  answer either."
  [kb doomed survivor]
  (let [tms  (:tms kb)
        recs (:records kb)]
    (doseq [jid  (vec (jtms/dependents tms doomed))
            :let [j     (or (p/get-justification recs jid) (jtms/justification tms jid))
                  antes (mapv #(if (= % doomed) survivor %) (:antecedents j))]
            :when (and j (not= (:consequence j) survivor)
                       (not (jtms/has-justification? tms (:informant j) antes
                                                     (:consequence j))))]
      (let [nid  (p/next-id recs)
            just (assoc (jtms/->just nid (:informant j) antes (:consequence j)
                                     (:bindings j) (:strength j))
                        :out (set (:out j)))]
        (p/put-justification recs just)
        (jtms/add-justification tms just)))))

(defn- fold-row!
  "Fold the mirrored row `doomed` into `survivor` and take it out of the store: its
  premise mark, the conclusions drawn through it, and the handle-naming metas that would
  otherwise be left pointing at a record nothing holds.

  Then `jtms/retract!`, which is what `core/retract!` runs and does the same work here —
  drops the premise, relabels the region, and sweeps the row now that nothing is left
  resting on it — with the swept records handed to the removal choke point above.  A row
  the sweep leaves behind goes through that choke point directly, `core/retract!`'s other
  branch: an **inert** sentex (`assert-inert`) was never a TMS datum, so the retraction
  no-ops over it, and nothing else concludes this row — that is what picked it."
  [kb doomed survivor witness]
  (fold-dependents! kb doomed survivor)
  (fold-premise! kb doomed survivor)
  (special/migrate-handle-metas kb doomed survivor [witness]
                                (:context (p/get-sentex (:records kb) doomed)))
  (p/unmark-premise! (:records kb) doomed)
  (let [{:keys [removed-sentexes removed-justifications]} (jtms/retract! (:tms kb) doomed)
        gone (into [] (keep #(p/get-sentex (:records kb) %)) removed-sentexes)]
    (doseq [sx gone] (sentex-removed! kb sx))
    (doseq [jid removed-justifications] (p/delete-justification! (:records kb) jid)))
  (when-let [sx (p/get-sentex (:records kb) doomed)] (sentex-removed! kb sx)))

(defn- symmetrize-row!
  "Bring one stored row of a newly symmetric predicate into the canonical argument order,
  and return the handle it ends up at, or nil when it was canonical already.

  With no mirror stored the row is simply re-spelled where it lies.  Nothing else moves,
  which is why the lone case costs no handle: a caller holding it can still retract it,
  and the mirror asserted later now dedups to it instead of storing a second row.  With
  one stored, the pair folds into a single row and that row is re-spelled if it needs it.

  **Which of the pair survives is decided from what supports it, and only then from the
  handle.**  A row a rule concluded cannot be the one that leaves: folding it away would
  have to delete the justifications naming it as their consequence, and the JTMS
  deliberately has no door for that — belief is recomputed from the justifications, never
  edited around them — so the row would go on grounding itself through the ones left
  behind.  A row that is only a premise leaves cleanly, because `jtms/retract!` is exactly
  the sweep that takes it.  Between two rows that both stand on nothing but their own
  premise, the **lower** handle survives: it is the row the KB would hold had the
  declaration been written first, which is the claim being restored.  Nothing keys belief
  on the number; what keys on it is which of two handles a caller can still name, and
  answering that with the earlier one is what makes the issue's `(retract! h1)` mean the
  same thing in both orders.

  **Two rows a rule concluded are left alone**, pair and all — there is no clean row to
  fold — and for that pair the KB reads exactly as it read before this arm existed.  It
  takes two rules concluding one proposition's two spellings under a predicate nothing had
  yet declared symmetric."
  [kb sx witness]
  (let [ctx  (:context sx)
        want (kb/canonical-sentence kb (:sentence sx) ctx)]
    (when (not= want (:sentence sx))
      (let [tms    (:tms kb)
            self   (:id sx)
            mirror (kb/find-sentex-handle kb want ctx)
            ;; the row that can leave: the one nothing concludes, and the later of two
            doomed (cond (nil? mirror)                          nil
                         (seq (jtms/supports tms mirror))       (when (empty? (jtms/supports tms self)) self)
                         (seq (jtms/supports tms self))         mirror
                         :else                                  (max self mirror))]
        (cond
          ;; nothing to fold: the row is alone under this proposition and only spelled
          ;; the way the door used to spell it
          (nil? mirror)   (:id (respell! kb sx want))
          ;; both rows are concluded by a rule — neither can leave, so neither does
          (nil? doomed)   nil
          ;; this row is the one that leaves; the mirror is already the canonical spelling
          (= doomed self) (do (fold-row! kb self mirror witness) mirror)
          ;; the mirror leaves, and this row takes the canonical spelling it vacated
          :else           (do (fold-row! kb mirror self witness)
                              (:id (respell! kb (p/get-sentex (:records kb) self) want))))))))

(defn symmetrize-existing
  "When a `(symmetric P)` declaration arrives, bring `P`'s **already stored** facts into
  the argument order the declaration puts every later one in.  `{:new [handles]}` — the
  rows whose spelling moved, which are new content to every rule that reads the canonical
  one — or nil when `sentence` declares nothing symmetric.

  A declaration has to reach the facts already stored exactly as it reaches the facts that
  follow, which is `equate-existing`'s rule and holds here for a blunter reason: the door
  *sorts* a symmetric literal's arguments, so a declaration arriving second leaves the KB
  holding `(P b a)` where a KB told the same things in the other order holds `(P a b)` —
  and if both spellings were written, two rows for one proposition, each retractable
  without the other (vaelii#61).  Written the ordinary way — declaration first, then the
  facts — this finds an empty extent and costs one index cardinality read.

  **Shape: the storage migrates, rather than an alias recording that two rows mean one.**
  Both answer the issue; they differ in what a *restart* sees.  An alias is derived state,
  so it has to be rebuilt on every `recover` from records that still spell the fact two
  ways, and every reader — matching, retraction, the TMS, the handle doors — has to
  consult it for ever after.  Migrating instead leaves the records themselves canonical,
  so `recover` reads a store that needs no reconciling and no reader learns a new rule.
  The price is that it is a write and therefore not undone by retracting the mark: the
  declaration going away leaves `P`'s facts spelled the way the declaration had them
  spelled, which is a spelling and not a belief, and `sort-symmetric-args` never claimed
  the two orders were different propositions to begin with.

  **The extent is `P`'s own stored rows, not its spec subtree.**  `res/kb-sentex` reads
  the mark off the literal's exact functor — a `genl` edge below a symmetric predicate
  does not make the sub-predicate symmetric, and `constraint_descension_test` holds that
  line — so a row this arm re-spelled at a sub-predicate would be one the door stores the
  other way round on the very next assertion.

  **Stored, never believed.**  A mirrored pair whose rows are currently defeated merges
  exactly as a believed one does, for `equate-existing`'s reason: a spelling is not a
  claim, and reading belief here would leave the migration missing when the defeat lifts
  — belief depending on the order the defeat and the declaration arrived in.

  On a KB with a large extent under the newly marked predicate this costs one posting-list
  read plus a record fetch and a canonicalization per row, and a store probe per row that
  is out of order.  That is the same shape `equate-existing` pays and the same bound: it
  is a declaration reaching the facts, so it is linear in the facts it reaches, and a
  predicate marked before it has any is free."
  [kb sentence witness]
  (when (and (sequential? sentence) (= 'symmetric (nm/functor sentence))
             (= 1 (nm/arity sentence)))
    (let [p   (first (nm/args sentence))
          idx (:index kb)]
      (when (and (symbol? p) (not (sx/variable? p))
                 (tax/has-prop? (:taxonomy kb) :symmetric p)
                 (pos? (reads/stored-count-with-functor idx p)))
        ;; snapshotted before the first write: the fold posts to the roots this walk
        ;; reads, and no index backend promises whether a posting read is a snapshot
        {:new (into []
                    (keep (fn [h]
                            (when-let [sx (p/get-sentex (:records kb) h)]
                              (symmetrize-row! kb sx witness))))
                    (vec (reads/as-stored-with-functor idx p)))}))))

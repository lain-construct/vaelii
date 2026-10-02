;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.settle
  "Belief settling: the pass that relabels the TMS and runs the `exceptWhen` re-check
  queue to a joint fixpoint with belief (`pass-work`, `block-work`, `apply-pass!`), the
  seed readers a pass gathers, `settle-finish` and `settle`.  A pass calls
  `vaelii.impl.discovery`, `readings`, `recheck` and `reroute`; what a reader reads of the
  clashes is `vaelii.impl.clashes`.  The top engine layer, below `vaelii.core`.  See
  docs/nmtms.md."
  (:require [clojure.set :as set]
            [taoensso.trove :as trove]
            [vaelii.impl.chain :as chain]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.decide :as decide]
            [vaelii.impl.decide.inherited :as inherited]
            [vaelii.impl.discovery :as discovery]
            [vaelii.impl.feed :as feed]
            [vaelii.impl.integrate :as integrate]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.predicates :as pr]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.readings :as readings]
            [vaelii.impl.recheck :as recheck]
            [vaelii.impl.reroute :as reroute]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.settle-phases :as phases]
            [vaelii.impl.special :as special]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.impl.violations :as violations]))

;; ---- the facet contract -------------------------------------------------
;; `predicates/check-facets` runs at this namespace's load (docs/predicates.md says why).

(def facet-check-inputs
  "The cross-layer facts `predicates/check-facets` cannot read for itself.  A var so
  that this call site and `predicates_test` check the same arguments.

  * `:recheck-subjects` — the functors posting exception re-checks through the shared
    path (`special/declaration-subjects`) rather than from an arm of their own.
  * `:family-rosters` — `family -> {roster-name functors}`, every roster that reads a
    mark family as a family (`predicates_test/a-roster-that-enumerates-a-family-is-named-here`)."
  {:recheck-subjects special/recheck-subjects
   :family-rosters   {:argument-constraint
                      {'checks/constraint-declaration-functors
                       checks/constraint-declaration-functors
                       'provers/meta-constraint-functors
                       provers/meta-constraint-functors}}})

(def checked-entries
  "`predicates/entries`, having passed the facet contract at this namespace's load, which
  throws on a violation.  A var rather than a bare call so `predicates_test` can prove
  the check runs here on the live inputs."
  (pr/check-facets pr/entries facet-check-inputs))

;; ---- the exception fixpoint ---------------------------------------------
;; Belief and blocking depend on each other, so `settle` iterates: relabel, re-evaluate
;; the exceptions the triggers queued, relabel again if the blocked set moved.

(def ^:private max-settle-passes
  "Bound on the exception fixpoint's passes.  Termination rests on the stratification
  checks at assert time; a run that reaches this bound logs `::exception-fixpoint`
  instead of looping (docs/exceptions.md)."
  16)

(defn- drain-recheck!
  "Take the queued `{rule-handle -> triggers}` map and clear the queue in one CAS, so a
  re-check is done once and a `swap!` landing during the take is kept for the next pass."
  [kb]
  (let [a (reasoning/recheck kb)]
    (loop []
      (let [old @a]
        (if (compare-and-set! a old {})
          old
          (recur))))))

(def ^:dynamic *touched-sink*
  "An atom holding a set, or nil.  When bound, every settle adds the handles of its
  relabelled region before clearing them.  `core/preview` and
  `core/edit-with-consequences!` bind it (docs/preview.md)."
  nil)

(def ^:dynamic *touched-in-sink*
  "An atom holding a set, or nil: the companion of `*touched-sink*`, collecting which
  handles of that region were believed before the settle (`jtms/touched-in`).
  `core/edit-with-consequences!` binds both."
  nil)

(def ^:dynamic *sweep?*
  "Does a settle delete what a newly-blocked justification solely supported?  False only
  inside `core/preview`, which must hand the KB back at the same handles
  (docs/preview.md)."
  true)

(def ^:dynamic *relabelled-before?*
  "True when labels flipped before the settle by a path that is neither a defeat, a
  block nor a write: `core/preview`'s `jtms/suspend-premise` and its rollback's
  `add-premise`.  It opens the `belief-moved?` gate (docs/nmtms.md, \"What
  `settle-finish` reconciles\").  A flag the caller binds, rather than a gate that tests
  the region for a taxonomy sentex, because that test would cost a record read per region
  member on every settle for a path only `preview` takes."
  false)

(def ^:dynamic *rebuilding?*
  "True while `recover`'s settles restore a KB rather than react to a change.  The passes
  that report or re-derive what a change moved read it and stand aside, among them the
  cut notices, the revival and un-merge re-seeds, the refusal re-asks
  and the second-route re-derivations.  A rebuild relabels the whole graph, so its region
  is every stored sentex, and the replayed justifications already carry every
  derivation.  The definitional nogood sweep does not read it (docs/taxonomy.md, \"What a
  declaration reaches back over\")."
  false)

(def ^:dynamic ^:private *unmerged-sink*
  "A volatile collecting the spellings an un-merge gave back, and each equality supporter
  believed again with its twins, or nil.  `settle` binds it, `settle-finish` fills it
  from the supersession moves since the last settle (`special/take-supersession-moves!`)
  and from `special/believed-again-sweeps`, and `settle` re-seeds
  what it holds and settles again (docs/nmtms.md, \"The other half: a spelling an
  un-merge gives back\")."
  nil)

(defn- apply-removals!
  "Delete from the stores what a network removal swept, and tear each deleted record down
  (`integrate/sentex-removed!`, which queues its re-check)."
  [kb {:keys [removed-sentexes removed-justifications]}]
  ;; fetch before tearing down: the JTMS hands back handles, and `sentex-removed!` is
  ;; what deletes the record
  (doseq [d removed-sentexes
          :let [sx (p/get-sentex (:records kb) d)]
          :when sx]
    (integrate/sentex-removed! kb sx))
  (doseq [jid removed-justifications] (p/delete-justification! (:records kb) jid)))

(defn- sweep-excepted!
  "Delete what the newly-blocked justifications were solely supporting, through the JTMS
  sweep (`apply-removals!`).  Deletes nothing while `*sweep?*` is false."
  [kb newly-blocked]
  (let [tms   (reasoning/tms kb)
        seeds (when *sweep?*
                (into #{} (keep #(:consequence (jtms/justification tms %))) newly-blocked))]
    (when (seq seeds)
      (apply-removals! kb (jtms/sweep! tms seeds)))))

(defn- released-rules
  "The informants of the justifications in `was` and not in `new`: the rules whose
  exception this pass lifted.  Called before the sweep, while those justifications are
  still in the TMS."
  [kb was new]
  (let [tms (reasoning/tms kb)]
    (into #{}
          (keep (fn [jid]
                  (let [inf (:informant (jtms/justification tms jid))]
                    (when (integer? inf) inf))))
          (remove new was))))

(defn- region-terms
  "Every symbol standing as an argument of a sentex in `region` — the terms whose
  memberships this settle can have moved."
  [kb region]
  (into #{}
        (comp (keep #(p/get-sentex (:records kb) %))
              (mapcat #(nm/args (:sentence %)))
              (filter symbol?))
        region))

(defn- released-constraint-refusals
  "The `:constraint` refusals the argument constraint no longer convicts, as `[[rule-handle
  entry] …]` for `chain/release-refusal!`.  An entry is re-asked only when a `genl` or
  `genlCx` generation moved since it was stamped or `region` holds a sentex naming its
  convicted term; one still convicted is restamped
  (`chain/redecide-constraint-refusal!`).  Empty during a rebuild, since `recover`
  re-records the refusals by re-firing (`chain/rerecord-refusals!`)."
  [kb region]
  (let [entries (when-not *rebuilding?* (chain/constraint-refusals kb))]
    (if (empty? entries)
      []
      (let [gens  (chain/constraint-generations kb)
            terms (delay (region-terms kb @region))]
        (reduce (fn [acc [rh e]]
                  (if (and (or (not= gens (:gens e)) (contains? @terms (:term e)))
                           (= :free (chain/redecide-constraint-refusal! kb rh e gens)))
                    (conj acc [rh e])
                    acc))
                []
                entries)))))

(defn- released-lifts
  "The decontextualized copies an argument conviction refused that the content this
  settle stored no longer convicts, as new handles to chain from
  (`special/release-lift!`) — re-asked on `released-constraint-refusals`' two triggers,
  since the conviction is the same one."
  [kb region]
  (let [pending (when-not *rebuilding?* (special/lift-refusals kb))]
    (if (empty? pending)
      []
      (let [gens  (chain/constraint-generations kb)
            terms (delay (region-terms kb @region))]
        (into []
              (mapcat (fn [[h e]]
                        (when (or (not= gens (:gens e)) (contains? @terms (:term e)))
                          (:new (special/release-lift! kb h e gens)))))
              pending)))))

(defn- minted-mintable
  "The types the minted `genl` edge `sentence` makes mintable, where `mintable?` answers
  for the hierarchy before the edge: the lower end and its subtypes when the upper end
  is mintable, the lower end is not, and `checks/mintable-type?` reads the lower end as
  mintable now (a mint off a disbelieved fact is not in the hierarchy).  Empty for any
  other sentence."
  [tax mintable? sentence]
  (let [[f sub super] sentence]
    (if (and (= 'genl f) (mintable? super) (not (mintable? sub))
             (checks/mintable-type? tax sub))
      (tax/specs-of-all tax [sub])
      #{})))

(defn- released-mints
  "The types minted by declarations whose type has become mintable since they were
  swept, as new handles to chain from (`special/release-mint!`).  Re-asked only when a
  `genl` or `genlCx` generation has moved since the entry was stamped, since nothing else
  changes what `mintable-type?` answers, and answered from one walk down from `thing`
  taken before the first release (`checks/mintable-types`).  A `genlArg` release mints a
  `genl` edge that walk does not hold: the types the edge makes mintable join the
  answer (`minted-mintable`), and the entries already restamped waiting on one of them
  are released again in the same pass.  Not during a rebuild, for
  `released-constraint-refusals`' reason."
  [kb]
  (let [gens    (chain/constraint-generations kb)
        pending (when-not *rebuilding?* (special/mint-refusals kb gens))]
    (if (empty? pending)
      []
      (let [tax       (reasoning/taxonomy kb)
            walked    (checks/mintable-types tax)
            added     (volatile! #{})
            mintable? #(or (walked %) (contains? @added %))]
        (special/minted-seeds
         kb
         ;; `waiting` holds the restamped entries by the type each waits on
         (loop [todo    (into clojure.lang.PersistentQueue/EMPTY (map first) pending)
                waiting {}
                minted  []]
           (if-let [dh (peek todo)]
             (let [{new :new waits :waits} (special/release-mint! kb dh gens mintable?)
                   grown (reduce (fn [acc h]
                                   (let [g (some->> (p/get-sentex (:records kb) h) :sentence
                                                    (minted-mintable tax mintable?))]
                                     (vswap! added into g)
                                     (into acc g)))
                                 #{} new)
                   waiting (reduce #(update %1 %2 (fnil conj #{}) dh) waiting waits)]
               (recur (into (pop todo) (comp (mapcat waiting) (distinct)) grown)
                      (reduce dissoc waiting grown)
                      (into minted new)))
             minted)))))))

(defn- revived-mark-seeds
  "The merges and lifts a mark, or a `genl` edge under one, in `revived` owes the facts
  stored while it was OUT, as new handles to chain from
  (`special/revived-declaration-sweeps`).  Reconciles the retired spellings and reports
  the violations, as `assert-one` does for the same sweeps on an arrival.  `revived` is
  `revived-seeds`' answer, so a rebuild asks nothing.  The taxonomy is reconciled over
  `revived` first: a datum a relabel inside this settle revived, such as a `genl` edge
  whose void firing a roster declaration released, is in no cache until `settle-finish`,
  and the sweeps read the marks and edges the caches hold."
  [kb revived]
  (when (seq revived)
    (special/reconcile-belief-change kb revived)
    (tax/restore-depths (reasoning/taxonomy kb)))
  (if-let [mig (special/revived-declaration-sweeps kb revived)]
    (do (when (seq (:superseded mig))
          (special/refresh-supersessions kb (:superseded mig)))
        (violations/report kb (:violations mig))
        (:new mig))
    []))

(defn- class-moved-merge-seeds
  "The merges and un-merges a collision member's class moving owes
  (`special/class-moved-merges` over `region`, the pass's `touched` as a delay), as handles
  to chain from: the new twins and the members of each dropped merge.  Applies the
  removals, reconciles the retired spellings and reports the violations, as
  `revived-mark-seeds` does.  `asked` is the settle's record of what it asked.  A merge
  that moves the equality edges moves `decide/stamp`, so every reader decides again.
  Empty during a rebuild, whose replayed justifications carry every merge."
  [kb region asked]
  (if-let [mig (when-not *rebuilding?* (special/class-moved-merges kb region asked *sweep?*))]
    (let [seeds (into (:new mig) (:members mig))]
      (some->> (:removed mig) (apply-removals! kb))
      (when (seq (:superseded mig))
        (special/refresh-supersessions kb (:superseded mig)))
      (violations/report kb (:violations mig))
      seeds)
    []))

(defn- except-move-seeds
  "The twins owed to the facts an `except` moved an equality's or a merge mark's
  visibility over, as new handles to chain from (`special/drain-except-moves!`).  The
  supersessions the sweep found wait on `:except-moves` for `settle-finish`; the
  violations are reported here.  A rebuild clears the queue, since it reconciles every
  supersession from the stored twins."
  [kb]
  (if *rebuilding?*
    (do (special/clear-except-moves! kb) [])
    (if-let [mig (special/drain-except-moves! kb)]
      (do (violations/report kb (:violations mig))
          (:new mig))
      [])))

(defn- released-subsumed
  "The mints a record leaving belief or the store no longer lets the KB withhold, as new
  handles to chain from (`special/withheld-releases`).  `withdrawn` is the mints this
  settle withdrew, whose own departure releases nothing.  Empty during a rebuild, which
  drops the queued departures: a restore changes nothing.  `was-in` and `believed?` are
  belief before the settle and now (`pass-belief`)."
  [kb moved was-in believed? asked withdrawn]
  (if *rebuilding?*
    (do (special/drain-departures! kb) [])
    (:new (special/withheld-releases kb moved was-in asked withdrawn believed?))))

(defn- subsumed-blocks
  "The mint justifications this settle withdraws, and the records they held up:
  `special/subsumed-mint-blocks` over `moved`, the delay of the region's sentexes
  `released-subsumed` reads too."
  [kb moved was-in believed? asked]
  (or (special/subsumed-mint-blocks kb moved was-in asked believed?)
      {:blocked #{} :withdrawn #{}}))

(defn- pass-belief
  "`[was-in believed?]` for a pass: the relabelled handles believed before the settle
  (`jtms/touched-in`) with the own-context moves `own` (`special/reconcile-own-withdrawals!`)
  folded in, and belief now as a handle's own context reads it."
  [kb own]
  (let [tms (reasoning/tms kb)
        out (readings/own-out kb)]
    [(as-> (jtms/touched-in tms) w
       (into w (:gone own))
       (reduce disj w (:back own)))
     (if out #(and (jtms/in? tms %) (not (contains? out %))) #(jtms/in? tms %))]))

(defn- revived-seeds
  "The datums `jtms/revived` finds in `region` (the pass's `touched`, as a delay), minus
  `done`, the ones an earlier pass of this settle already re-seeded.  Nil during a
  rebuild (docs/nmtms.md, \"A revived datum is a datum the agenda has not seen\")."
  [kb done region]
  (when-not *rebuilding?*
    (into [] (remove done) (jtms/revived (reasoning/tms kb) @region))))

(defn- departed-handles
  "The handles in `region` (the pass's `touched`, as a delay) that went IN ⇒ OUT this
  settle, by a relabel: the window `departed-seeds` and `defeated-derivation-seeds` both
  read, beside the handles a verdict withdrew at their own context.  Empty during a
  rebuild."
  [kb region]
  (if *rebuilding?*
    []
    (let [tms (reasoning/tms kb)
          was (jtms/touched-in tms)]
      (into [] (filter #(and (contains? was %) (not (jtms/in? tms %)))) @region))))

(defn- departed-seeds
  "The facts owed a re-join because a `genl` or `genlCx` edge in `out` (`departed-handles`)
  went IN ⇒ OUT or was withdrawn at its own context, minus `done`
  (`special/departed-edge-seeds`).  A verdict sweeps nothing, so this is the re-join a
  retraction gets from `special/resubsumption-seeds`
  (docs/nmtms.md, \"Where the layer stops\")."
  [kb done out]
  (when (seq out)
    (into [] (remove done) (special/departed-edge-seeds kb out))))

(defn- lost-derivation-seeds
  "Draw `justs` (`special/lost-descended-derivations`) again over a route that survives,
  and return the handles that created and each conclusion the new justification brought
  back IN, as seeds.  The second is what makes the pass that drew it productive, so the
  next pass reads the region the new support moved."
  [kb justs]
  (if (seq justs)
    (let [tms (reasoning/tms kb)]
      (into (special/rederive-descended kb justs)
            (comp (map :consequence) (distinct) (filter #(jtms/in? tms %)))
            justs))
    []))

(defn- defeated-derivation-seeds
  "The argument-type entailments and descended equalities a `genl` edge took OUT or
  withdrew at their own context when this settle withdrew it, drawn again over a route
  that survives — `departed-seeds`' twin for the derivations that name the edge rather
  than for the firings.  An equality whose facts a withdrawn merge still supersedes is
  drawn by `settle`'s un-merge round instead, once the spellings are back.

  `out` is `departed-handles`' answer for the pass."
  [kb out]
  (if (seq out)
    (lost-derivation-seeds kb (special/lost-descended-derivations kb out true))
    []))

(defn- blanket-recheck-rules
  "The queued rules with no triggering sentence (`:all` or `:all-rejoin`: a taxonomy edge
  moved, or the rule was just indexed) or with a withdrawal marker.  They take the coarse
  re-chain, since nothing says whether the move blocked or released."
  [queued]
  (keep (fn [[rh triggers]]
          (when (or (#{:all :all-rejoin} triggers)
                    (some recheck/withdrawal-marker? triggers))
            rh))
        queued))

(defn- forced-recheck-rules
  "The unconditional rechecks that also owe a fresh join when blocking stayed still."
  [queued]
  (keep (fn [[rh triggers]] (when (= :all-rejoin triggers) rh)) queued))

(defn- rejoin-on-arrival-rules
  "The queued rules an arriving fact can release rather than only block
  (`rules/arrival-releasable?`: an aggregate or a nested NAF), which are re-joined
  whatever the blocked set did (docs/exceptions.md, \"Re-chaining what was released, not
  what was touched\").  One record fetch per queued rule."
  [kb queued]
  (keep (fn [[rh _]]
          (when-let [rsx (p/get-sentex (:records kb) rh)]
            (when (and (rules/rule? rsx) (rules/arrival-releasable? rsx)) rh)))
        queued))

(defn rechain-exception-rules
  "Re-chain the stored, believed forward rules among `rule-handles` over their whole
  extent, to re-derive what a released exception suppressed.  A firing whose conclusion
  stands or whose exception still holds places nothing.  Each rule costs one join over its
  extent, so callers pass the released rules rather than the queued ones
  (docs/exceptions.md).  Uses `chain`, not `chain-all`: the violations ledger is scoped to
  the caller's run."
  [kb rule-handles]
  (let [live (filter (fn [rh]
                       (let [rsx (p/get-sentex (:records kb) rh)]
                         (and rsx (rules/rule? rsx) (rules/forward-sentex? rsx)
                              (jtms/in? (reasoning/tms kb) rh))))
                     rule-handles)]
    (when (seq live) (chain/chain kb live nil))))

(defn rechain-seeds
  "Re-chain from `seeds`, the datum handles something put back on the agenda, filtered to
  what is still stored and believed.  One join per rule keyed by each datum's predicate,
  as an assert pays (docs/nmtms.md, \"A revived datum is a datum the agenda has not
  seen\").  Uses `chain`, not `chain-all`, as `rechain-exception-rules` does."
  [kb seeds]
  (let [live (filter (fn [h] (and (p/get-sentex (:records kb) h) (jtms/in? (reasoning/tms kb) h)))
                     seeds)]
    (when (seq live) (chain/chain kb live nil))))

(def ^:private max-own-rounds
  "How many times `settle-finish` reconciles the unscoped caches with own-context belief
  before it reads the reports and the window.  A cache a verdict moved can move a verdict
  only through a nogood read over the moved supporter itself."
  4)

(defn- settle-finish
  "Reconcile the derived caches with settled belief, publish the moved region to the
  sinks and the feed, and clear the touched window.  `belief-moved?` gates the first
  `refresh-beliefs` reconcile.  The order and each gate: docs/nmtms.md, \"What
  `settle-finish` reconciles\"."
  [kb region win passes moved belief-moved?]
  ;; the depth repair a `with-deferred-settle` batch owes; free when nothing deferred
  (tax/restore-depths (reasoning/taxonomy kb))
  (let [extra    (volatile! #{})     ; region members no relabel recorded
        extra-in (volatile! #{})     ; ...of which these were believed until this settle
        opened   (volatile! {})]     ; the superseded map when the window opened
    ;; forces the region only on a timing run (`settle_region_cost_test` counts reads)
    (when (phases/profiling?) (phases/note-region! (count @region)))
    (when belief-moved?
      (special/reconcile-belief-change kb @region)
      ;; the reconcile can open or close a cycle (docs/taxonomy.md)
      (tax/restore-depths (reasoning/taxonomy kb)))
    ;; an equality supporter a reconcile found believed again restates its class, as its
    ;; arrival does; `settle` re-seeds the supporter and its twins
    (when-let [hs (tax/take-believed-again! (reasoning/taxonomy kb))]
      (when-not *rebuilding?*
        (let [mig (special/believed-again-sweeps kb hs)]
          (when (seq (:superseded mig))
            (special/refresh-supersessions kb (:superseded mig)))
          (violations/report kb (:violations mig))
          (vswap! extra into (:new mig))
          (some-> *unmerged-sink* (vswap! into (concat hs (:new mig)))))))
    ;; the write path reconciles every supersession a stored or removed sentence moves;
    ;; the settle owes it only for an `except` that moved (`special/take-except-moves!`)
    ;; and an equality edge that moved in belief
    (let [ex (special/take-except-moves! kb)]
      (when (or ex (tax/equality-moves? (reasoning/taxonomy kb) :supersessions))
        (special/refresh-supersessions kb (:extra ex) (when-not (:full? ex) (set (:region ex))))))
    ;; `moved` is every datum whose supersession entry changed since the last settle
    ;; finished, and `was` its entry before the first change, so `before` and `after` are
    ;; the superseded maps of the last settle and this one
    (let [after  (jtms/superseded (reasoning/tms kb))
          {:keys [moved was]} (or (special/take-supersession-moves! kb) {:moved #{} :was {}})
          before (vreset! opened (reduce (fn [m d] (if-let [e (get was d)] (assoc m d e) (dissoc m d)))
                                         after moved))]
      (vswap! extra into moved)
      ;; a datum superseded since the last settle was believed until now, and no relabel
      ;; says so, unless this window stored it
      (let [born (jtms/touched-new (reasoning/tms kb))]
        (vswap! extra-in into (filter #(and (contains? after %) (not (contains? before %))
                                            (not (contains? born %))))
                moved))
      ;; a merge supersedes a declaration with no label moving, after the reconcile above
      (when (seq moved)
        (special/reconcile-belief-change kb (into @region moved)))
      ;; the spellings an un-merge gave back, for `settle` to re-seed
      (when-let [sink (and (not *rebuilding?*) *unmerged-sink*)]
        (vswap! sink into
                (filter #(and (contains? before %) (not (contains? after %))
                              (jtms/in? (reasoning/tms kb) %)))
                moved)))
    ;; the readers' readings, recorded on every settle since the next one diffs against
    ;; them, each read after `res/reconcile-withdrawn!` so it reads no dropped entry; a
    ;; handle a verdict withdrew at its own context, or gave back, leaves or rejoins the
    ;; unscoped caches with no label moving, and the caches it moves can move a verdict,
    ;; so to a fixpoint, bounded
    (loop [n 0]
      (res/reconcile-withdrawn! kb)
      (when (and (< n max-own-rounds)
                 (readings/reconcile-own! kb win region *rebuilding?*))
        (tax/restore-depths (reasoning/taxonomy kb))
        (recur (inc n))))
    ;; the last read of the touched window before the reset
    (res/reconcile-withdrawn! kb)
    ;; the window is built only when a sink is bound or a listener registered
    (let [sink    *touched-sink*
          in-sink *touched-in-sink*
          fed?    (and (not *rebuilding?*) (feed/wants-region? kb))
          decided {:moved @(:moved win) :withdrawn-before @(:before win)}]
      (when (or sink in-sink fed?)
        (let [tms    (reasoning/tms kb)
              moved  (-> @extra (into @region) (into (:moved decided)))
              ;; a spelling superseded when the window opened was not believed, whatever
              ;; its label: `touched-in` records the label, and a handle outside the
              ;; region keeps its label from before
              open?  #(not (contains? @opened %))
              was-in (-> @extra-in
                         (into (filter open?) (jtms/touched-in tms))
                         (into (filter #(and (not (contains? @region %)) (jtms/defeat-class tms %)
                                             (open? %)))
                               (:moved decided))
                         (set/difference (:withdrawn-before decided)))]
          (when sink    (swap! sink into moved))
          (when in-sink (swap! in-sink into was-in))
          (when fed?    (feed/note-region! kb moved was-in)))))
    (jtms/reset-touched! (reasoning/tms kb))
    (swap! (reasoning/settle-stats kb)
           (fn [s] (-> s
                       (assoc :iterations moved :passes passes)
                       (update-in [:histogram moved] (fnil inc 0))))))
  ;; the pass count says whether the KB's exceptions have started to interact
  (trove/log! {:level :debug :id ::settled
               :data {:passes     passes
                      :iterations moved
                      :moved?     belief-moved?}})
  nil)

(defn- finish-settle
  "Close one settle: note the pass count for `settle-phases`, run `settle-finish` inside
  the `:finish` span, and file this settle's record.  Every `settle*` return runs
  through here."
  [kb win passes moved belief-moved?]
  (phases/note-passes! passes)
  ;; one materialized region for the finish's reads
  (let [region (delay (jtms/touched (reasoning/tms kb)))
        _      (res/reconcile-withdrawn! kb)
        r      (phases/with-phase :finish
                 (settle-finish kb region win passes moved belief-moved?))]
    (phases/end-settle!)
    r))

;; ---- one pass -------------------------------------------------------------------
;; A pass reads what it owes (`pass-work`), what the queued exceptions block
;; (`block-work`), and applies both (`apply-pass!`).  It has converged when it queues,
;; blocks and owes nothing.

(def ^:private owed
  "The keys of `pass-work` a pass applies whatever the blocked set does: the rules a
  verdict released, the datums whose belief came back, the facts a departed edge owes a
  re-join, each reader's lost firings, the refusals a constraint no longer convicts, and
  the mints, lifts and merges owed."
  [:flips :revived :departed :lost :cfree :mnew])

(defn- owes-nothing?
  "Is every key of `ks` empty in the pass work `w`?"
  [w ks]
  (every? #(empty? (get w %)) ks))

(defn- pass-work
  "One pass's reads, before anything is blocked or re-chained, as a map: the inherited
  clashes found again first, since the discovery reads no verdict; the readers' moves;
  the drained re-check queue (`:queued`); every key of `owed`; and the mints this pass
  withdraws (`:wdrawn`, `subsumed-blocks`).  `:region` is the relabelled window, read
  again when a merge this pass owed moved it.  The second argument is the settle's
  state: `:region`, `:reseeded` and `:relost` (what earlier passes seeded), the readers'
  window `:win`, and the volatiles of `:asked`."
  [kb {:keys [region reseeded relost win asked]}]
  (discovery/clear-inherited! kb)
  (res/reconcile-withdrawn! kb)
  ;; the merges a collision member's class moving owes, before the discovery reads the
  ;; pairs they reconcile
  (let [remerge (class-moved-merge-seeds kb region (:merge asked))
        region  (if (seq remerge) (delay (jtms/touched (reasoning/tms kb))) region)
        _       (phases/with-phase :discovery (discovery/discover-inherited! kb region))
        ;; the handles a reader's verdict withdrew at their own context, or gave back,
        ;; which leave or rejoin the unscoped caches with no label moving
        own     (when-not *rebuilding?* (readings/reconcile-own! kb win region false))
        ;; the rules a verdict released, whose swept firing no instrument below can find;
        ;; read before the drain, since it posts their triggers
        flips   (readings/released! kb win region own)
        queued  (drain-recheck! kb)
        ;; the datums whose belief came back; `reseeded` seeds each once per settle,
        ;; since the window spans the settle
        revived (into (vec (revived-seeds kb reseeded region)) (remove reseeded) (:back own))
        ;; the facts under an edge a firing named that this settle defeated, whose second
        ;; route nothing else re-joins (`departed-seeds`)
        out      (into (departed-handles kb region) (:gone own))
        departed (departed-seeds kb reseeded out)
        ;; the firings a reader below a scoped defeat or an `except` reads as withdrawn
        ;; while it still reaches over a second route (`reroute/lost-firing-seeds`)
        lost    (when-not *rebuilding?* (reroute/lost-firing-seeds kb relost region))
        ;; the firings an argument constraint dropped that the content this settle stored
        ;; no longer convicts (`released-constraint-refusals`)
        cfree   (released-constraint-refusals kb region)
        ;; the types a declaration could not mint until its type reached `thing`, the
        ;; merges and lifts a revived mark owes the facts that arrived while it was OUT,
        ;; the twins an `except` that began or stopped hiding an equality or a merge mark
        ;; owes, and the entailments and equalities a defeated genl edge took OUT while a
        ;; second route still licenses them
        mnew    (-> (released-mints kb)
                    (into (released-lifts kb region))
                    (into (revived-mark-seeds kb revived))
                    (into (except-move-seeds kb))
                    (into (defeated-derivation-seeds kb out))
                    (into remerge))
        ;; the relabelled records and the own-context moves, read once for both halves of
        ;; the subsumption question
        rsx     (delay (into [] (keep #(p/get-sentex (:records kb) %))
                             (-> (set @region) (into (:back own)) (into (:gone own)))))
        [was-in believed?] (pass-belief kb own)
        mnew    (into mnew (released-subsumed kb rsx was-in believed? (:release asked)
                                              @(:withdrawn asked)))
        ;; the other direction of the subsumption question: the mints a membership
        ;; arriving this settle has made redundant, whose justifications this pass blocks
        ;; so the sweep collects the records
        wdrawn  (subsumed-blocks kb rsx was-in believed? (:subsumption asked))]
    {:region region :queued queued :flips flips :revived revived :departed departed
     :lost lost :cfree cfree :mnew mnew :wdrawn wdrawn}))

(defn- block-work
  "`w` with what its queued exceptions block: the blocked set as it is (`:was`) and as the
  queue and the withdrawn mints leave it (`:new`), the visibility transitions that owe the
  blanket re-join whether or not anything blocked (`:forced`), the rules an arrival can
  release (`:aggs`), and the refusals the queue released (`:free`, and `:over` for an
  overflowed rule)."
  [kb {:keys [queued wdrawn] :as w}]
  (let [was  (jtms/blocked (reasoning/tms kb))
        new  (into (recheck/exception-blocked-set kb queued) (:blocked wdrawn))
        aggs (rejoin-on-arrival-rules kb queued)
        {free :free over :overflow} (recheck/released-refusals kb queued)]
    (assoc w :was was :new new :forced (vec (forced-recheck-rules queued))
           :aggs aggs :free free :over over)))

(defn- apply-pass!
  "Block what `w` blocks, sweep what that excepts, and re-chain what the pass owes: the
  released refusals, the revived datums and the mints on one agenda; the departed facts
  and each reader's lost firings silently, as the retraction path's re-join is; and the
  rules the pass released.  `asked` takes the mints withdrawn."
  [kb {:keys [was new wdrawn queued free cfree revived mnew departed lost aggs over flips]}
   asked]
  ;; read before the sweep, which deletes justifications
  (let [released (released-rules kb was new)]
    (vswap! (:withdrawn asked) into (:withdrawn wdrawn))
    (jtms/set-blocked (reasoning/tms kb) new)
    (sweep-excepted! kb (into #{} (remove was) new))
    ;; the rules the sweep queued; what the re-chains below queue the next pass drains
    ;; and re-decides narrowly
    (let [swept (keys @(reasoning/recheck kb))
          seeds (-> (into [] (mapcat (fn [[rh e]] (chain/release-refusal! kb rh e)))
                          (concat free cfree))
                    (into revived)
                    (into mnew))]
      (when (seq seeds) (rechain-seeds kb seeds))
      ;; the re-join a defeated witness owes, silent where it places nothing
      ;; (`chain/*report-no-placement?*`)
      (when (seq departed)
        (binding [chain/*report-no-placement?* false] (rechain-seeds kb departed)))
      ;; each reader's lost firings, with every witness search asked from that reader
      (doseq [[r pairs] lost]
        (binding [chain/*witness-view*         r
                  chain/*report-no-placement?* false]
          (rechain-seeds kb (into [] (comp (mapcat second) (distinct)) pairs))))
      ;; only the rules this pass released, never every rule it touched: a rule seed
      ;; joins over the whole extent
      (rechain-exception-rules kb (into released (concat (blanket-recheck-rules queued)
                                                         aggs over flips swept))))))

(defn- settle*
  "Relabel, find the inherited clashes, and re-evaluate the `exceptWhen` exceptions the
  triggers queued, to a joint fixpoint of at most `max-settle-passes` passes.  A pass
  that leaves the blocked set as it was (`set-blocked` replaces) and queues, revives and
  releases nothing ends the loop; every other pass counts in `settle-stats`'
  `:iterations`."
  [kb]
  ;; one `settle-phases` record per settle, filed by `finish-settle` at each return
  (phases/begin-settle!)
  ;; belief moves by a block change, a caller's relabel before the settle or a reader's
  ;; verdict, and `moved?` is the `belief-moved?` gate over them
  (let [inherited?        #(boolean (seq (inherited/inherited-clashes kb)))
        inherited-before? (inherited?)
        ;; read before the settle clears them, so a verdict that moves releases its rules
        losers-before    (if inherited-before? (discovery/inherited-losers kb) #{})
        ;; ...and a handle withdrawn at its own context, which the caches leave out
        own?   (fn [] (boolean (seq (::special/own-out @(reasoning/taxonomy kb)))))
        own-before? (own?)
        moved? (fn [moved] (or inherited-before? own-before? *relabelled-before?*
                               (inherited?)
                               (own?)
                               (pos? moved)))]
    (phases/with-phase :belief
      (discovery/clear-inherited! kb)
      (res/reconcile-withdrawn! kb))
    ;; reconcile the caches with what a caller relabelled before discovery reads them: a
    ;; revived `genl` or `genlCx` edge can make a pair jointly visible.  The region is
    ;; read once per pass into a delay (docs/nmtms.md, "The runtime view").
    (let [region (delay (jtms/touched (reasoning/tms kb)))
          _      (phases/with-phase :belief
                   (when *relabelled-before?*
                     (special/reconcile-belief-change kb @region)
                     (tax/restore-depths (reasoning/taxonomy kb))))
          ;; the records asked the subsumption question this settle, in each direction
          ;; (`subsumed-blocks`, `released-subsumed`), the merges asked, and the mints it
          ;; withdrew
          asked  {:subsumption (volatile! #{}) :release (volatile! #{})
                  :merge (volatile! #{}) :withdrawn (volatile! #{})}
          ;; the readers' own-context moves, across the passes and the finish
          win    (readings/reader-window losers-before)]
      (loop [pass 1, moved 0, reseeded #{}, relost #{}, region region]
        (let [w (pass-work kb {:region region :reseeded reseeded :relost relost
                               :win win :asked asked})]
          (if (and (empty? (:queued w)) (empty? (:blocked (:wdrawn w))) (owes-nothing? w owed))
            (finish-settle kb win pass moved (moved? moved))
            (let [w (block-work kb w)]
              (if (and (= (:new w) (:was w))
                       (owes-nothing? w (into owed [:forced :aggs :free :over])))
                (finish-settle kb win pass moved (moved? moved))   ; unproductive pass: converged
                (do (apply-pass! kb w asked)
                    (if (< pass max-settle-passes)
                      (recur (inc pass) (inc moved)
                             (-> reseeded (into (:revived w)) (into (:departed w)))
                             (into relost (for [[r pairs] (:lost w), [h _] pairs] [r h]))
                             (delay (jtms/touched (reasoning/tms kb))))
                      (do (trove/log! {:level :warn :id ::exception-fixpoint
                                       :msg  (str "exception re-check did not converge in "
                                                  max-settle-passes " passes; giving up")
                                       :data {:passes pass :blocked (count (:new w))}})
                          (finish-settle kb win pass (inc moved) (moved? (inc moved))))))))))))))

(def ^:private max-unmerge-rounds
  "How many times `settle` re-seeds an un-merge and settles again before it logs
  `::unmerge-fixpoint` and stops (docs/nmtms.md, \"The other half: a spelling an un-merge
  gives back\")."
  8)

(defn- respelled-seeds
  "Drain the `:respell` queue, the predicates whose permuting marks moved in the settle
  just run, through `chain/reconcile-spellings!`, and return the handles it made.  A
  rebuild clears the queue and respells nothing, since a recovered store was spelled
  when written.  With `*sweep?*` off the queue is kept, so `core/preview`'s rollback
  settle drains it against the restored KB and the handles stay the same."
  [kb]
  (let [q (reasoning/respell kb)]
    (when (seq @q)
      (cond
        *rebuilding?*    (do (reset! q #{}) nil)
        (not *sweep?*)   nil
        :else            (let [preds @q]
                           (reset! q #{})
                           (chain/reconcile-spellings! kb preds))))))

(defn- hold-belief!
  "Hold the belief `kb` holds now for every other thread until `publish-belief!`, and
  return the hold, or nil when nothing is held: on a rebuild, and when a hold is open on
  the network already.  The network (`jtms/hold!`) and the candidate index, whose
  inherited clashes the settle re-finds (`observe/hold-atom!`), are held before
  `observe/open-hold!` registers the hold, so a reader switches to both at once (docs/nmtms.md, \"Two representations of the same
  network\")."
  [kb]
  (when-not *rebuilding?*
    (let [tms (reasoning/tms kb)
          sd  (reasoning/nogood-candidates kb)
          h   (observe/new-hold)]
      (when (jtms/hold! tms h)
        (observe/hold-atom! sd h)
        (observe/open-hold! h)
        [tms h sd]))))

(defn- publish-belief!
  "Publish what the settle decided under `held` (`hold-belief!`'s answer): close the hold,
  so every reader reads the belief the settle reached in one step, then drop what the
  network and the candidate index kept for it."
  [held]
  (when-let [[tms h sd] held]
    (observe/close-hold! h)
    (jtms/release! tms h)
    (observe/release-atom! sd)))

(defn settle
  "Settle belief (`settle*`) under a belief hold, re-settle while an un-merge gives
  spellings back (at most `max-unmerge-rounds` rounds), then deliver the moved region to
  the feed listeners, outside the relabel so a listener's write starts a fresh settle.
  Returns nil.  The un-merge rounds: docs/nmtms.md, \"The other half: a spelling an
  un-merge gives back\"."
  [kb]
  (let [held (hold-belief! kb)]
    (try
      ;; the readers of the whole settle share each family's pass cache
      (decide/with-pass true
        (loop [round 1]
          (let [seeds (volatile! #{})
                _     (binding [*unmerged-sink* seeds] (settle* kb))
                back  (into (vec @seeds) (respelled-seeds kb))]
            (cond
              (empty? back) nil
              (>= round max-unmerge-rounds)
              (trove/log! {:level :warn :id ::unmerge-fixpoint
                           :msg  (str "un-merge re-seeding did not converge in "
                                      max-unmerge-rounds " rounds; giving up")
                           :data {:rounds round :seeds (count back)}})
              ;; a given-back spelling is also a fact a descended equality is drawn
              ;; from, and the merge it rests on may have lost its route while the
              ;; spelling was superseded (`lost-derivation-seeds`)
              :else (do (rechain-seeds
                         kb (into back (lost-derivation-seeds
                                        kb (special/lost-descended-derivations kb back false))))
                        (recur (inc round)))))))
      (finally
        (publish-belief! held)))
    (feed/deliver! kb)
    nil))

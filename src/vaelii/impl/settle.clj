;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.settle
  "Belief settling: relabel the TMS, resolve soft contradictions on defeat-class,
  report the dilemmas and conflicts, and run the `exceptWhen` re-check queue to a joint
  fixpoint with belief.  The top engine layer, below `vaelii.core`.  See docs/nmtms.md."
  (:require [clojure.set :as set]
            [clojure.string :as str]
            [taoensso.trove :as trove]
            [vaelii.impl.capabilities :as cap]
            [vaelii.impl.chain :as chain]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.feed :as feed]
            [vaelii.impl.inherit :as inherit]
            [vaelii.impl.integrate :as integrate]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.predicates :as pr]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.settle-phases :as phases]
            [vaelii.impl.special :as special]
            [vaelii.impl.strength :as strength]
            [vaelii.impl.taxonomy :as tax :refer [*exposure-instance-budget*]]
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

;; ---- belief settling: soft, prioritized contradictions ------------------
;; Discover the nogoods, decide each on defeat-class, publish the dilemmas and conflicts
;; (docs/nmtms.md, "Soft, prioritized contradictions").

(def ^:dynamic *incremental-negations*
  "True (the default): `negation-nogoods` re-derives only the opposed bodies this settle
  could have moved and carries every other body's entry forward.  False: every opposed
  body is re-derived on every call, the exhaustive reference `negation_oracle_test`
  compares the memo against."
  true)

(defn- body-nogoods
  "What one opposed body yields now, as `{:nogoods :neg :pos}`.  `:nogoods` pairs every
  believed `(not body)` with every believed `body` whose contexts `share-a-view?`;
  `:neg` and `:pos` are the contexts each polarity is believed in, paired or not.  Reads
  as stored (`kb/sentexes-matching-as-stored` says why), so a superseded body yields
  nothing."
  [kb body share-a-view?]
  (let [tms (reasoning/tms kb)
        neg (vec (kb/sentexes-matching-as-stored kb (list 'not body) '?ctx)) ; believed (not body)
        pos (vec (kb/sentexes-matching-as-stored kb body '?ctx))]            ; believed body
    {:neg (into #{} (map :context) neg)
     :pos (into #{} (map :context) pos)
     :nogoods
     (into #{}
           (for [nx    neg
                 :let  [ctxN (:context nx)]
                 sx    pos
                 :let  [ctxX (:context sx)
                        vs   (share-a-view? ctxN ctxX)]
                 :when (and (not= (:id sx) (:id nx)) vs)]
             (let [p (max (strength/rank-of (jtms/defeat-class tms (:id nx)))
                          (strength/rank-of (jtms/defeat-class tms (:id sx))))]
               {:nogood #{(:id nx) (:id sx)} :priority p :vantages vs
                :sentence (list 'contradicts body (:sentence nx))})))}))

(defn- moved-bodies
  "The opposed bodies named by the relabelled region or posted to `dirty` — the memo's
  invalidation set apart from `genlCx` moves (docs/nmtms.md, \"The negation memo\").
  `scan` is `resolve-contradictions`' volatile `{:seen :bodies}`, updated here so each
  region handle's record is read once per settle; `region` is the round's `touched`, a
  delay."
  [kb opposed dirty scan region]
  (let [touched @region
        {:keys [seen bodies]} @scan
        bodies  (into bodies
                      (comp (remove seen)
                            (keep #(p/get-sentex (:records kb) %))
                            (map #(kb/body-under-not (:sentence %)))
                            (filter opposed))
                      touched)]
    (vreset! scan {:seen touched :bodies bodies})
    (into bodies (filter opposed) dirty)))

(defn- opposed-bodies-of
  "The opposed bodies `handles` name, or nil when nothing is opposed."
  [kb handles]
  (let [opposed @(reasoning/opposed kb)]
    (when (seq opposed)
      (into #{} (comp (keep #(p/get-sentex (:records kb) %))
                      (map #(kb/body-under-not (:sentence %)))
                      (filter opposed))
            handles))))

(defn- visibility-key
  "The order-free key for the joint-visibility question about two contexts, ordered by
  `nm/compare-form`, since the question is symmetric."
  [a b]
  (if (neg? (nm/compare-form a b)) [a b] [b a]))

(defn- visibility-pairs
  "The context pairs, one from each polarity, that one memo entry's pairing reads."
  [{:keys [neg pos]}]
  (for [a neg, b pos] (visibility-key a b)))

(defn- visibility-views
  "`{pair verdict}`: `tax/maximal-common-descendant-contexts` of each context pair in `ks`."
  [tax ks]
  (into {} (map (fn [[a b :as k]] [k (tax/maximal-common-descendant-contexts tax [a b])])) ks))

(defn- moved-verdicts
  "The pairs of `views` whose verdict now reads differently.  Exact: an entry none of
  whose pairs moved yields the pairing it yielded last settle."
  [tax views]
  (reduce-kv (fn [acc [a b :as k] v]
               (cond-> acc (not= v (tax/maximal-common-descendant-contexts tax [a b])) (conj k)))
             #{} views))

(defn- bodies-crossing
  "The memoized bodies whose pairing reads one of the pairs `ks`."
  [by-body ks]
  (into #{}
        (keep (fn [[body entry]]
                (when (some ks (visibility-pairs entry)) body)))
        by-body))

(defn- note-supersession-flips!
  "Post the handles keyed in one of the superseded maps `before` and `after` and not the
  other to the `:clashes` memo's dirty set, and their opposed bodies to the `:negations`
  memo's.  A supersession flip moves belief with no relabel, so neither memo's region
  sees it (docs/nmtms.md, \"The negation memo\")."
  [kb before after]
  (let [flipped (into (into #{} (remove after) (keys before))
                      (remove before)
                      (keys after))]
    (when (seq flipped)
      (swap! (reasoning/clashes kb) update :dirty (fnil into #{}) flipped))
    (when-let [bodies (seq (opposed-bodies-of kb flipped))]
      (swap! (reasoning/negations kb) update :dirty (fnil into #{}) bodies))))

(defn- negation-nogoods
  "The negation nogoods: every believed `(not X)` paired with a believed `X` whose two
  contexts share a descendant, each `{:nogood :priority :vantages :sentence}`.  Reads
  and CAS-writes the per-body memo `(reasoning/negations kb)`; `scan` and `region` are
  `moved-bodies`'.  See docs/nmtms.md, \"The negation memo\"."
  [kb scan region]
  (let [opposed @(reasoning/opposed kb)]
    (if (empty? opposed)
      ;; nothing can pair; the reset leaves no `:vocab`, so the next settle re-derives all
      (do (reset! (reasoning/negations kb) {}) #{})
      (let [tax   (reasoning/taxonomy kb)
            prev  @(reasoning/negations kb)
            vocab (tax/relation-gen tax :genlCx)
            ;; no stamp: a fresh KB, a `recover`, or the reset above
            stale? (or (not *incremental-negations*) (nil? (:vocab prev)))
            views  (:views prev {})
            carry  (if stale? {} (:by-body prev {}))
            shifted (when-not (or stale? (= vocab (:vocab prev)))
                      (moved-verdicts tax views))
            moved  (if stale?
                     opposed
                     (cond-> (moved-bodies kb opposed (:dirty prev) scan region)
                       (seq shifted) (into (bodies-crossing carry shifted))))
            ;; the vantages of a pair — the maximal common descendants of its two
            ;; contexts — or nil when no context sees both
            share-a-view? (memoize (fn [ca cb]
                                     (not-empty (tax/maximal-common-descendant-contexts
                                                 tax [ca cb]))))
            by-body (reduce (fn [m b]
                              (let [{:keys [neg pos nogoods] :as entry}
                                    (body-nogoods kb b share-a-view?)]
                                ;; a side believed nowhere: belief returns through the region
                                (if (or (seq nogoods) (and (seq neg) (seq pos)))
                                  (assoc m b entry)
                                  (dissoc m b))))
                            carry
                            moved)]
        (loop []
          (let [cur    @(reasoning/negations kb)
                ;; the posts that landed since `prev` was read; only this fn clears `:dirty`
                posted (set/difference (set (:dirty cur)) (set (:dirty prev)))
                kept   (apply dissoc by-body posted)
                next   {:vocab   vocab
                        :by-body kept
                        ;; pruned only on a full re-derivation
                        :views   (if stale?
                                   (visibility-views
                                    tax (into #{} (mapcat visibility-pairs) (vals kept)))
                                   (merge views
                                          (visibility-views tax shifted)
                                          (visibility-views
                                           tax (into #{} (mapcat visibility-pairs)
                                                     (vals (select-keys kept moved))))))
                        :dirty   posted}]
            (if (compare-and-set! (reasoning/negations kb) cur next)
              (into #{} (mapcat :nogoods) (vals kept))
              (recur))))))))

(def ^:dynamic *whole-store-region?*
  "True while `recover` runs the settle that follows `rebuild-tms`, whose region is the
  whole store.  `clash-candidates` and `preserving-candidates` skip their store-wide
  sweeps under it, and only when the region is also at least the store's sentex count
  (docs/nmtms.md, \"Which entry point the content came through\")."
  false)

(defn- vantage-reads
  "What one round of `resolve-contradictions` reads per vantage, each asked once per
  vantage and round: `{:tms :plain? :hidden (fn [v]) :withdrawal (fn [v])}`, the two fns
  `res/hidden-fn` and `res/withdrawal` memoized.  `:plain?` is true when the KB stores no
  `except` and holds no scoped defeat, where every vantage reads what the network reads
  and both fns answer nil.  A round weighs every standing nogood at every vantage before
  it mutates the network or the scoped-defeat roster, so the answers hold for the round."
  [kb]
  {:tms        (reasoning/tms kb)
   :plain?     (and (empty? @(reasoning/scoped-defeats kb)) (empty? @(reasoning/excepted kb)))
   :hidden     (memoize #(res/hidden-fn kb %))
   :withdrawal (memoize #(res/withdrawal kb %))})

(defn- class-at
  "`h`'s defeat-class as `vantage` reads it, or nil when `vantage` reads `h` as OUT.  The
  network's class, unless `vantage` withdraws part of what supports `h`; then the class is
  recomputed over the withdrawn region (`jtms/classes-in-region`).  A nil vantage is the
  network's own reading.  `rd` is `vantage-reads`."
  [{:keys [tms plain? withdrawal]} h vantage]
  (let [{:keys [region in]} (when (and vantage (not plain?)) (withdrawal vantage))]
    (if (contains? region h)
      (when (contains? in h) (get (jtms/classes-in-region tms region in) h))
      (jtms/defeat-class tms h))))

(defn- live-at?
  "Does `vantage` read every member of `nogood` as believed?  A nil vantage asks the
  network alone.  `rd` is `vantage-reads`."
  [{:keys [tms hidden]} nogood vantage]
  (let [hid (when vantage (hidden vantage))]
    (every? #(and (jtms/in? tms %) (not (and hid (hid %)))) nogood)))

(defn- live-vantages
  "The vantages of `ngmap` that read every member as believed, in content order.  A nogood
  its source gave no vantage is weighed by the network alone, as the nil vantage.  `rd` is
  `vantage-reads`."
  [{:keys [tms plain?] :as rd} {:keys [nogood vantages]}]
  (let [vs (cond (empty? vantages)      [nil]
                 (next (seq vantages))  (vec (sort vantages))
                 :else                  (vec vantages))]
    (if plain?
      (if (every? #(jtms/in? tms %) nogood) vs [])
      (filterv #(live-at? rd nogood %) vs))))

(defn- global-defeat?
  "Does a defeat of `h` weighed at `vantage` reach every reader of `h`?  True for a nil
  vantage, and when `h`'s context sees `vantage`; otherwise the defeat is scoped."
  [kb h vantage]
  (or (nil? vantage)
      (let [c (:context (p/get-sentex (:records kb) h))]
        (or (nil? c) (tax/sees? (reasoning/taxonomy kb) c vantage)))))

(defn- scope-defeats!
  "Record `pairs`, each `[vantage handle]`, as scoped defeats (`res/withdrawal` reads
  them).  Moves the change clock, since a scoped defeat changes what a read answers with
  no store or network mutation."
  [kb pairs]
  (swap! (reasoning/scoped-defeats kb)
         (fn [m] (reduce (fn [m [v h]] (update m v (fnil conj #{}) h)) m pairs)))
  (res/clear-withdrawn! kb)
  (observe/note-change))

(defn- note-vantage-disagreements!
  "Record, for each nogood in `weighed` whose vantages defeated different members, the
  `{vantage -> handle}` map of what each vantage decided.  `weighed` is `[[ngmap vantage
  decision] …]`, the whole round's weighing.  `res/withdrawal` and `disagreement-reports`
  read the roster (docs/nmtms.md, \"Vantages that disagree\")."
  [kb weighed]
  (let [entries (into []
                      (comp (map (fn [[ngmap decided]]
                                   {:ngmap ngmap
                                    :by    (into {} (keep (fn [[v d]]
                                                            (when-let [h (:defeat d)] [v h])))
                                                 decided)}))
                            (filter (fn [{:keys [by]}] (< 1 (count (distinct (vals by)))))))
                      (reduce (fn [m [ngmap v d]]
                                (update m ngmap (fnil conj []) [v d]))
                              {} weighed))]
    (when (seq entries)
      (swap! (reasoning/vantage-disagreements kb)
             (fn [v] (into v (remove (set v)) entries)))
      (res/clear-withdrawn! kb)
      (observe/note-change))))

(defn- clear-scoped-defeats!
  "Empty the scoped defeats and the vantage disagreements at the start of a settle, as
  `jtms/clear-defeats!` empties the network's defeated set."
  [kb]
  (when (or (seq @(reasoning/scoped-defeats kb)) (seq @(reasoning/vantage-disagreements kb)))
    (reset! (reasoning/scoped-defeats kb) {})
    (reset! (reasoning/vantage-disagreements kb) [])
    (observe/note-change))
  (res/reconcile-withdrawn! kb))

(defn- decide-nogood
  "Decide a nogood at `vantage` from the defeat-classes that vantage reads (`class-at`,
  over `rd`, `vantage-reads`):
  `{:defeat h}` for a unique weakest member, `{:dilemma ngmap}` for a defeasible minimum
  shared by several, `{:hard ngmap}` for a shared `:monotonic` minimum.  Never throws
  (docs/nmtms.md, \"Soft, prioritized contradictions\")."
  [rd {:keys [nogood] :as ngmap} vantage]
  (let [ranked  (mapv (fn [h] (let [c (class-at rd h vantage)] [h c (strength/rank-of c)]))
                      nogood)
        floor   (reduce min (map peek ranked))
        weakest (filterv #(= floor (peek %)) ranked)]
    (cond
      (= 1 (count weakest))                  {:defeat (ffirst weakest)}
      (strength/defeasible? (second (first weakest))) {:dilemma ngmap}
      :else                                  {:hard ngmap})))

(defn- reads-clash?
  "Does `vantage` still read `ngmap`'s members as a definitional clash?  Re-asks
  `checks/arbitrable-violations` from each member at `vantage`, for a round after one
  that may have defeated the grounds (docs/nmtms.md, \"A defeat is scoped to its
  vantage\")."
  [kb {:keys [nogood]} vantage]
  (let [recs (:records kb)]
    (boolean
     (some (fn [h]
             (when-let [s (p/get-sentex recs h)]
               (let [others (disj nogood h)]
                 (some (fn [v]
                         (let [opp (set (checks/opposing-handles v))]
                           (every? opp others)))
                       (checks/arbitrable-violations kb (:sentence s) vantage
                                                     (:context s))))))
           nogood))))

(defn- watched-count
  "How many handles `resolution-watch` watches: the stored `except`s (either polarity, as
  the functor root holds them) and the stored denials of an equation instance
  (`tax/instance-denials`).  One index count and one map read."
  [kb]
  (+ (reads/stored-count-with-functor (:index kb) sx/except-functor)
     (count (tax/instance-denials (reasoning/taxonomy kb)))))

(defn- watched-believed
  "The believed watched handles (`watched-count`), as a set."
  [kb]
  (let [tms (reasoning/tms kb)]
    (-> #{}
        (into (reads/believed-with-functor kb sx/except-functor))
        (into (filter #(jtms/in? tms %)) (keys (tax/instance-denials (reasoning/taxonomy kb)))))))

(defn- resolution-watch
  "Read before contradiction resolution, for `resolution-flips`: the belief of the
  watched handles (`watched-count`) as the pass enters resolution.  nil on a KB storing
  none of them.  Walks the smaller side: `region`, the pass's `touched`, when it holds
  no more handles than the watched pools, as `{:t0 region :in0 its-believed-members}`;
  else the pools, as `{:believed set}`."
  [kb region]
  (let [n (watched-count kb)]
    (when (pos? n)
      (let [t0 @region]
        (if (<= (count t0) n)
          {:t0 t0 :in0 (into #{} (filter #(jtms/in? (reasoning/tms kb) %)) t0)}
          {:believed (watched-believed kb)})))))

(defn- resolution-flips
  "The handles whose belief contradiction resolution flipped, from `watch`
  (`resolution-watch`) and the regions resolution received and returned.  Covers every
  flipped watched handle; the caller filters to the pool it acts on.

  Resolution moves belief only by `jtms/defeat`, which relabels, and never touches the
  superseded map, so a flipped handle is in the region resolution returned.  A region
  returned `identical?` to the one received means no defeat ran, and nothing flipped.
  The region-side comparison is exact: a member of `t0` is compared with its belief in
  `in0`, and a member only the defeat relabelled was first relabelled by it, so
  `jtms/touched-in` holds its label from before resolution.  A handle named here that
  did not flip would cost one queued re-check (`recheck-flipped-excepts`) and one noted
  move (`special/note-denial-flips!`), and never an answer, since both only schedule a
  re-derivation."
  [kb watch region-in region-out]
  (when (and watch (not (identical? region-in region-out)))
    (let [tms (reasoning/tms kb)]
      (if-let [believed (:believed watch)]
        (let [now (watched-believed kb)]
          (into (set/difference believed now) (set/difference now believed)))
        (let [{:keys [t0 in0]} watch
              was (jtms/touched-in tms)
              sup (jtms/superseded tms)]
          (-> #{}
              (into (filter #(not= (jtms/in? tms %) (contains? in0 %))) t0)
              (into (comp (remove t0)
                          (filter #(not= (jtms/in? tms %)
                                         (and (contains? was %) (not (contains? sup %))))))
                    @region-out)))))))

(defn- recheck-flipped-excepts
  "Queue the re-check for every visibility `except` in `handles` and return the rule
  handles it marked.  A belief flip on an except — defeated by this settle's resolution,
  or revived by `clear-defeats!` — hides or reveals as its arrival or departure does, and
  the store and removal choke points that call `recheck-except` never see it.  The
  returned rules mark the pass productive, since a reveal moves no blocked justification."
  [kb handles]
  (into #{}
        (comp (keep #(p/get-sentex (:records kb) %))
              (filter #(= sx/except-functor (nm/functor (:sentence %))))
              (mapcat #(special/recheck-except kb %)))
        handles))

(defn- released-by-defeat
  "The rules watching the predicate of a sentex in `handles`, which this pass newly
  defeated: an `(unknown S)` that now holds, or an exception that no longer does
  (docs/naf.md).  Returns the rule handles, which the pass re-chains."
  [kb handles]
  (into #{}
        (comp (keep #(p/get-sentex (:records kb) %))
              (mapcat #(special/rules-watching kb (sx/sentence-of %))))
        handles))

(defn- refresh-after-defeat
  "Reconcile the taxonomy with a defeat arbitration just applied, over `touched`, the
  region read after the defeat (docs/inherit.md)."
  [kb touched]
  (special/reconcile-belief-change kb touched)
  (tax/restore-depths (reasoning/taxonomy kb)))

(defn- preserved-rejoins-for
  "The forward rules whose preserving joins arbitration's defeat of `handles` may have
  moved, for the pass to re-chain (docs/inherit.md)."
  [kb handles]
  (into #{}
        (comp (keep #(p/get-sentex (:records kb) %))
              (mapcat #(inherit/rejoin-rules kb (sx/sentence-of %))))
        handles))

(defn- clash-report
  "A standing clash as a report map, the shape docs/nmtms.md (\"A clash is reported,
  never stored\") shows: the members as `:sides` in content order, each with its
  justifications.  `:kind` is the definitional violation's `:type`, `:inherited`, or nil
  for a rebuttal.  `:inherited` and `:vantages` appear only on the reports that carry
  them; the weighing contexts ride the metadata (`report-vantages`)."
  [kb {:keys [nogood priority sentence kind inherited vantages] ::keys [vantage-verdicts]}]
  (let [tms   (reasoning/tms kb)
        recs  (:records kb)
        ;; a side's justifications in `core/supporting-justifications`' content order
        jkey  (kb/justification-content-key kb)
        ;; Sides by sentence then context, which identify a sentex, so no handle enters
        ;; the key; `report_order_test` scans the `sort-by` line below for one.
        sides (->> nogood
                   (map (fn [h]
                          (let [s (p/get-sentex recs h)]
                            {:handle h :sentence (sx/sentence-of s) :context (:context s)
                             :defeat-class (jtms/defeat-class tms h)
                             :justifications (->> (jtms/supports tms h)
                                                  (keep #(p/get-justification recs %))
                                                  ;; keyed once per justification
                                                  (nm/sort-by-content-key jkey nm/compare-form))})))
                   (sort-by (juxt :sentence :context) nm/compare-form)
                   vec)]
    (-> (cond-> {:nogood nogood :priority priority :sentence sentence
                 :handles (mapv :handle sides)
                 :kind kind
                 :sides sides}
          inherited (assoc :inherited inherited)
          ;; `{vantage handle}`, on a vantage disagreement only
          vantage-verdicts (assoc :vantages vantage-verdicts))
        ;; metadata stays off the wire and out of `=`
        (vary-meta assoc ::vantages vantages))))

(defn report-vantages
  "The contexts that weighed report `r`'s clash, or nil for one the network weighed
  alone.  `core/contradictions`' reader arity keeps a report for a reader at or below
  one of them."
  [r]
  (::vantages (meta r)))

(defn- report-order
  "One clash report's sort key: each side's sentence then its context, in side order.
  Compared by `nm/compare-form`; no handle enters it."
  [r]
  (mapv (juxt :sentence :context) (:sides r)))

(defn ranked
  "`reports` in content order, by the `::order` key `record-clashes!` attached or, on a
  report without one, by `report-order`.  Every reader of `conflicts-of` or
  `contradictions-of` owes this call, since those hold arrival order."
  [reports]
  (vec (sort-by #(or (::order (meta %)) (report-order %)) nm/compare-form reports)))

(defn conflicts-of
  "The settle's conflict reports, in arrival order (`ranked` orders them).  Read off the
  one `:clash-readings` atom, so it and `contradictions-of` describe the same settle."
  [kb] (:conflicts @(reasoning/clash-readings kb)))

(defn contradictions-of
  "The settle's dilemma reports, in arrival order (`ranked` orders them)."
  [kb] (:contradictions @(reasoning/clash-readings kb)))

(defn disagreement-reports
  "One `clash-report` per standing vantage disagreement, each carrying `:vantages`, the
  `{vantage handle}` map of what each vantage decided.  Built from the roster at the read,
  so a settle whose region misses the pair keeps the report, and cached in `:withdrawn`
  until the next settle point drops it (`res/reconcile-withdrawn!`)."
  [kb]
  (let [ds    @(reasoning/vantage-disagreements kb)
        build #(mapv (fn [{:keys [ngmap by]}]
                       (clash-report kb (assoc ngmap ::vantage-verdicts by)))
                     ds)]
    (if (empty? ds)
      []
      ;; a reader of a settle's held belief neither reads nor fills the cache
      (jtms/through-cache
       (reasoning/tms kb) build
       #(let [cache (reasoning/withdrawn kb)
              m     @cache
              hit   (get m ::disagreement-reports ::absent)]
          (if (identical? ::absent hit)
            (let [rs (build)]
              (res/install-withdrawn! cache (::res/gen m) ::disagreement-reports rs)
              rs)
            hit))))))

(defn- record-clashes!
  "Publish the settle's conflicts and dilemmas, and the `{nogood report}` memo behind
  them, in one write to `:clash-readings`.  A nogood none of whose members is in
  `touched`, and whose `:kind` and vantages match its memoized report, keeps that report
  (docs/nmtms.md, \"The reports are rebuilt only where the region moved\").  Runs before
  `jtms/reset-touched!`."
  [kb violated dilemmas touched]
  (let [prev  (:reports @(reasoning/clash-readings kb))
        moved (set touched)
        build (fn [ng]
                (or (when-not (some moved (:nogood ng))
                      (when-let [r (get prev (:nogood ng))]
                        (when (and (= (:kind ng) (:kind r))
                                   (= (:vantages ng) (report-vantages r)))
                          r)))
                    (clash-report kb ng)))
        ;; stored in arrival order; `ranked` sorts at the read, by this key
        keyed (fn [r] (cond-> r (nil? (::order (meta r)))
                              (vary-meta assoc ::order (report-order r))))
        vs    (mapv (comp keyed build) violated)
        ds    (mapv (comp keyed build) dilemmas)]
    (reset! (reasoning/clash-readings kb)
            {:reports        (into {} (map (juxt :nogood identity)) (concat vs ds))
             :conflicts      vs
             :contradictions ds})))

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

;; ---- narrowing the re-check to the firings a trigger can reach ----------
;;
;; A memory-only filter over a queued rule's firings, run before any level-6 query, in
;; which every "cannot tell" answers keep: docs/exceptions.md, "Narrowing the re-check to
;; the firings a trigger can reach".

(defn- peel-negation
  "`s` with every `not` wrapper stripped.  Polarity is dropped: the shape test asks only
  which content a trigger is about."
  [s]
  (if (and (sequential? s) (= 'not (first s)) (= 2 (count s)))
    (recur (second s))
    s))

(defn- literal-shape
  "`[predicate {argument -> count}]` of `lit` with polarity dropped, or nil when `lit` is
  not flat and ground.  The arguments are a multiset, so a symmetric predicate's mirrored
  fact has the same shape."
  [lit]
  (let [body (peel-negation lit)]
    (when (and (sequential? body) (symbol? (nm/functor body)))
      (let [as (nm/args body)]
        (when (and (seq as)
                   (not-any? sequential? as)               ; a nested subterm: cannot tell
                   (not-any? #(and (symbol? %) (sx/variable? %)) as))
          [(nm/functor body) (frequencies as)])))))

(defn- cross-argument-predicate?
  "Can a level-6 prover derive `pred` from content with different arguments?  Then
  argument agreement proves nothing about it, and the caller keeps every candidate.
  True for the closure relations, `disjoint`, the evaluables, a predicate declared
  transitive, reflexive or with an inverse, and one `inherit/declared-about?` names as
  having a preserved argument position.  The property reads are global."
  [kb pred]
  (let [tx (reasoning/taxonomy kb)]
    (or (contains? provers/transitive-predicates pred)
        (contains? provers/evaluable-predicates pred)
        (= 'evaluate pred)
        (= 'disjoint pred)
        (tax/has-prop? tx :transitive pred)
        (tax/has-prop? tx :reflexive pred)
        (seq (tax/inverses-under tx pred))
        (inherit/declared-about? kb pred))))

(defn- merge-normalizer
  "A `literal -> literal` fn mapping every symbol to its equality-class representative,
  read unscoped, or nil when the partition is empty.  The caller applies it to both sides
  of the shape test."
  [kb]
  (when (tax/merged-term-pred (reasoning/taxonomy kb))
    (fn [lit] (res/representative-term kb nil lit))))

(defn- trigger-shapes
  "The shapes of a rule's queued triggers, or `:all` when the rule was queued
  unconditionally or any trigger has no readable shape.  `norm` is `merge-normalizer`,
  applied here and to the conjunct side alike."
  [triggers norm]
  (if (#{:all :all-rejoin} triggers)
    :all
    (let [ss (map #(literal-shape (cond-> % norm norm)) triggers)]
      (if (some nil? ss) :all (set ss)))))

(defn- reachable-predicates
  "The trigger predicates that can answer the exception conjunct `lit`, whose predicate is
  `pred`: the global `specs` of `pred` for a positive conjunct, and `specs` plus `genls`
  for a negated one."
  [kb pred lit]
  (let [tax (reasoning/taxonomy kb)]
    (if (sx/negation? lit)
      (into (tax/specs-global tax pred) (tax/genls-global tax pred))
      (tax/specs-global tax pred))))

(defn- firing-reachable?
  "Could a trigger of a shape in `shapes` have flipped this firing's block condition?
  `except` is the rule's block literals; `bindings` are substituted into each, and one
  literal whose arguments agree with a trigger's and whose `reachable-predicates` hold the
  trigger's predicate is enough.  An unreadable literal, or one on a `cross?` predicate,
  keeps the firing.

  `cross?` is `cross-argument-predicate?` memoized by the caller for the pass, because
  one of its arms reads the index and the filter reads nothing but memory per firing.
  `norm` is `merge-normalizer`'s answer, applied to each substituted literal as it is to
  the trigger shapes."
  [kb except bindings shapes cross? norm]
  (boolean
   (some (fn [lit]
           (let [lit' (cond-> (res/substitute lit bindings) norm norm)]
             (if-let [[lp la] (literal-shape lit')]
               (or (cross? lp)
                   (let [reach (reachable-predicates kb lp lit')]
                     (some (fn [[tp ta]] (and (= la ta) (contains? reach tp))) shapes)))
               true)))                                    ; unreadable conjunct: keep
         except)))

(defn- withdrawal-marker?
  "Is queued trigger `t` one of `special`'s withdrawal markers rather than a sentence?"
  [t]
  (or (keyword? t) (map? t)))

(defn- blocked-firings
  "The members of `firings` the blocked set holds, walking whichever is smaller."
  [blocked firings]
  (if (< (count blocked) (count firings))
    (filter #(contains? firings %) blocked)
    (filter #(contains? blocked %) firings)))

(defn- entailment-candidates
  "The firings of rule `rsx` whose `chain/entailment-withdrawn?` answer an `::entailment`
  marker can have moved: the blocked ones, which a satisfiable network releases, and the
  rest only while some network the rule joins on is unsatisfiable
  (`chain/entailment-withdrawable?`) — or all of them when a block literal is on a
  predicate a calculus answers, whose answer moves with the whole network."
  [kb rsx firings block-lits blocked]
  (if (or (chain/entailment-withdrawable? kb rsx)
          (some #(let [b (peel-negation %)]
                   (and (sequential? b) (chain/answered-by-calculus? kb (nm/functor b))))
                block-lits))
    firings
    (blocked-firings @blocked firings)))

(defn- preserving-candidates
  "The firings of rule `rsx` a `{::preserving s}` marker can have moved: those binding an
  antecedent on a declared predicate to a goal one of the markers' sentences moves
  (`inherit/moved-goal-test`), each also read under the equality representative
  (`merge-normalizer`).  All of them when a sentence has no test or no antecedent is on
  a declared predicate."
  [kb rsx firings sens test-for norm]
  (let [tests (for [s sens, s' (cond-> [s] norm (conj (norm s)))] (test-for s'))
        antes (filterv #(and (sequential? %) (symbol? (nm/functor %))
                             (not= 'not (nm/functor %))
                             (inherit/declared-about? kb (nm/functor %)))
                       (:antecedent rsx))]
    (if (or (some nil? tests) (empty? antes))
      firings
      (filter (fn [jid]
                (if-let [j (p/get-justification (:records kb) jid)]
                  (some (fn [a]
                          (let [g (res/substitute a (:bindings j))]
                            (some (fn [t] (or (t g) (and norm (t (norm g))))) tests)))
                        antes)
                  false))
              firings))))

(defn- exception-candidates
  "The justifications of the queued rules whose block condition the queued triggers could
  have flipped.  One record fetch per rule, and none for a rule queued `:all`, which
  keeps every firing.  The block literals are the exception conjuncts read through
  their query frames (`rules/watched-literals`), the NAF inner queries and the aggregate
  bodies (docs/naf.md).  A withdrawal marker adds the firings its own test keeps
  (`entailment-candidates`, `preserving-candidates`)."
  [kb queued]
  (let [tms      (reasoning/tms kb)
        cross?   (memoize #(cross-argument-predicate? kb %))
        norm     (merge-normalizer kb)
        blocked  (delay (jtms/blocked tms))
        test-for (memoize #(inherit/moved-goal-test kb %))]
    (into #{}
          (mapcat (fn [[rh triggers]]
                    (let [firings (jtms/dependents tms rh)]
                      (if (#{:all :all-rejoin} triggers)
                        firings
                        (let [sens   (remove withdrawal-marker? triggers)
                              marks  (filter withdrawal-marker? triggers)
                              shapes (when (seq sens) (trigger-shapes sens norm))
                              rsx    (when (or (seq marks) (not= :all shapes))
                                       (p/get-sentex (:records kb) rh))
                              block-lits (when rsx
                                           (concat (mapcat rules/watched-literals
                                                           (apply concat (provers/rule-exceptions kb rh)))
                                                   (rules/naf-queries rsx)
                                                   (rules/aggregate-queries rsx)))
                              pres   (keep ::special/preserving marks)]
                          (cond
                            (and (seq sens) (or (= :all shapes) (empty? block-lits)))
                            firings                        ; nothing to narrow by
                            (and (seq marks) (nil? rsx)) firings
                            :else
                            (concat
                             (when (seq sens)
                               ;; the bindings are on the record: the network keeps only
                               ;; what belief is computed from (`jtms/graph-just`)
                               (filter (fn [jid]
                                         (if-let [j (p/get-justification (:records kb) jid)]
                                           (firing-reachable? kb block-lits (:bindings j) shapes
                                                              cross? norm)
                                           false))
                                       firings))
                             (when (some #{::special/entailment} marks)
                               (entailment-candidates kb rsx firings block-lits blocked))
                             (when (seq pres)
                               (preserving-candidates kb rsx firings pres test-for
                                                      norm)))))))))
          queued)))

(defn- exception-blocked-set
  "The blocked set after re-deciding the exceptions of `exception-candidates`' firings:
  a block outside the candidates is carried forward, and every candidate is re-decided
  from scratch.  The whole set, since `jtms/set-blocked` replaces rather than adds."
  [kb queued]
  (let [tms   (reasoning/tms kb)
        cands (exception-candidates kb queued)
        held  (into #{} (remove cands) (jtms/blocked tms))]
    (into held
          (filter (fn [jid]
                    (when-let [j (p/get-justification (:records kb) jid)]
                      (chain/justification-excepted? kb j))))
          cands)))

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
  "A volatile collecting the spellings an un-merge gave back, or nil.  `settle` binds it,
  `settle-finish` fills it from `special/refresh-supersessions`, and `settle` re-seeds
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

(defn- released-refusals
  "The recorded refusals the queued triggers may have released: `{:free [[rule-handle
  entry] …] :overflow [rule-handle …]}`.  Narrowed as `exception-candidates` narrows
  justifications.  A dead entry is dropped as it is read, and an overflowed rule is named
  for the caller to re-join (docs/exceptions.md, \"A refused firing is remembered as
  bindings\")."
  [kb queued]
  (let [refused @(reasoning/refused kb)]
    (if (empty? refused)
      {:free [] :overflow []}
      (let [cross? (memoize #(cross-argument-predicate? kb %))
            norm   (merge-normalizer kb)]
        (reduce
         (fn [acc [rh triggers]]
           (let [recs (get refused rh)]
             (cond
               (nil? recs)        acc
               (= :overflow recs) (update acc :overflow conj rh)
               :else
               (let [shapes (if (and (set? triggers) (some withdrawal-marker? triggers))
                              :all             ; a marker keeps every refusal, as `:all` does
                              (trigger-shapes triggers norm))
                     rsx    (when-not (= :all shapes) (p/get-sentex (:records kb) rh))
                     ;; the two block conditions the record covers, frames peeled
                     ;; as in `exception-candidates`
                     lits   (when rsx
                              (concat (mapcat rules/watched-literals
                                              (apply concat (provers/rule-exceptions kb rh)))
                                      (rules/naf-queries rsx)))]
                 (reduce (fn [acc e]
                           (case (chain/refusal-state kb rh e)
                             :free (update acc :free conj [rh e])
                             :dead (do (chain/drop-refusal! kb rh e) acc)
                             acc))
                         acc
                         (if (seq lits)
                           (filter #(firing-reachable? kb lits (:bindings %) shapes cross?
                                                       norm)
                                   recs)
                           recs))))))
         {:free [] :overflow []}
         queued)))))

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

(defn- released-mints
  "The types minted by declarations whose type has become mintable since they were
  swept, as new handles to chain from (`special/release-mint!`).  Re-asked only when a
  `genl` or `genlCx` generation has moved since the entry was stamped, since nothing else
  changes what `mintable-type?` answers.  Not during a rebuild, for
  `released-constraint-refusals`' reason."
  [kb]
  (let [pending (when-not *rebuilding?* (special/mint-refusals kb))]
    (if (empty? pending)
      []
      (let [gens (chain/constraint-generations kb)]
        (special/minted-seeds
         kb
         (into []
               (mapcat (fn [[dh e]]
                         (when (not= gens (:gens e))
                           (:new (special/release-mint! kb dh gens)))))
               pending))))))

(defn- revived-mark-seeds
  "The merges and lifts a mark, or a `genl` edge under one, in `revived` owes the facts
  stored while it was OUT, as new handles to chain from
  (`special/revived-declaration-sweeps`).  Reconciles the retired spellings and reports
  the violations, as `assert-one` does for the same sweeps on an arrival.  `revived` is
  `revived-seeds`' answer, so a rebuild asks nothing."
  [kb revived]
  (if-let [mig (special/revived-declaration-sweeps kb revived)]
    (do (when (seq (:superseded mig))
          (special/refresh-supersessions kb (:superseded mig)))
        (violations/report kb (:violations mig))
        (:new mig))
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
    (if-let [mig (special/drain-except-moves! kb #(apply-removals! kb %))]
      (do (violations/report kb (:violations mig))
          (:new mig))
      [])))

(defn- released-subsumed
  "The mints a record leaving belief or the store no longer lets the KB withhold, as new
  handles to chain from (`special/withheld-releases`).  `withdrawn` is the mints this
  settle withdrew, whose own departure releases nothing.  Empty during a rebuild, which
  drops the queued departures: a restore changes nothing."
  [kb moved asked withdrawn]
  (if *rebuilding?*
    (do (special/drain-departures! kb) [])
    (:new (special/withheld-releases kb moved (jtms/touched-in (reasoning/tms kb))
                                     asked withdrawn))))

(defn- subsumed-blocks
  "The mint justifications this settle withdraws, and the records they held up:
  `special/subsumed-mint-blocks` over `moved`, the delay of the region's sentexes
  `released-subsumed` reads too."
  [kb moved was-in asked]
  (or (special/subsumed-mint-blocks kb moved was-in asked)
      {:blocked #{} :withdrawn #{}}))

(defn- revived-seeds
  "The datums `jtms/revived` finds in `region` (the pass's `touched`, as a delay), minus
  `done`, the ones an earlier pass of this settle already re-seeded.  Nil during a
  rebuild (docs/nmtms.md, \"A revived datum is a datum the agenda has not seen\")."
  [kb done region]
  (when-not *rebuilding?*
    (into [] (remove done) (jtms/revived (reasoning/tms kb) @region))))

(defn- departed-handles
  "The handles in `region` (the pass's `touched`, as a delay) that went IN ⇒ OUT this
  settle: the window `departed-seeds` and `defeated-derivation-seeds` both read.  Empty
  during a rebuild."
  [kb region]
  (if *rebuilding?*
    []
    (let [tms (reasoning/tms kb)
          was (jtms/touched-in tms)]
      (into [] (filter #(and (contains? was %) (not (jtms/in? tms %)))) @region))))

(defn- departed-seeds
  "The facts owed a re-join because a `genl` or `genlCx` edge in `out` (`departed-handles`)
  went IN ⇒ OUT, minus `done` (`special/departed-edge-seeds`).  A defeat sweeps nothing, so
  this is the re-join a retraction gets from `special/resubsumption-seeds`
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
  "The argument-type entailments and descended equalities a `genl` edge took OUT when this
  settle defeated it, drawn again over a route that survives — `departed-seeds`' twin for
  the derivations that name the edge rather than for the firings.  An equality whose
  facts the defeated merge still supersedes is drawn by `settle`'s un-merge round
  instead, once the spellings are back.

  `out` is `departed-handles`' answer for the pass."
  [kb out]
  (if (seq out)
    (lost-derivation-seeds kb (special/lost-descended-derivations kb out true))
    []))

(defn- witness-paths
  "The witness edges among `sentences` (`{handle sentence}`, one justification's
  antecedents) joined into paths, as `{:rel :a :b :edges}`: the `genl` and `genlCx` edges,
  and the edges of a relation some `transitiveInArg` among them preserves a claim along.
  A path is what the firing depends on, so its two ends are the reachability a second
  route can answer for."
  [sentences]
  (let [binary    (fn [s] (when (and (seq? s) (= 2 (count (nm/args s))))
                            [(nm/functor s) (first (nm/args s)) (second (nm/args s))]))
        preserved (into #{} (keep (fn [s] (when (and (seq? s) (= 'transitiveInArg (nm/functor s)))
                                            (last (nm/args s)))))
                        (vals sentences))
        edges     (into [] (keep (fn [[h s]]
                                   (when-let [[f a b] (binary s)]
                                     (when (or (contains? tax/closure-relations f)
                                               (contains? preserved f))
                                       [h f a b]))))
                        sentences)]
    (into []
          (mapcat (fn [[rel es]]
                    (let [out  (group-by #(nth % 2) es)
                          tgts (into #{} (map #(nth % 3)) es)]
                      (for [a (distinct (remove tgts (map #(nth % 2) es)))]
                        (loop [n a, hs #{}]
                          (if-let [[h _ _ b] (first (remove #(contains? hs (first %)) (out n)))]
                            (recur b (conj hs h))
                            {:rel rel :a a :b n :edges hs}))))))
          (group-by second edges))))

(defn- reaches-at?
  "Does `reader` reach `b` from `a` over `rel`, on the edges it sees and believes?"
  [kb reader rel a b]
  (let [tx (reasoning/taxonomy kb)]
    (case rel
      genl   (tax/genl? tx a b reader)
      genlCx (tax/sees? tx a b)
      (contains? (inherit/witness-terms kb {:rel rel :inverse? false} a reader) b))))

(defn- rerouteable
  "The facts to re-chain for justification `j` at `reader`, or nil: non-nil when every
  antecedent `reader` reads as withdrawn is a witness edge, and `reader` still reaches
  both ends of every path such an edge lies on."
  [kb reader out j]
  (let [tms  (reasoning/tms kb)
        rests (jtms/rests-on j)
        gone (into #{} (filter #(or (contains? out %) (not (jtms/in? tms %)))) rests)]
    (when (seq gone)
      (let [sentences (into {} (keep (fn [h] (when-let [sx (p/get-sentex (:records kb) h)]
                                               [h (:sentence sx)])))
                            rests)
            paths     (witness-paths sentences)
            hit       (filter #(some gone (:edges %)) paths)]
        (when (and (every? (into #{} (mapcat :edges) paths) gone)
                   (every? (fn [{:keys [rel a b]}] (reaches-at? kb reader rel a b)) hit))
          (into [] (remove gone) (:antecedents j)))))))

(defn- lost-firing-seeds
  "`[[reader seeds] …]`: the facts to re-chain, per reader, under `chain/*witness-view*`,
  for the firings a reader reads as withdrawn only because an edge of a path they name
  is withdrawn there, while the reader still reaches that path's ends and believes the
  firing's sentence through no other sentex.  The readers are the contexts that see a
  scoped defeat's vantage or an excepting context.  `done` holds the `[reader handle]`
  pairs an earlier pass re-chained.  Nil when the KB holds no scoped defeat and no
  `except`, and during a rebuild (docs/nmtms.md, \"Where the layer stops\").

  A firing is a candidate only in a reader's `:derived` set (`res/withdrawal`): an
  `except` target or a scoped-defeated handle is withdrawn by name, not over a path, so
  the walk is proportional to what rests on those and not to how many there are."
  [kb done]
  (let [sd @(reasoning/scoped-defeats kb)
        ex @(reasoning/excepted kb)]
    (when (and (not *rebuilding?*) (or (seq sd) (seq ex)))
      (let [tx      (reasoning/taxonomy kb)
            tms     (reasoning/tms kb)
            tops    (into (set (keys sd)) (keys ex))
            ;; a reader's `:derived` leaves out its own seeds; a target is left out for
            ;; every reader, so ask the rosters per candidate rather than build their union
            target? (fn [h] (or (some #(contains? % h) (vals sd))
                                (some #(contains? % h) (vals ex))))
            readers (filter (fn [c] (some #(tax/sees? tx c %) tops)) (tax/contexts tx))]
        (into []
              (keep (fn [r]
                      (let [{:keys [out derived]} (res/withdrawal kb r)
                            out   (or out #{})
                            seeds (into []
                                        (comp (remove target?)
                                              (remove #(contains? done [r %]))
                                              (keep (fn [h]
                                                      (let [js (keep #(jtms/justification tms %)
                                                                     (jtms/supports tms h))
                                                            ss (into [] (mapcat #(rerouteable kb r out %)) js)]
                                                        (when (and (seq ss)
                                                                   (empty? (res/matches-visible
                                                                            kb (:sentence (p/get-sentex (:records kb) h))
                                                                            r)))
                                                          [h ss])))))
                                        derived)]
                        (when (seq seeds) [r seeds]))))
              readers)))))

(defn- blanket-recheck-rules
  "The queued rules with no triggering sentence (`:all` or `:all-rejoin`: a taxonomy edge
  moved, or the rule was just indexed) or with a withdrawal marker.  They take the coarse
  re-chain, since nothing says whether the move blocked or released."
  [queued]
  (keep (fn [[rh triggers]]
          (when (or (#{:all :all-rejoin} triggers) (some withdrawal-marker? triggers)) rh))
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

;; ---- believed content, and the clash no single writer could see -----------
;;
;; The believed-content readers the retroactive sweeps and the arbitration vantages
;; share, and `exposed-clashes`' per-term clash reader (docs/contexts.md).

(defn- believed-xf
  "A transducer from handles to the believed, positive sentexes among them.  Belief is
  `jtms/in?`, so a superseded spelling drops out with a defeated one."
  [kb]
  (comp (filter #(jtms/in? (reasoning/tms kb) %))
        (keep #(p/get-sentex (:records kb) %))
        (filter #(not (sx/negative? %)))))

(defn- believed-in-ancestors
  "The believed, positive sentexes stored across `contexts`, lazily and in the order
  `contexts` gives, so a budgeted consumer realizes only its prefix (docs/taxonomy.md,
  \"What a declaration reaches back over\").  A non-symbol context is dropped."
  [kb contexts]
  (for [c     (filter symbol? contexts)
        s     (keep #(p/get-sentex (:records kb) %)
                    (filter #(jtms/in? (reasoning/tms kb) %)
                            (reads/as-stored-in-context (:index kb) c)))
        :when (not (sx/negative? s))]
    s))

(defn- believed-at-arg
  "The believed, positive sentexes posted on `term`'s argument-`pos` root, or nil for a
  non-symbol `term`.  The partner read of `exposed-clashes`, the retroactive sweeps and
  the arbitration vantages.  Most partners share position 1; an `anti_transitive` chain
  reaches a tuple by its target, so its partner read is at position 2."
  [kb pos term]
  (when (symbol? term)
    (into [] (believed-xf kb) (reads/as-stored-with-arg (:index kb) pos term))))

(defn- believed-at-arg1
  "`believed-at-arg` at position 1 — the membership and slot-partner read, which is most
  of them."
  [kb term]
  (believed-at-arg kb 1 term))

(defn- believed-memberships
  "The believed positive unary memberships of `x`, as `[type context handle]` triples,
  in content order."
  [kb x]
  ;; `compare` on the symbols: a keyfn runs per comparison and would allocate each time.
  ;; Symbols order by namespace then name.
  (sort (fn [[t1 c1] [t2 c2]]
          (let [r (compare t1 t2)] (if (zero? r) (compare c1 c2) r)))
        (into []
              (keep (fn [s]
                      (let [sen (:sentence s)]
                        (when (and (sequential? sen) (= 2 (count sen))
                                   (symbol? (first sen))
                                   (= x (second sen)))
                          [(first sen) (:context s) (:id s)]))))
              (believed-at-arg1 kb x))))

(defn- exposure-probes
  "`{:disjoint? (fn [t1 t2]) :visible-from (fn [t1 c1 t2 c2])}` over the taxonomy `tax`,
  each memoized for one pass.  `:visible-from` is the maximal common descendant contexts
  of the first disjointness witness that shares one with `c1` and `c2`, or nil; it
  enumerates witnesses only after the scoped `disjoint?` at some common descendant of `c1`
  and `c2` says one exists (docs/contexts.md)."
  [tax]
  (let [dj  (volatile! {})
        vis (volatile! {})
        memo (fn [v k f]
               (if-let [e (find @v k)]
                 (val e)
                 (let [r (f)] (vswap! v assoc k r) r)))]
    {:disjoint?
     (fn [t1 t2] (memo dj [t1 t2] #(tax/disjoint? tax t1 t2)))
     :visible-from
     (fn [t1 c1 t2 c2]
       (memo vis [t1 c1 t2 c2]
             #(when (some (fn [k] (tax/disjoint? tax t1 t2 k))
                          (tax/common-descendants tax [c1 c2]))
                (some (fn [w]
                        (let [m (tax/maximal-common-descendant-contexts
                                 tax (into [c1 c2] w))]
                          (when (seq m) m)))
                      (distinct (tax/disjointness-witnesses tax t1 t2))))))}))

(defn- exposed-clashes-for-term
  "The `:disjoint` entries for the jointly-visible clashes among `x`'s believed
  memberships.  `probes` is `exposure-probes`' answer."
  [kb x {:keys [disjoint? visible-from]}]
  (let [ms (believed-memberships kb x)]
    (for [i (range (count ms))
          j (range (inc i) (count ms))
          :let  [[t1 c1] (nth ms i)
                 [t2 c2] (nth ms j)]
          :when (and (not= t1 t2) (disjoint? t1 t2))
          :let  [mx (visible-from t1 c1 t2 c2)]
          :when mx]
      {:violation :disjoint
       :detail    {:term         x
                   :held         [[t1 c1] [t2 c2]]
                   :visible-from mx
                   :message      (str "disjointness clash exposed: " x " holds " t1
                                      " (in " c1 ") and " t2 " (in " c2
                                      "), jointly visible from "
                                      (pr-str (vec (sort nm/compare-form mx))))}})))

;; `*exposure-instance-budget*` is `vaelii.impl.taxonomy`'s, `:refer`red, because `settle`
;; and `special` both spend it and `settle` requires `special`.  A re-`def` here would be a
;; second var, and a `binding` of one would not reach the other.

;; ---- the two halves every bounded pass is made of ------------------------
;;
;; The take and the notice every pass spending `*exposure-instance-budget*` is built from,
;; stated once.

(defn- take-budgeted
  "The prefix of `xs` the budget in the volatile `left` still allows, as `[taken cut?]`
  with `taken` a vector, debiting `left`.  One element past the budget is realized, so
  `cut?` is true exactly when an element went unread (docs/defenses.md, \"A bounded
  sweep reports its cut once, read one past the budget\").  A cut sets `left` to zero, so
  the later enumerations of the pass take nothing; a negative `left` reads as zero.

  The tail past the prefix is unread, which is why an enumeration handed here is not
  sorted.  The cap bounds the postings read, not the work of building `xs`.  The budget
  bounds what is enumerated, so a caller filters after the take."
  [left xs]
  (let [n     (max 0 (long @left))
        taken (into [] (take (inc n)) xs)
        cut?  (> (count taken) n)]
    (vreset! left (if cut? 0 (- n (count taken))))
    [(if cut? (subvec taken 0 n) taken) cut?]))

(defn- cut-notice
  "The one ledger entry a bounded sweep files when `cut`, the units it did not look at, is
  non-empty, else nil: `kind`, the count under `count-key`, a `:sample` of three, the
  `:budget` and a message built from `sweep`, `unit`, `noun` and `consequence`.  Filed off
  the cut and never off the findings, once per pass (docs/defenses.md, \"A bounded sweep
  reports its cut once, read one past the budget\").  A pass reporting two bounds builds
  its own entry."
  [kind cut {:keys [sweep unit noun consequence count-key]}]
  (when (seq cut)
    {:violation kind
     :detail    (array-map
                 count-key (count cut)
                 :sample   (vec (take 3 cut))
                 :budget   *exposure-instance-budget*
                 :message  (str sweep " sweep cut short at " *exposure-instance-budget*
                                " " unit ": " (count cut) " " noun "(s) went unswept, so "
                                consequence))}))

(defn- instances-below
  "The terms holding a believed, positive unary membership in any global spec of `types`:
  the candidates a separating declaration or a new `genl` edge can put in a clash.  Lazy
  and unsorted, so a budgeted consumer realizes only its prefix (docs/taxonomy.md, \"What
  a declaration reaches back over\").  A non-symbol type or member is dropped: a compound
  heads no stored membership."
  [kb types]
  (let [tax (reasoning/taxonomy kb)]
    (for [t     (filter symbol? types)
          t'    (filter symbol? (tax/specs-global tax t))
          s     (keep #(p/get-sentex (:records kb) %)
                      (filter #(jtms/in? (reasoning/tms kb) %)
                              (reads/as-stored-with-functor (:index kb) t')))
          :when (and (not (sx/negative? s))
                     (= 1 (count (rest (:sentence s))))
                     (symbol? (second (:sentence s))))]
      (second (:sentence s)))))

(defn- denial-of
  "`[p x]` for a sentex denying a unary membership `(not (p x))`, `p` and `x` symbols, or
  nil for any other sentex."
  [s]
  (let [sen (:sentence s)]
    (when (sx/negation? sen)
      (let [body (second sen)]
        (when (and (sequential? body) (= 2 (count body))
                   (symbol? (first body)) (symbol? (second body)))
          [(first body) (second body)])))))

(defn- refutable-terms
  "The terms holding a believed denial of the part among `parts` with the fewest stored
  facts: the candidates a cover over `parts` arriving can refute, since a refutation
  denies every part.  Ties break on the part symbol.  Lazy and unsorted, for
  `instances-below`' reason."
  [kb parts]
  (when-let [part (nm/min-by-content-key
                   (fn [p] [(reads/stored-count-with-functor (:index kb) p) p]) compare
                   (filter symbol? (distinct parts)))]
    (for [s     (keep #(p/get-sentex (:records kb) %)
                      (filter #(jtms/in? (reasoning/tms kb) %)
                              (reads/as-stored-with-functor (:index kb) part)))
          :let  [[p x] (denial-of s)]
          :when (= part p)]
      x)))

(defn- members-in-ancestors
  "The terms of the believed unary memberships stored in the contexts `sub` now sees: the
  candidates a `genlCx` edge can put in joint sight.  Lazy and in the ancestor set's own
  order, for `instances-below`'s reason."
  [kb sub]
  (for [s     (believed-in-ancestors kb (tax/context-up (reasoning/taxonomy kb) sub))
        :let  [sen (:sentence s)]
        :when (and (sequential? sen) (= 2 (count sen))
                   (symbol? (first sen)) (symbol? (second sen)))]
    (second sen)))

;; ---- what a declaration reaches back over --------------------------------
;;
;; The candidate enumerations a declaration arriving puts back in question: docs/taxonomy.md,
;; "What a declaration reaches back over".

(defn- spec-closure
  "The union of the down-closures of `types` — the type labels a membership must carry
  to sit below any of them."
  [tax types]
  (into #{} (comp (filter symbol?) (mapcat #(tax/specs-global tax %))) types))

(defn- extent-size
  "How many stored facts sit under the spec `closure`, any arity: `count-with-functor` per
  member.  Only picks which side of a separation to walk, so a miscount costs a worse
  choice of side and never an answer."
  [kb closure]
  (transduce (map #(reads/stored-count-with-functor (:index kb) %)) + 0 closure))

(defn- holds-below?
  "Does `term` hold a believed unary membership whose type is in `closure`?  Read off
  the argument-1 root — the posting `kb/types-of` reads — so it is one seek per term
  rather than a walk of the other side's extent."
  [kb closure term]
  (boolean
   (some (fn [h]
           (when-let [s (p/get-sentex (:records kb) h)]
             (let [sen (:sentence s)]
               (and (sequential? sen) (= 2 (count sen))
                    (contains? closure (first sen))
                    (not (sx/negative? s))
                    (jtms/in? (reasoning/tms kb) (:id s))))))
         (reads/as-stored-with-arg (:index kb) 1 term))))

(defn- holds-two-members?
  "Does `term` hold believed memberships below two distinct members of a metatype?
  `owner` is `member-owners`' `type -> #{member}` map, so one pass over the term's
  argument-1 root answers it, stopping at the second member."
  [kb owner term]
  (> (count (reduce (fn [seen h]
                      (if-let [s (p/get-sentex (:records kb) h)]
                        (let [sen (:sentence s)]
                          ;; `sequential?` first: `count` throws on a non-sequence
                          (if (and (sequential? sen) (= 2 (count sen)) (not (sx/negative? s))
                                   (jtms/in? (reasoning/tms kb) (:id s)))
                            (let [seen' (into seen (owner (first sen)))]
                              (if (> (count seen') 1) (reduced seen') seen'))
                            seen))
                        seen))
                    #{}
                    (reads/as-stored-with-arg (:index kb) 1 term)))
     1))

(defn- member-owners
  "`type -> #{metatype member}` over the members' spec closures, so one pass over a
  term's memberships says how many distinct members it holds.  Built once per
  declaration rather than per candidate."
  [tax members]
  (reduce (fn [m mem]
            (reduce (fn [m t] (update m t (fnil conj #{}) mem)) m (tax/specs-global tax mem)))
          {} (filter symbol? members)))

(defn- pairable?
  "Could `term` be half of a clash?  True when its argument-1 root holds more than one
  stored fact, over every predicate and either polarity, so it over-approximates."
  [kb term]
  (> (reads/stored-count-with-arg (:index kb) 1 term) 1))

(defn- two-sided-reach
  "The reach of a separation between the type sets `as` and `bs`: the terms holding a
  believed membership below both.  The side with the smaller `extent-size` is enumerated,
  and each of its terms is probed against the other side's closure.  Empty outright when
  either spec closure is empty, as for a separation naming a non-symbol
  (docs/taxonomy.md, \"What a declaration reaches back over\")."
  [kb as bs roots]
  (let [tax (reasoning/taxonomy kb)
        ca  (spec-closure tax as)
        cb  (spec-closure tax bs)]
    (if (or (empty? ca) (empty? cb))
      {:enumerate nil :keep? (constantly false) :roots roots}
      ;; the near side's roots, since `instances-below` closes each root itself and a
      ;; closure would yield a term once per path; the far side's closure, to probe
      (let [[near far] (if (<= (extent-size kb ca) (extent-size kb cb)) [as cb] [bs ca])]
        {:enumerate (instances-below kb near)
         :keep?     #(holds-below? kb far %)
         :roots     roots}))))

(defn- declaration-reach
  "What a believed declaration in the moved region puts back in question, or nil when
  `sen` reaches back over nothing stored:

      {:enumerate <lazy seq of terms>   ; what the instance budget bounds
       :keep?     (fn [term] …)         ; never drops a term the declaration can convict
       :roots     (#{type …} | :all)    ; the type roots a candidate is focused on
       :refutes   <lazy seq of terms>}  ; a cover's refutable terms, unfiltered

  * `(disjoint A B)`: `two-sided-reach`.
  * `(disjoint_metatype M)`, `(partition W P …)`, `(separating W P …)`: below the
    members or parts, kept when below two distinct ones.
  * `(sibling_disjoint C)`: below C, kept when below two distinct specs of C; a
    `genl`-related pair is dropped by the conviction's own `disjoint?`.
  * `(genl A B)`, `(covering W P …)`: below A or the parts, kept by `pairable?`.
  * `(genlCx Sub Super)`: the memberships Sub now sees, kept by `pairable?`, roots
    `:all`.

  `(covering W P …)` and `(partition W P …)` also carry `:refutes`, the terms
  `refutable-terms` names.  Only `declaration-parts` reads it, and it does not
  depend on a separation standing.

  A new `(M T)` member of a disjoint metatype is `metatype-member-reach`."
  [kb sen]
  (let [tax (reasoning/taxonomy kb)
        f   (nm/functor sen)]
    (case f
      disjoint
      (let [[_ a b] sen] (two-sided-reach kb [a] [b] #{a b}))

      disjoint_metatype
      (let [[_ mt]  sen
            members (tax/metatype-members tax mt)
            owner   (member-owners tax members)]
        {:enumerate (instances-below kb members)
         :keep?     #(holds-two-members? kb owner %)
         :roots     (set members)})

      sibling_disjoint
      (let [[_ c]   sen
            members (disj (tax/specs-global tax c) c)
            owner   (member-owners tax members)]
        {:enumerate (instances-below kb [c])
         :keep?     #(holds-two-members? kb owner %)
         :roots     #{c}})

      genl
      (let [[_ a _] sen]
        {:enumerate (instances-below kb [a])
         :keep?     #(pairable? kb %)
         :roots     #{a}})

      (partition separating)
      (let [parts (distinct (drop 2 sen))
            owner (member-owners tax parts)]
        (cond-> {:enumerate (instances-below kb parts)
                 :keep?     #(holds-two-members? kb owner %)
                 :roots     (set parts)}
          (= 'partition f) (assoc :refutes (refutable-terms kb parts))))

      covering
      (let [parts (distinct (drop 2 sen))]
        {:enumerate (instances-below kb parts)
         :keep?     #(pairable? kb %)
         :roots     (set parts)
         :refutes   (refutable-terms kb parts)})

      genlCx
      (let [[_ sub _] sen]
        {:enumerate (members-in-ancestors kb sub)
         :keep?     #(pairable? kb %)
         :roots     :all})

      nil)))

(defn- metatype-member-reach
  "The reach of `(M T)` for a disjoint metatype `M`: the two-sided reach between `T` and
  `M`'s other members.  Separate from `declaration-reach` because the sentence is an
  ordinary membership, and only the taxonomy says it declares anything."
  [kb mt t]
  (two-sided-reach kb [t] (disj (set (tax/metatype-members (reasoning/taxonomy kb) mt)) t) #{t}))

;; ---- definitional clashes as nogoods -------------------------------------
;;
;; Disjointness, functionality, asymmetry and anti-transitivity clashes, found by re-running
;; the definitional checks over the settle's region and what a declaration in it implicates,
;; and arbitrated as nogoods (docs/nmtms.md, "How a settle finds the clashes").  The rosters
;; are read off `predicates` (docs/predicates.md).

(def ^:private definitional-marks
  "The arbitrable tuple marks that store under a taxonomy prop, as `[functor prop-keyword]`
  pairs: `(pr/prop-marks :arbitrable)`.  The declaration states the keyword, since case
  conversion gets `anti_transitive` wrong (`:anti-transitive`).  `functionalInArg` has no
  prop keyword and is out; a reader that wants it unions `tax/functional-in-arg-predicates`
  (docs/predicates.md).  Only `clash-vocabulary` reads the order, and it compares the
  result against itself."
  (pr/prop-marks :arbitrable))

(def ^:private definitional-mark-symbols
  "`definitional-marks`' declaration functors, as a set."
  (into #{} (map first) definitional-marks))

(def ^:private definitional-mark-keywords
  "`definitional-marks`' taxonomy prop keywords, as a set: what a stored mark's key or a
  violation's `:type` is compared against."
  (into #{} (map second) definitional-marks))

(def ^:private clash-declaration-kinds
  "Each `pr/sweep-kinds` kind → the set of functors whose declaration carries it
  (`pr/sweeps`).  `:type-separating` implicates the memberships of the terms a declaration
  separates, `:predicate-marked` the facts beneath the predicate a mark stands over, and
  `:both` (`genl` alone) both.  Throws `:bad-table-entry` at load when the grouped kinds
  differ from `pr/sweep-kinds`, or when a `definitional-marks` functor carries no
  `:predicate-marked` sweep (docs/predicates.md)."
  (let [by-kind (reduce (fn [m [f kind]] (update m kind (fnil conj #{}) f))
                        {} (pr/sweeps))]
    (when-not (= (set (keys by-kind)) pr/sweep-kinds)
      (throw (ex-info (str "the clash-declaration kinds and the reaches do not match: "
                           (pr-str (set (keys by-kind))) " against the declared "
                           (pr-str pr/sweep-kinds)
                           " — every kind a declaration carries needs an arm in"
                           " declaration-reach, and a kind with no declaration reaches"
                           " nothing")
                      {:type :bad-table-entry :mismatch :reach
                       :grouped  (set (keys by-kind))
                       :declared pr/sweep-kinds})))
    (when-not (set/subset? definitional-mark-symbols (:predicate-marked by-kind))
      (throw (ex-info (str "a definitional mark does not sweep what it convicts: "
                           (pr-str (set/difference definitional-mark-symbols
                                                   (:predicate-marked by-kind)))
                           " pairs a prop keyword in definitional-marks and carries no"
                           " :predicate-marked sweep, so it would convict at the entry point and"
                           " reach nothing stored before it")
                      {:type :bad-table-entry :mismatch :reach
                       :missing (set/difference definitional-mark-symbols
                                                (:predicate-marked by-kind))})))
    by-kind))

(def ^:private clash-declaration-functors
  "Sentence functors whose arrival implicates content already stored: every functor of
  `clash-declaration-kinds`.  A membership or a relation fact is its own candidate and
  needs no entry.  Joining this set does not join `special`'s merge lane
  (`functional-family-declaration`)."
  (into #{} cat (vals clash-declaration-kinds)))

(def ^:private clash-declaration-kind
  "Functor → its `clash-declaration-kinds` key, or nil: the roster inverted at load."
  (into {} (for [[kind functors] clash-declaration-kinds, f functors] [f kind])))

(defn- metatype-member?
  "Is `sen` a unary membership `(M T)` whose functor `M` the taxonomy holds as a disjoint
  metatype?  Such a sentence separates `T` from every member of `M` already there.  Only
  the taxonomy identifies it, so it is tested here rather than listed in
  `clash-declaration-functors`."
  [kb sen]
  (and (sequential? sen)
       (= 2 (count sen))
       (let [f (nm/functor sen)]
         (and (symbol? f) (symbol? (second sen))
              (tax/disjoint-metatype? (reasoning/taxonomy kb) f)))))

(defn- membership-sentexes
  "The believed unary-membership sentexes of `term` — its candidate side of a
  disjointness pair.  Read off the argument root, so it is one posting per term."
  [kb term]
  (filter #(= 2 (count (:sentence %))) (believed-at-arg1 kb term)))

(defn- clash-marked-below
  "Every predicate at or below a `definitional-marks` mark or a `functionalInArg` mark, as
  one set: `tax/specs-of-all` over the marked roster.  A mark is read down the hierarchy,
  as the checks read it: `(functional parentOf)` convicts two `fatherOf` fillers.
  docs/taxonomy.md has why the walk starts from the marks."
  [tax]
  (tax/specs-of-all tax (into (tax/functional-in-arg-predicates tax)
                              (mapcat #(tax/props tax %))
                              definitional-mark-keywords)))

(def ^:dynamic *clash-marked-below*
  "A `delay` over `clash-marked-below` for the pass in flight, or nil.  `constraint-nogoods`
  binds it.  The taxonomy does not move within a pass, so one answer serves every asker."
  nil)

(defn- marks-above?
  "Is any `definitional-marks` or `functionalInArg` mark at or above predicate `f`?  Reads
  `*clash-marked-below*`, or builds a delay of its own when that is unbound."
  [tax f]
  (contains? @(or *clash-marked-below* (delay (clash-marked-below tax))) f))

(defn- predicate-sentexes
  "The believed positive facts of predicate `pred`, off its functor posting in posting
  order; nil for a non-symbol.  Every caller folds it over a `predicate-subtree`, so a
  budget cuts within one predicate in handle order, the residual
  `tax/*exposure-instance-budget*` describes."
  [kb pred]
  (when (symbol? pred)
    (for [s     (keep #(p/get-sentex (:records kb) %)
                      (filter #(jtms/in? (reasoning/tms kb) %)
                              (reads/as-stored-with-functor (:index kb) pred)))
          :when (not (sx/negative? s))]
      s)))

(defn- predicate-subtree
  "The predicates at or below `pred` (`tax/specs-global`, which includes `pred`) that hold
  stored facts, as a sorted set.  Filtered by index cardinality, so a predicate with no
  facts costs one count.  Sorted, so which predicates a budgeted sweep reaches is a
  function of the vocabulary.  `report-arity-reach!` reads the same subtree, since a
  length and a mark descend the same edge."
  [kb pred]
  (into (sorted-set)
        (comp (filter symbol?)
              (filter #(pos? (reads/stored-count-with-functor (:index kb) %))))
        (when (symbol? pred) (tax/specs-global (reasoning/taxonomy kb) pred))))

(defn- subtree-facts
  "The believed facts of `pred` and of every predicate beneath it: what a mark reaching
  `pred` implicates, whether a declaration naming `pred` or a `(genl pred super)` edge
  under a marked `super` carried it there.  Lazy, for the budgeted caller."
  [kb pred]
  (mapcat #(predicate-sentexes kb %) (predicate-subtree kb pred)))

(defn- marked-at-final-arg?
  "Does some `functionalInArg` mark reaching `f` sit at position `k`, the last argument of
  an arity-`k` tuple?  The determinant is then empty (arity 1) or composite (above arity
  2), which no single argument root narrows, so the callers send the candidate to an
  extent sweep.  At arity 2 they read the argument root instead.  A mark on a position
  other than the last is not asked about (docs/taxonomy.md, `functionalInArg`)."
  [tax f k]
  (boolean (some #(= k (second %)) (tax/functional-in-arg-over tax f))))

(defn- constraint-facts-in-ancestors
  "The believed facts in the ancestor set of context `sub` whose predicate a tuple mark
  reaches: binary facts under `marks-above?`, and facts of any arity under
  `marked-at-final-arg?`.  These are the candidates a `(genlCx sub super)` edge newly puts
  in joint sight.  The tuple-mark counterpart of `members-in-ancestors`, and lazy for the
  same budgeted caller.

  **Read from the smaller side.**  Every fact a tuple mark reaches has a functor in
  `clash-marked-below`, so the candidates are those functors' believed facts that sit in
  the ancestor set as well as the ancestor set's believed facts under a mark — one set
  read two ways.  An edge into a corpus context has the corpus for its ancestor set, and
  the marked predicates hold a few of its facts, so the side is chosen by the two stored
  counts.  Belief is asked of the handle before a record is paged, as
  `believed-in-ancestors` asks it.  Which prefix a budget cut takes follows the side read,
  the residual `tax/*exposure-instance-budget*` describes."
  [kb sub]
  (let [tax     (reasoning/taxonomy kb)
        idx     (:index kb)
        cs      (filterv symbol? (tax/context-up tax sub))
        fs      (filterv #(pos? (reads/stored-count-with-functor idx %))
                         @(or *clash-marked-below* (delay (clash-marked-below tax))))
        marked? (fn [sen]
                  (and (sequential? sen)
                       (let [f (nm/functor sen)
                             k (count (nm/args sen))]
                         (and (symbol? f)
                              (or (and (= 2 k) (marks-above? tax f))
                                  (marked-at-final-arg? tax f k))))))]
    (if (< (transduce (map #(reads/stored-count-with-functor idx %)) + 0 fs)
           (transduce (map #(reads/stored-count-in-context idx %)) + 0 cs))
      (let [in-set? (set cs)
            tms     (reasoning/tms kb)]
        (for [f     fs
              s     (keep #(p/get-sentex (:records kb) %)
                          (filter #(jtms/in? tms %) (reads/as-stored-with-functor idx f)))
              :when (and (contains? in-set? (:context s))
                         (not (sx/negative? s))
                         (marked? (:sentence s)))]
          s))
      (for [s     (believed-in-ancestors kb cs)
            :when (marked? (:sentence s))]
        s))))

(defn- separations?
  "Does the KB separate any two types, by a `disjoint` pair, a disjoint metatype, a
  `sibling_disjoint` parent or a `partition`/`separating` cover?  Four set-emptiness reads
  and no walk.  The covers are read because `separation-frame` reads them
  (docs/taxonomy.md)."
  [tax]
  (boolean (or (seq (tax/disjoint-pairs tax))
               (seq (tax/disjoint-metatypes tax))
               (seq (tax/sibling-disjoints tax))
               (seq (tax/separating-covers tax)))))

(defn- membership-part
  "A reach `{:enumerate :keep?}` over terms as a sweep part: the terms the budget takes,
  filtered by `keep?`, emit their `membership-sentexes`."
  [kb {:keys [enumerate keep?]}]
  {:enumerate enumerate
   :emit      (fn [terms] (mapcat #(membership-sentexes kb %) (filter keep? terms)))})

(defn- fact-part
  "A lazy enumeration of candidate sentexes as a sweep part, emitting what it takes."
  [xs]
  {:enumerate xs :emit identity})

(defn- declaration-parts
  "The sweep parts through which a believed declaration `sen` puts stored sentexes back
  in question, as a vector of `{:enumerate lazy-seq :emit fn}` (`take-parts`):

  - a type-separating declaration: the memberships `declaration-reach` names, plus for
    a cover the memberships of its `:refutes` terms.  A `genlCx` edge adds `constraint-facts-in-ancestors` of its sub;
  - a `definitional-marks` or `functionalInArg` declaration: `subtree-facts` of the
    predicate it names;
  - `(genl sub super)`: both, the predicate half only while a mark stands at or above
    `sub`;
  - `(M T)` joining a disjoint metatype: `metatype-member-reach`.

  Empty when `sen` implicates nothing."
  [kb sen]
  (let [[f a] sen
        tax (reasoning/taxonomy kb)
        ;; a KB separating no two types convicts no membership by disjointness, so a
        ;; `genl` edge there skips the enumeration; a cover's refutable terms are read
        ;; either way
        implicated (fn [{:keys [refutes] :as reach}]
                     (cond-> (if (separations? tax) [(membership-part kb reach)] [])
                       refutes (conj (membership-part kb {:enumerate refutes
                                                          :keep?     (constantly true)}))))]
    (case (clash-declaration-kind f)
      :type-separating
      (cond-> (implicated (declaration-reach kb sen))
        (= 'genlCx f) (conj (fact-part (constraint-facts-in-ancestors kb a))))

      :predicate-marked
      [(fact-part (subtree-facts kb a))]

      :both
      (cond-> (implicated (declaration-reach kb sen))
        (marks-above? tax a) (conj (fact-part (subtree-facts kb a))))

      ;; no kind: only `(M T)` joining a disjoint metatype implicates anything
      (if (metatype-member? kb sen)
        (implicated (metatype-member-reach kb f a))
        []))))

(defn- take-parts
  "Spend the volatile budget `left` over `parts` in order, as `[sentexes unread]`: what
  the taken prefixes emit, and the parts whose enumeration the budget cut, each holding
  its unread tail as `:enumerate`.  `unread` is empty exactly when every part was read to
  its end.  The tail is the same lazy seq past the prefix, so resuming it re-reads no
  element (docs/taxonomy.md, \"What a declaration reaches back over\")."
  [left parts]
  (reduce (fn [[out unread] {:keys [enumerate emit] :as part}]
            (let [[taken cut?] (take-budgeted left enumerate)]
              [(into out (emit taken))
               (cond-> unread
                 cut? (conj (assoc part :enumerate (nthrest enumerate (count taken)))))]))
          [[] []]
          parts))

(defn- content-order
  "`sentexes` sorted by `[sentence context]` under `nm/compare-form`.  The triggers of every
  budgeted sweep are walked in this order, so which members one budget reaches does not
  depend on the handle order the region arrived in.  A sort for determinism, so it is
  given the triggers alone and never a region: a region can be the whole store, and the
  sort is n·log n structural comparisons over it.  Structural, so no string is built per
  comparison and `*print-length*` cannot merge two keys."
  [sentexes]
  (nm/sort-by-content-key (juxt :sentence :context) sentexes))

(defn- region-holds-store?
  "Do the handle sets name every sentex the store holds, as at least the store's sentex
  count of distinct handles that resolve to a stored record?  Handles are counted rather
  than the believed region, which leaves out a stored denial or an OUT sentex
  (docs/nmtms.md, \"Which entry point the content came through\").  Records are fetched
  only when the handle count reaches the store's."
  [kb & handle-sets]
  (let [recs (:records kb)
        n    (cap/count-sentexes recs)]
    (and (>= (reduce + 0 (map count handle-sets)) n)
         (>= (count (into #{} (comp cat (filter #(p/get-sentex recs %))) handle-sets)) n))))

(def ^:dynamic *arbitration-cut*
  "A volatile collecting the declarations whose retroactive arbitration sweep the instance
  budget cut short, or nil, which records nothing.  Bound for the whole settle, since
  `constraint-nogoods` sweeps once per pass; `report-arbitration-cut!` files one
  `:arbitration-truncated` entry from it."
  nil)

(defn- note-arbitration-cut!
  "Record `sen` as a declaration whose implicated content this settle did not finish
  examining — cut short mid-reach, or reached after the budget was already spent."
  [sen]
  (when-let [sink *arbitration-cut*] (vswap! sink conj sen)))

(defn- rearm-reach
  "The reach a departed sibling-disjointness exception pair `#{x y}` (posted to
  `:sib-exc-dirty` by a retract) re-arms: `two-sided-reach` below both sides, plus
  `:trigger`, the `(siblingDisjointException x y)` a cut notice names.  A pair the
  exception spared ab initio never entered `:clashes`, so this is the one route that
  re-arms it."
  [kb pr]
  (let [[x y] (sort nm/compare-form pr)]
    (assoc (two-sided-reach kb [x] [y] pr) :trigger (list 'siblingDisjointException x y))))

(defn- rearm-order
  "The exception pairs `pairs` in content order."
  [pairs]
  (sort-by #(vec (sort nm/compare-form %)) pairs))

(def ^:dynamic *arbitration-progress*
  "A volatile `clash-candidates` sets, every pass, to the sweeps the pass left unfinished
  as `{key [part …]}`: a trigger's handle or a re-armed pair `#{x y}`, to the parts
  `take-parts` left unread.  nil until a pass sweeps, and unbound outside a settle.
  `settle*` binds it; `carry-arbitration-sweeps!` hands the last pass's value to the next
  settle."
  nil)

(defn- carried-sweeps
  "The sweeps named by `ks`, keys of `:clashes`' `:pending`, as `[key trigger parts]`:
  triggers believed now in content order, then re-armed pairs in content order.  Each
  resumes from its unread tail in `:arbitration-cursors`, or from the start of its reach
  when the KB holds no tail for it, as after an image install.  A trigger no longer
  stored or believed is dropped."
  [kb ks]
  (let [cursors @(reasoning/arbitration-cursors kb)
        tms     (reasoning/tms kb)
        decls   (content-order
                 (into [] (comp (filter integer?)
                                (filter #(jtms/in? tms %))
                                (keep #(p/get-sentex (:records kb) %)))
                       ks))]
    (concat
     (for [s decls]
       [(:id s) (:sentence s) (or (get cursors (:id s)) (declaration-parts kb (:sentence s)))])
     (for [pr (rearm-order (filter set? ks))
           :let [r (rearm-reach kb pr)]]
       [pr (:trigger r) (or (get cursors pr) [(membership-part kb r)])]))))

(defn- clash-candidates
  "The believed positive sentexes whose definitional checks this settle re-runs, as a set:

  - the region `touched`, and `revisit`, the handles of known pairs `clash-nogoods`
    re-derives;
  - the memberships of each term a denial in `touched` denies a cover's part of;
  - what each declaration in the region implicates (`declaration-parts`), under either
    constraint policy;
  - the memberships a retracted sibling-disjointness exception re-arms (`rearm-reach`);
  - the rest of the sweeps an earlier settle's budget cut (`carried-sweeps`), except
    those the region restarts.

  The sweeps share one `*exposure-instance-budget*` in that order, walk their triggers in
  content order, record a cut trigger in `*arbitration-cut*` and set
  `*arbitration-progress*` to the sweeps left unfinished.  They are skipped when the region
  holds the whole store: under `*whole-store-region?*` with `touched` at least the store's
  size, or by `region-holds-store?`, asked only when there is a sweep to run
  (docs/nmtms.md, \"Which entry point the content came through\").  They run
  under `*rebuilding?*` too, since `recover`'s second settle runs under it over part of
  the store."
  [kb touched revisit]
  (let [believed  (believed-xf kb)
        tally     (fn [] (cap/count-sentexes (:records kb)))
        ;; inside a recover the region holds only stored handles
        recovered? (and *whole-store-region?* (>= (count touched) (tally)))
        ;; `touched` drops what `revisit` names, so a declaration in both does not spend the
        ;; shared budget twice
        firsts (into [] believed revisit)
        others (into [] believed (remove revisit touched))
        region (into (set firsts) others)
        ;; `believed-xf` drops a denial, so a moved denial of a cover's part puts its
        ;; term's memberships in the candidates instead, unbudgeted as a membership in the
        ;; region is
        tax    (reasoning/taxonomy kb)
        denied (when (and (not recovered?) (seq (tax/coverings tax)))
                 (into []
                       (comp (filter #(jtms/in? (reasoning/tms kb) %))
                             (keep #(p/get-sentex (:records kb) %))
                             (keep denial-of)
                             (filter (fn [[p _]] (seq (tax/covers-naming tax p))))
                             (map second)
                             (distinct)
                             (mapcat #(membership-sentexes kb %)))
                       touched))
        dirty  (when-not recovered? @(reasoning/sib-exc-dirty kb))
        ;; named ahead of the sweep, so the store is tallied only when there is one.  In
        ;; content order, the revisited ones first: a filter of a sorted run is the sort of
        ;; the filtered one, so this is the order sorting the region gave, for the triggers'
        ;; count of comparisons
        trigger? (fn [s]
                   (let [sen (:sentence s)]
                     (and (sequential? sen)
                          (or (contains? clash-declaration-functors (nm/functor sen))
                              (metatype-member? kb sen)))))
        triggers (when-not recovered?
                   (into (vec (content-order (filterv trigger? firsts)))
                         (content-order (filterv trigger? others))))
        pending  (when-not recovered? (:pending @(reasoning/clashes kb)))
        covers-store? (or recovered?
                          (and (or (seq triggers) (seq dirty) (seq pending))
                               (region-holds-store? kb touched revisit)))
        left  (volatile! (long *exposure-instance-budget*))
        ;; `[key trigger parts]` per sweep
        sweeps (when-not covers-store?
                 (concat (for [s triggers]
                           [(:id s) (:sentence s) (declaration-parts kb (:sentence s))])
                         (for [pr (rearm-order dirty)
                               :let [r (rearm-reach kb pr)]]
                           [pr (:trigger r) [(membership-part kb r)]])
                         (carried-sweeps kb (remove (into (set dirty) (map :id) triggers)
                                                    pending))))
        ;; a trigger reached after the budget is spent is asked too: `take-budgeted`
        ;; probes past the cap, so an empty reach is not filed as cut
        swept (mapv (fn [[k trigger parts]]
                      (let [[ss unread] (take-parts left parts)]
                        (when (seq unread) (note-arbitration-cut! trigger))
                        [k ss unread]))
                    sweeps)
        tms   (reasoning/tms kb)]
    (when-let [p *arbitration-progress*]
      (vreset! p (into {} (keep (fn [[k _ unread]] (when (seq unread) [k unread]))) swept)))
    ;; a resumed tail holds elements realized in an earlier settle, so belief is re-read
    (-> region
        (into denied)
        (into (comp (mapcat second) (filter #(jtms/in? tms (:id %)))) swept))))

(def ^:dynamic *incremental-clashes*
  "True, the default: `clash-nogoods` examines the region and the known pairs, gates on
  `could-clash?` and carries unmoved pairs.  Bound false, every believed sentex is a
  candidate every settle and nothing is carried: the exhaustive reference
  `clash_oracle_test` compares against, at O(believed) checks per settle."
  true)

(defn- all-believed
  "Every believed, positive, stored sentex — the exhaustive candidate set
  `*incremental-clashes*` false substitutes for the region."
  [kb]
  (into [] (comp (keep #(p/get-sentex (:records kb) %))
                 (filter #(not (sx/negative? %))))
        (jtms/in-datums (reasoning/tms kb))))

(defn- clash-vocabulary
  "The declarations a clash depends on beyond its members and the `genl` closure, as one
  vector value `clash-nogoods` compares whole: the `disjoint` pairs, the disjoint
  metatypes and each one's members, the `sibling_disjoint` parents, the separating and the
  covering covers, the sibling-disjointness exceptions, one prop set per
  `definitional-marks` mark, the `functionalInArg` table, and the `genlCx` generation.
  Each part is sized by the declarations and not by the KB (docs/nmtms.md, \"How a settle
  finds the clashes\")."
  [tax]
  [(tax/disjoint-pairs tax)
   (tax/disjoint-metatypes tax)
   (into {} (map (juxt identity #(tax/metatype-members tax %)))
         (tax/disjoint-metatypes tax))
   (tax/sibling-disjoints tax)
   (tax/separating-covers tax)
   (tax/coverings tax)
   (tax/sib-exceptions tax)
   (mapv #(tax/props tax (second %)) definitional-marks)
   (tax/functional-in-arg-table tax)
   (tax/relation-gen tax :genlCx)])

(defn- genl-view-keys
  "The `[functor context]` key of each member of the known pair `pr` (handles), or nil when
  a member is not a stored unary membership with a symbol functor.  A membership pair is
  decided by `tax/disjoint?` of its two functors, so the `genl` edges among each
  functor's supertypes are all a `genl` edge can move.  Any other shape answers nil and
  re-derives."
  [recs pr]
  (reduce (fn [acc h]
            (if-let [sx (p/get-sentex recs h)]
              (let [sen (:sentence sx)]
                (if (and (sequential? sen) (= 1 (nm/arity sen)) (symbol? (nm/functor sen)))
                  (conj acc [(nm/functor sen) (:context sx)])
                  (reduced nil)))
              (reduced nil)))
          #{} pr))

(def ^:private scoped-reading
  "`genl-view`'s answer where a member's context sees less of the `genl` relation than the
  KB holds.  `clash-nogoods` re-derives a pair holding one."
  ::scoped)

(defn- genl-view
  "Each supertype of `t` mapped to its direct `genl` parents — the edges out of `t`'s
  global up-closure — when context `ctx` sees every one of those edges, else
  `scoped-reading` (docs/nmtms.md, \"How a settle finds the clashes\").

  A membership pair is decided by `tax/disjoint?` of its two functors, which reads their
  supertypes and nothing past them, so the edges out of that set are all a `genl` edge can
  move for the pair: one out of a supertype changes this map, and no other can.  The edges
  rather than each supertype's own closure, which is a closure per supertype per key on a
  deep hierarchy, and changes on no edge this map misses.  A context that cannot see one
  of the edges reads `scoped-reading` even where another path reaches the same types —
  the pair is re-derived, which costs a check and moves no answer.  A scoped parent set
  is a subset of the global one, so equal counts are equal sets."
  [tax [t ctx]]
  (let [view (into {} (map (fn [s] [s (tax/direct-genls tax s nil)]))
                   (tax/genls-global tax t))]
    (if (every? (fn [[s ps]] (= (count ps) (count (tax/direct-genls tax s ctx)))) view)
      view
      scoped-reading)))

(defn- could-clash?
  "Could believed sentex `s` be one member of a definitional clash?  An over-approximating
  gate in front of `checks/arbitrable-violations`, answered without a record fetch.  True
  for:

  - a unary membership `(T x)`, `x` a symbol whose argument-1 root holds more than one
    stored sentex;
  - a binary fact under `marks-above?`;
  - a fact of any arity with a `functionalInArg` mark at its last argument
    (`marked-at-final-arg?`)."
  [kb s]
  (let [sen (:sentence s)]
    (and (sequential? sen)
         (symbol? (nm/functor sen))
         (let [as  (rest sen)
               f   (nm/functor sen)
               tax (reasoning/taxonomy kb)
               k   (count as)]
           (or (case k
                 1 (let [x (first as)]
                     (and (symbol? x) (> (reads/stored-count-with-arg (:index kb) 1 x) 1)))
                 2 (marks-above? tax f)
                 false)
               (marked-at-final-arg? tax f k))))))

(def ^:dynamic *partner-cut*
  "A volatile collecting the `partner-contexts` extent sweeps cut short this settle, or nil.
  `settle*` binds it for the settle and `report-partner-cut!` files
  `:partner-sweep-truncated` from it.  The assert entry point leaves it nil, and a cut
  there records nothing."
  nil)

(defn- note-partner-cut!
  "Record that a `partner-contexts` sweep for `[pred arity]` stopped at `budget`.  The sink
  is a set, so a cap hit once per candidate records one entry."
  [pred arity budget]
  (when-some [v *partner-cut*]
    (vswap! v conj {:pred pred :arity arity :budget budget})))

(defn- denial-contexts
  "The contexts of the believed denials `(not (p x))` with `p` a part of a cover over `t`
  or a supertype of `t`, read globally: where the other members of a cover refutation of
  `(t x)` are held.  Empty, with no posting read, when no cover is over `t`."
  [kb t x]
  (let [tax   (reasoning/taxonomy kb)
        parts (when (and (symbol? t) (symbol? x) (seq (tax/coverings tax)))
                (into #{} (mapcat second) (tax/covers-over tax t nil)))]
    (if (empty? parts)
      #{}
      (into #{}
            (comp (filter #(jtms/in? (reasoning/tms kb) %))
                  (keep #(p/get-sentex (:records kb) %))
                  (filter #(contains? parts (first (denial-of %))))
                  (map :context))
            (reads/as-stored-with-arg (:index kb) 1 x)))))

(defn- partner-contexts
  "The contexts holding a believed sentex, other than `s`, that could be the other member
  of a clash with `s`, as a set.  Over-approximating: a context that convicts nothing
  costs one check.

  - a membership: the contexts of its term's other memberships, and of its term's denials
    of a part of a cover over its type (`denial-contexts`);
  - a binary fact: the argument-root postings the marks at or above its functor select,
    kept to predicates under those marks.  `functional` and `(functionalInArg P 2)` read
    argument 1's term at position 1, `asymmetric` argument 2's term at position 1,
    `(functionalInArg P 1)` argument 2's term at position 2, and `anti_transitive` both
    terms at both positions;
  - a `functionalInArg` mark at the last position of an arity-1 or above-2 tuple:
    `subtree-facts` of the marked predicate, capped at `tax/*exposure-instance-budget*`,
    a cut noted through `note-partner-cut!`."
  [kb s]
  (let [sen (:sentence s)
        as  (vec (nm/args sen))
        own (:id s)
        f   (nm/functor sen)
        tax (reasoning/taxonomy kb)
        k   (count as)
        ;; the empty and composite `functionalInArg` determinants: an extent sweep, capped
        ;; locally because no settle-wide budget reaches this fn at the entry point
        det-budget (max 0 (long tax/*exposure-instance-budget*))
        det-facts  (into [] (take (inc det-budget))
                         (mapcat #(subtree-facts kb (first %))
                                 (filter #(and (= k (second %)) (not= 2 k))
                                         (tax/functional-in-arg-over tax f))))
        _          (when (> (count det-facts) det-budget)
                     (note-partner-cut! f k det-budget))
        swept-det (into #{}
                        (comp (take det-budget)
                              (remove #(= own (:id %))) (map :context))
                        det-facts)]
    (into swept-det
          (case k
            1 (into (denial-contexts kb f (first as))
                    (comp (remove #(= own (:id %))) (map :context))
                    (membership-sentexes kb (first as)))
            2 (let [;; each mark reads only the postings its partner can sit in: on a term
                    ;; shared across an extent another posting is the extent (`perf`'s
                    ;; `constraint-exposure-shared-arg`)
                    fun    (tax/props-over tax :functional f)
                    asym   (tax/props-over tax :asymmetric f)
                    anti   (tax/props-over tax :anti-transitive f)
                    inarg  (tax/functional-in-arg-over tax f)
                    at-pos (fn [n] (into [] (comp (filter #(= n (second %))) (map first))
                                         inarg))
                    fnarg2 (at-pos 2)
                    fnarg1 (at-pos 1)
                    marks (-> (set fun) (into asym) (into anti)
                              (into fnarg2) (into fnarg1))
                    srcs (distinct
                          (cond-> []
                            (seq fun)    (conj [1 (first as)])
                            (seq asym)   (conj [1 (second as)])
                            (seq fnarg2) (conj [1 (first as)])
                            (seq fnarg1) (conj [2 (second as)])
                            (seq anti)   (into [[1 (first as)]  [2 (first as)]
                                                [1 (second as)] [2 (second as)]])))
                    ;; a partner may sit under a sub-predicate of the mark: under
                    ;; `(functional parentOf)`, `motherOf` partners `fatherOf`
                    partner? (fn [p]
                               (let [g (nm/functor (:sentence p))]
                                 (or (= f g)
                                     (and (symbol? g)
                                          (boolean (some #(tax/genl?-global tax g %) marks))))))]
                (into #{} (comp (mapcat (fn [[pos t]] (believed-at-arg kb pos t)))
                                (remove #(= own (:id %)))
                                (filter partner?)
                                (map :context))
                      srcs))
            #{}))))

(defn- chain-contexts
  "The pairs of contexts other than `s`'s own, each a set, holding the other two steps of
  an `anti_transitive` chain `s` is a step of.  A vantage must see all three steps
  (docs/nmtms.md, \"A defeat is scoped to its vantage\").  For each of the three places
  `s` takes in a chain, two argument postings are joined on the term the steps share.  A
  step is a binary tuple under an `anti_transitive` mark at or above `s`'s functor.
  Empty unless such a mark stands."
  [kb s]
  (let [sen  (:sentence s)
        f    (nm/functor sen)
        as   (vec (nm/args sen))
        tax  (reasoning/taxonomy kb)
        anti (when (and (symbol? f) (= 2 (count as)))
               (tax/props-over tax :anti-transitive f))]
    (if (empty? anti)
      #{}
      (let [c     (:context s)
            [a b] as
            step? (fn [p]
                    (let [psen (:sentence p)
                          g    (nm/functor psen)]
                      (and (not= (:id s) (:id p))
                           (= 2 (count (nm/args psen)))
                           (or (= f g)
                               (and (symbol? g)
                                    (boolean (some #(tax/genl?-global tax g %) anti)))))))
            ;; the steps posted on `t` at `pos`, keyed on the term at position `n`
            by    (fn [pos t n]
                    (group-by #(nth (:sentence %) n)
                              (filter step? (believed-at-arg kb pos t))))
            join  (fn [xs ys]
                    (for [[t ps] xs, p ps, q (get ys t)
                          :let  [g (disj (hash-set (:context p) (:context q)) c)]
                          :when (= 2 (count g))]
                      g))]
        (into #{}
              (concat (join (by 1 a 2) (by 2 b 1))
                      (join (by 1 b 2) (by 1 a 2))
                      (join (by 2 a 1) (by 2 b 1))))))))

(defn- ground-reading
  "`(fn [g k])` → what reader `k` (nil: the whole KB) sees of the grounds `s` could clash
  on, `g` being the contexts holding the other members.  For a membership, the types held
  of its term in `g` that `k` proves disjoint from `s`'s type; for a relation fact, the
  marks `k` sees above its predicate, per kind, independent of `g`.  Read off the
  taxonomy's cached closures; no check runs.  Two readers with equal readings convict `s`
  on the same grounds."
  [kb s]
  (let [tax (reasoning/taxonomy kb)
        sen (:sentence s)
        f   (nm/functor sen)
        as  (nm/args sen)]
    (cond
      (not (and (sequential? sen) (symbol? f)))
      (constantly #{})

      (= 1 (count as))
      (if (and (symbol? (first as)) (separations? tax))
        (let [held (group-by second (believed-memberships kb (first as)))]
          (fn [g k]
            (into #{}
                  (comp (mapcat held)
                        (map first)
                        (remove #(= f %))
                        (filter #(if k (tax/disjoint? tax f % k) (tax/disjoint? tax f %))))
                  g)))
        (constantly #{}))

      :else
      (fn [_ k]
        (into #{(tax/functional-in-arg-over tax f k)}
              (map (fn [kind] [kind (tax/props-over tax kind f k)]))
              definitional-mark-keywords)))))

(defn- readers
  "The common descendants of `cs` whose reading of the grounds can differ from that of
  the maximum above them, beside the maxima `top`: see `group-vantages`."
  [tax cs top]
  (if-let [gs (tax/ground-contexts tax)]
    (into (set top)
          (comp (remove (fn [x] (every? #(tax/sees? tax % x) top)))
                (mapcat #(tax/common-descendants tax (into [%] cs))))
          gs)
    (tax/common-descendants tax cs)))

(defn- group-vantages
  "The vantages beyond `s`'s own context of the clashes `s` could form with members held in
  each of `groups`, a collection of context sets.  Per group: the maximal common
  descendants of `s`'s context and the group's, and the most general context of each
  distinct `ground-reading` among the `readers`.  When every maximum reads what the whole
  KB holds, the common descendants are not enumerated (docs/nmtms.md, \"A defeat is scoped
  to its vantage\").  A group holding only `s`'s context adds nothing."
  [kb s groups]
  (let [tax     (reasoning/taxonomy kb)
        c       (:context s)
        reading (ground-reading kb s)]
    (into #{}
          (comp (map #(disj (set %) c))
                (filter seq)
                (mapcat (fn [g]
                          (let [cs    (into [c] (sort g))
                                top   (tax/maximal-common-descendant-contexts tax cs)
                                read  (memoize #(reading g %))
                                whole (read nil)]
                            (if (every? #(= whole (read %)) top)
                              top
                              (into top
                                    (mapcat #(tax/maximal-contexts tax (val %)))
                                    (group-by read (readers tax cs top)))))))
                (remove #(= c %)))
          groups)))

(defn- clash-vantages
  "The contexts `s`'s definitional question is asked from beyond its own: `group-vantages`
  over the partner contexts and the chain-step context pairs.  Each vantage sees every
  member and the grounds, and convicts on what it sees (docs/nmtms.md, \"Who asks the
  pair's question\").  A converse read by argument preservation is `preserving-nogoods`'
  case and not a partner here."
  [kb s]
  (group-vantages kb s (into (chain-contexts kb s)
                             (map hash-set)
                             (partner-contexts kb s))))

(defn- clash-askers
  "`s`'s own context, then its `clash-vantages` sorted, under both constraint policies
  (docs/nmtms.md, \"Who asks the pair's question\").  Entries are keyed on the handle set,
  so the order decides nothing; it is sorted so it is not arrival order."
  [kb s]
  (cons (:context s)
        ;; vantages are contexts (symbols), so `compare-form` reduces to `compare` — a
        ;; bare sort gives the same order with no per-comparison form-rank dispatch
        (sort (clash-vantages kb s))))

(defn- clash-dirty
  "The handles a settle adds to `clash-nogoods`' region, which a spelling's belief or
  reading can move through with no relabel: the `:dirty` handles of the `:clashes` memo
  `prev` (`note-supersession-flips!`), and every stored sentex naming a term of
  `tax/take-equality-moves!`.  A merge or un-merge changes which spellings a reader
  retires (`res/without-retired`), which the checks read, so it can make or unmake a pair
  whose members are neither relabelled nor superseded (docs/nmtms.md, \"How a settle
  finds the clashes\")."
  [kb prev]
  (let [moved (tax/take-equality-moves! (reasoning/taxonomy kb) :clashes)]
    (cond-> (set (:dirty prev))
      moved (into (mapcat #(reads/as-stored-with-term (:index kb) %)) moved))))

(defn- clash-nogoods
  "The definitional clashes among this settle's candidates, as nogood maps
  `{:nogood :vantages :kind :priority :sentence}`.  Resets `kb`'s `:clashes` memo to the
  new answer.

  A candidate passing `could-clash?` is asked `checks/arbitrable-violations`, the check
  the assert entry point runs, from each of its `clash-askers`.  A member moved when
  `touched` or `clash-dirty` holds it.  A known pair is carried unless a member moved,
  `clash-vocabulary` moved, or a `genl` edge moved and the pair's `genl-view` reading
  moved.  A pair read clean while a scoped defeat stands is kept and
  asked again by the next call, since the settle re-decides the scoped defeats.  There is
  one entry per handle set, with `:sentence` and `:kind` chosen by content.  `:priority`
  is 2 plus the highest defeat-class rank among the members, the 3–4 range above every
  rebuttal
  (docs/nmtms.md, \"How a settle finds the clashes\")."
  [kb touched]
  (let [tms   (reasoning/tms kb)
        recs  (:records kb)
        tax   (reasoning/taxonomy kb)
        vocab (clash-vocabulary tax)
        gen   (tax/relation-gen tax :genl)
        prev  @(reasoning/clashes kb)
        dirty (clash-dirty kb prev)
        touched (if (seq dirty) (into (set touched) dirty) touched)
        scoped? (boolean (seq @(reasoning/scoped-defeats kb)))
        stale?  (or (not *incremental-clashes*) (not= vocab (:vocab prev)))
        stored? (fn [pr] (every? #(some? (p/get-sentex recs %)) pr))
        ;; `disj` from the memo's own set, which a settle that retracted nothing returns
        ;; unchanged rather than rebuilds
        live    (reduce (fn [s pr] (if (stored? pr) s (disj s pr))) (:pairs prev #{}) (:pairs prev))
        moved?  (let [t (set touched)] (fn [pr] (boolean (some t pr))))
        ;; `:keys` holds each pair's `genl-view-keys`, `:views` their readings at the last stamp
        gen?    (not= gen (:gen prev))
        keys-of (:keys prev {})
        view-of (memoize (fn [k] (genl-view tax k)))
        views   (:views prev {})
        ;; memoized on the key set, which the pairs of a clash over two types share
        keys-seen? (memoize (fn [ks]
                              (every? (fn [k]
                                        (let [v (view-of k)]
                                          (and (not= scoped-reading v)
                                               (= (get views k ::gone) v))))
                                      ks)))
        seen?   (fn [pr] (if-let [ks (get keys-of pr)] (keys-seen? ks) false))
        revisit (into (cond stale? live
                            gen?   (into #{} (filter (fn [pr] (or (moved? pr) (not (seen? pr))))) live)
                            :else  (into #{} (filter moved?) live))
                      (filter live) (:held prev))
        carried (if stale?
                  {}
                  (reduce-kv (fn [m pr _]
                               (if (and (contains? live pr) (not (contains? revisit pr)))
                                 m
                                 (dissoc m pr)))
                             (:nogoods prev {}) (:nogoods prev {})))
        cands   (let [raw (if *incremental-clashes*
                            (clash-candidates kb touched (into #{} (mapcat identity) revisit))
                            (all-believed kb))]
                  ;; clustered by argument-1 term: `disjoint-problems` re-reads the term's
                  ;; memberships per membership asked, and back-to-back asks hit the record
                  ;; LRU.  The order decides nothing, since entries are keyed on the handle set.
                  (sort-by (fn [s] (let [sen (:sentence s)]
                                     (if (sequential? sen) (hash (first (nm/args sen))) 0)))
                           raw))
        entries
        (mapcat (fn [s]
                  (when (or (not *incremental-clashes*) (could-clash? kb s))
                    (mapcat
                     (fn [asker]
                       (keep (fn [v]
                               ;; a violation opposing only `s` itself weighs nothing
                               ;; (`checks/antitransitivity-problems`)
                               (let [opp (into [] (comp (remove #(= % (:id s)))
                                                        (filter #(jtms/in? tms %))
                                                        (distinct))
                                               (checks/opposing-handles v))]
                                 (when (seq opp)
                                   (let [hs   (into #{(:id s)} opp)
                                         said (->> opp
                                                   (keep #(p/get-sentex (:records kb) %))
                                                   (map :sentence)
                                                   (cons (:sentence s))
                                                   (sort nm/compare-form))]
                                     {:nogood   hs
                                      :vantages #{asker}
                                      :kind     (:type v)
                                      :priority (+ 2 (reduce max (map #(strength/rank-of
                                                                        (jtms/defeat-class tms %))
                                                                      hs)))
                                      :sentence (apply list 'contradicts said)}))))
                             (checks/arbitrable-violations kb (:sentence s) asker
                                                           (:context s))))
                     (clash-askers kb s))))
                cands)]
    ;; one entry per handle set, chosen by content
    (let [derived (into {} (map (fn [[pr es]]
                                  [pr (assoc (first (sort-by (juxt :kind :sentence)
                                                             nm/compare-form es))
                                             :vantages (tax/maximal-contexts
                                                        tax (into #{} (mapcat :vantages) es)))]))
                        (group-by :nogood entries))
          answer  (merge carried derived)
          ngs     (into #{} (vals answer))
          found   (into #{} (keys answer))]
      ;; a pair leaves `:pairs` only when re-derived clean with both members believed and
      ;; no scoped defeat standing, which a clean reading can rest on
      (let [held  (when scoped?
                    (into #{} (filter (fn [pr] (and (not (contains? found pr))
                                                    (every? #(jtms/in? tms %) pr))))
                          live))
            pairs (into (into found held)
                        (filter (fn [pr]
                                  (or (contains? found pr)
                                      (not (every? #(jtms/in? tms %) pr)))))
                        live)
            ;; keys are read off the records only for a pair derived this settle
            [ks fresh]
            (reduce (fn [[m nk] pr]
                      (if (contains? m pr)
                        [m nk]
                        (let [k (genl-view-keys recs pr)]
                          [(assoc m pr k) (if k (into nk k) nk)])))
                    [keys-of #{}] (keys derived))
            ;; the reduce only adds, so an equal count is an equal domain
            ks    (cond-> ks (not= (count ks) (count pairs)) (select-keys pairs))]
        (reset! (reasoning/clashes kb)
                {:vocab   vocab
                 :gen     gen
                 :nogoods answer
                 :pairs   pairs
                 :held    held
                 :keys    ks
                 ;; re-read whole only when the relation moved; else extended by `fresh`
                 :views   (if gen?
                            (into {} (map (fn [k] [k (view-of k)]))
                                  (into #{} (comp (keep identity) cat) (vals ks)))
                            (reduce (fn [m k] (if (contains? m k) m (assoc m k (view-of k))))
                                    views fresh))
                 ;; `carry-arbitration-sweeps!` writes it once per settle, and a pass keeps it
                 :pending (:pending prev)}))
      ngs)))

(defn- tuple-marks?
  "Does any predicate carry a `definitional-marks` mark or a `functionalInArg` mark?  The
  second is read because a KB may declare `functionalInArg` alone.  One set-emptiness read
  per roster entry."
  [tax]
  (boolean (or (some #(seq (tax/props tax %)) definitional-mark-keywords)
               (seq (tax/functional-in-arg-predicates tax)))))

(defn- constraint-nogoods
  "`clash-nogoods` over `region` (the pass's `touched`, as a delay), behind `separations?`,
  `tuple-marks?` and `tax/coverings`: a KB passing none has its `:clashes` memo reset and
  yields `#{}`.  Not gated on `*rebuilding?*`, since a nogood is belief state and a
  rebuild that skipped it would believe a decided loser again.  Binds
  `*clash-marked-below*` and the taxonomy's per-pass closure caches for the call."
  [kb region]
  (let [tax (reasoning/taxonomy kb)]
    (if (not (or (separations? tax) (tuple-marks? tax) (seq (tax/coverings tax))))
      ;; no clash can exist, and this is the one place the memo can be dropped
      (do (reset! (reasoning/clashes kb) {})
          (tax/take-equality-moves! tax :clashes)
          #{})
      ;; the taxonomy does not move during the pass, so its closures are held per pass
      (binding [*clash-marked-below*             (delay (clash-marked-below tax))
                tax/*closure-pass-cache*         (atom {})
                tax/*visible-neighbours-cache*   (atom {})
                tax/*separation-frame-cache*     (atom {})]
        (clash-nogoods kb @region)))))

(def ^:dynamic *incremental-preserving*
  "True (the default): `preserving-nogoods` carries each standing inherited clash whose
  inputs did not move, and re-asks only the stored facts a moved claim reaches.  False:
  every call re-asks every standing clash and the whole stored extent of every predicate
  a claim moved, the reference `inherited_clash_oracle_test` compares the memo against."
  true)

(defn- preserving-stamp
  "The inputs of every inherited clash's question compared as whole values: the `genlCx`
  generation, the contexts each flat-cache entry is asserted from, and the `except`
  roster.  When one moves, `preserving-nogoods` carries nothing."
  [kb]
  (let [tax (reasoning/taxonomy kb)]
    [(tax/relation-gen tax :genlCx) (tax/flat-contexts tax) @(reasoning/excepted kb)]))

(defn- member-priority
  "The rebuttal-range priority of an inherited nogood: the highest defeat-class rank among
  `members`."
  [tms members]
  (reduce max (map #(strength/rank-of (jtms/defeat-class tms %)) members)))

(defn- inherited-nogoods
  "The nogood maps `{:nogood :priority :vantages :kind :sentence :inherited}` for stored
  claim `h`, stating `sen`, against the `inherit/clashing-claim` answers `cs`: one per
  member set, its `:vantages` the most general of the contexts that found it."
  [kb h sen cs]
  (let [tms (reasoning/tms kb)
        tax (reasoning/taxonomy kb)]
    (mapv (fn [[members hits]]
            (let [c     (first hits)
                  [a b] (sort nm/compare-form [(:sentence c) sen])
                  vs    (into #{} (map :context) hits)]
              {:nogood   members
               :priority (member-priority tms members)
               :vantages (if (next vs) (tax/maximal-contexts tax vs) vs)
               :kind     :inherited
               :sentence (list 'contradicts a b)
               ;; the claim nobody stored, where it was read, the general `:claim` it was
               ;; read from and the handles `:via` which it was carried
               :inherited {:sentence (:sentence c) :context (:context c)
                           :claim (:claim c) :via (vec (:handles c))}}))
          (group-by #(into #{h} (cons (:claim %) (:handles %))) cs))))

(defn- preserving-entry
  "`s`'s inherited clash, or nil: `{:pred :own? :askers :classes :class :nogoods}`.  The
  clashing claims are `inherit/clashing-claim`'s answers from `s`'s own context or, when
  that finds none, from each vantage (`group-vantages` over `inherit/denial-contexts`);
  `:askers` is every context asked, `:classes` the defeat-class of every member but `s`,
  `:class` `s`'s own, and `:nogoods` `inherited-nogoods`.  An answer of no clash is an
  entry with no nogoods while some claim would deny `s` in a reader that saw both, so the
  `genlCx` edge that makes that reader is asked again, and while an asker reads something
  withdrawn, so the settle that clears the withdrawal asks again."
  [kb s]
  (let [sen  (:sentence s)
        own  (:context s)
        ask  #(inherit/clashing-claim kb sen %)
        tms  (reasoning/tms kb)
        make (fn [cs askers own?]
               {:pred    (nm/functor (kb/body-under-not sen))
                :own?    own?
                :askers  askers
                :classes (into {} (map (juxt identity #(jtms/defeat-class tms %)))
                               (mapcat #(cons (:claim %) (:handles %)) cs))
                :class   (jtms/defeat-class tms (:id s))
                :nogoods (inherited-nogoods kb (:id s) sen cs)})]
    (if-let [c (ask own)]
      (make [c] #{own} true)
      (let [denial (inherit/denial-contexts kb sen)
            vs     (sort (group-vantages kb s denial))
            cs     (into [] (keep ask) vs)
            askers (into #{own} vs)]
        (when (or (seq cs) (seq denial) (some #(seq (res/withdrawn-set kb %)) askers))
          (make cs askers false))))))

(defn- withdrawal-moves
  "The handles whose withdrawal at an asker in `seen` (`{context withdrawn-set}`, as the last
  call read it) differs now (`res/withdrawn-set`)."
  [kb seen]
  (into #{}
        (mapcat (fn [[k was]]
                  (let [now (res/withdrawn-set kb k)]
                    (when-not (identical? now was)
                      (let [now (or now #{}) was (or was #{})]
                        (concat (remove was now) (remove now was)))))))
        seen))

(defn- preserving-moves
  "What the moved handles `moves` (`[handle region?]`, `region?` false for a withdrawal
  alone) re-open, as `[whole reached]`: the preserved predicates whose stored extent is
  re-asked (`inherit/moved-channels`' other channels, and a `genl` edge between
  predicates), and the stored facts a moved claim reaches
  (`inherit/claim-reach-extent`).  A claim reaches when it is believed and known-true,
  and, moved in the region, when `vantaged` holds its predicate: the claims of every
  class decide which vantages ask.  `narrow?` false re-opens the stored extent of every
  predicate a claim moves.  The `genl` closures are global, since what a moved edge
  re-opens is asked from every context that reads it."
  [kb pairs moves vantaged narrow?]
  (let [recs   (:records kb)
        tms    (reasoning/tms kb)
        tax    (reasoning/taxonomy kb)
        extent (memoize #(reads/as-stored-with-functor (:index kb) %))
        preds  (into #{} (map first) pairs)
        ;; a functor whose channels read no argument answers once per call
        by-f   (memoize #(inherit/moved-channels kb (list %) pairs any?))]
    (inherit/with-memo
      (reduce
       (fn [[whole reached] [h region?]]
         (if-let [s (p/get-sentex recs h)]
           (let [sen   (sx/sentence-of s)
                 body  (kb/body-under-not sen)
                 f     (nm/functor body)
                 [claimed other]
                 (if (inherit/channels-read-arguments? f)
                   (inherit/moved-channels
                    kb sen pairs #(and (not (contains? whole %)) (seq (extent %))))
                   (by-f f))
                 ;; a `genl` edge between predicates makes one's claims the other's, and
                 ;; carries a mark over to a sub-predicate (`tax/props-over`)
                 whole (cond-> (into whole other)
                         (and (= 'genl f) (every? symbol? (nm/args body)))
                         (into (filter preds) (mapcat #(tax/genls-global tax %) (nm/args body))))
                 kt?   (delay (and (jtms/in? tms h)
                                   (strength/known-true? (jtms/defeat-class tms h))))]
             [whole
              (into reached
                    (comp (remove whole)
                          (filter #(or (not narrow?) (and region? (contains? vantaged %)) @kt?))
                          (mapcat #(or (when narrow? (inherit/claim-reach-extent kb sen %))
                                       (extent %))))
                    claimed)])
           [whole reached]))
       [#{} #{}]
       moves))))

(defn- entry-live?
  "Does every member of entry `e` but its candidate hold the defeat-class `e` recorded?"
  [tms e]
  (every? (fn [[h c]] (and (jtms/in? tms h) (= c (jtms/defeat-class tms h)))) (:classes e)))

(defn- preserving-entries
  "The standing inherited clashes after this call, `{handle entry}` (`preserving-entry`).
  An entry is carried when the stamp (`preserving-stamp`) did not move, the region holds
  no retraction, its predicate's extent was not re-opened, no moved claim reaches it
  (`preserving-moves`, over the region and `withdrawal-moves`), and its members hold the
  classes it recorded.  Every other entry, the region, and what the moves re-open are
  asked.  An entry whose candidate is OUT is kept and publishes nothing.  Under
  `*whole-store-region?*` with a region the store's size, nothing is carried and no
  extent is swept (docs/nmtms.md, \"The inherited-clash memo\")."
  [kb pairs region prev stamp]
  (let [recs    (:records kb)
        tms     (reasoning/tms kb)
        handles @region
        entries (:entries prev {})
        whole?  (and *whole-store-region?* (>= (count handles) (cap/count-sentexes recs)))
        fresh?  (or whole? (not *incremental-preserving*) (not= stamp (:stamp prev))
                    ;; a retracted handle has no record, so nothing reads what it moved
                    (some #(nil? (p/get-sentex recs %)) handles))
        [whole reached]
        (if whole?
          [#{} #{}]
          (preserving-moves kb pairs
                            (concat (map #(vector % true) handles)
                                    (when-not fresh?
                                      (map #(vector % false) (withdrawal-moves kb (:seen prev)))))
                            (into #{} (keep (fn [[_ e]] (when-not (:own? e) (:pred e)))) entries)
                            *incremental-preserving*))
        kept    (if fresh?
                  {}
                  (into {} (filter (fn [[h e]] (and (not (contains? whole (:pred e)))
                                                    (not (contains? reached h))
                                                    (some? (p/get-sentex recs h))
                                                    (entry-live? tms e))))
                        entries))
        idx     (:index kb)
        ask     (-> #{}
                    (into (keys entries))
                    (into handles)
                    (into reached)
                    (into (mapcat #(reads/as-stored-with-functor idx %)) whole)
                    (->> (remove kept)))
        preds   (into #{} (map first) pairs)]
    (into kept
          (keep (fn [h]
                  (when (jtms/in? tms h)
                    (when-let [s (p/get-sentex recs h)]
                      (when (contains? preds (nm/functor (kb/body-under-not (:sentence s))))
                        (when-let [e (preserving-entry kb s)] [h e]))))))
          ;; sorted so the queries run in a reproducible order
          (sort ask))))

(defn- preserving-nogoods
  "The clashes between a stored claim and a known-true claim argument preservation reads
  at its own tuple, as nogood maps (`inherited-nogoods`).  Resets `:preserved-clashes`,
  the memo `preserving-entries` carries.

  The members are the stored claim and the reading's reasons (`inherit/clashing-claim`'s
  `:claim` and `:handles`).  `:priority` is the rebuttal range, 1–2.  A candidate is asked
  from its own context first, the most general asker there is, and only when that finds
  nothing from `group-vantages` over `inherit/denial-contexts`.  A body stored in both
  polarities is `negation-nogoods`' pair, excluded by `clashing-claim`.  Behind an `empty?`
  on `kb`'s `:preserving` roster (docs/nmtms.md, \"What qualifies as a nogood\";
  docs/inherit.md)."
  [kb region]
  (let [pairs @(reasoning/preserving kb)]
    (if (empty? pairs)
      (do (reset! (reasoning/preserved-clashes kb) {}) #{})
      (let [tms     (reasoning/tms kb)
            stamp   (preserving-stamp kb)
            entries (preserving-entries kb (set (keys pairs)) region
                                        @(reasoning/preserved-clashes kb) stamp)]
        (reset! (reasoning/preserved-clashes kb)
                {:stamp   stamp
                 :entries entries
                 :seen    (into {} (map (juxt identity #(res/withdrawn-set kb %)))
                                (into #{} (mapcat :askers) (vals entries)))})
        (into #{}
              (mapcat (fn [[h e]]
                        (when (jtms/in? tms h)
                          ;; the other members hold the classes `e` recorded
                          (if (= (:class e) (jtms/defeat-class tms h))
                            (:nogoods e)
                            (map #(assoc % :priority (member-priority tms (:nogood %)))
                                 (:nogoods e))))))
              entries)))))

(defn- resolve-contradictions
  "Resolve the nogoods to a fixpoint and return
  `{:violated [hard...] :dilemmas [ngmap...] :rejoin #{rule...} :region delay}`.
  `:region` is `touched` as the last round read it, which is current because the last
  round defeated nothing.

  `constraint` is the pass's definitional nogoods, discovered once; `negation-nogoods` and
  `preserving-nogoods` are asked every round, and `scan` carries the first one's record
  reads across rounds (`moved-bodies`). A round applies one kind of defeat and re-enters: the
  scoped defeats the roster does not hold, else the global defeats that withdraw grounds,
  else the other global defeats. The hard clashes and the dilemmas are collected at the
  round that defeats nothing, and no nogood reaches a solver: `decide-nogood` answers a
  defeat, a dilemma or a hard clash. The order and the termination argument:
  docs/nmtms.md, \"The resolution rounds\"."
  [kb constraint region]
  (loop [rejoin #{}, scan (volatile! {:seen #{} :bodies #{}}), region region, round 1]
    (let [rd (vantage-reads kb)
          ;; `live-vantages` first: it drops a pair a defeated member already retired
          ;; at two map reads.  A nil vantage is the network's reading and is carried.
          grounded (if (= 1 round)
                     constraint
                     (keep (fn [ng]
                             (let [vs (filterv #(or (nil? %) (reads-clash? kb ng %))
                                               (live-vantages rd ng))]
                               (when (seq vs) (assoc ng :vantages (set vs)))))
                           constraint))
          ;; every nogood is decided at the vantages that still read it whole, and one
          ;; with none is dropped: an OUT member ranks 0, so a nogood handed back after
          ;; its defeat would be defeated again and the loop would not terminate
          live-at (into {}
                        (keep (fn [ng] (let [vs (live-vantages rd ng)] (when (seq vs) [ng vs]))))
                        (concat grounded
                                (phases/with-phase :discovery (negation-nogoods kb scan region))
                                (phases/with-phase :discovery (preserving-nogoods kb region))))
          active (seq (into #{} (keys live-at)))]
      (if-not active
        {:violated [] :dilemmas [] :rejoin rejoin :region region}
        (let [weighed   (for [ng active, v (live-at ng)]
                          [ng v (decide-nogood rd ng v)])
              decisions (map peek weighed)
              clears    (into #{} (keep (fn [[_ v d]]
                                          (when-let [h (:defeat d)]
                                            (when (global-defeat? kb h v) h))))
                              weighed)
              scoped    (into #{} (keep (fn [[_ v d]]
                                          (when-let [h (:defeat d)]
                                            (when-not (global-defeat? kb h v) [v h]))))
                              weighed)
              ;; a scoped round needs a defeat the roster lacks, which bounds the rounds
              roster    @(reasoning/scoped-defeats kb)
              fresh     (into #{} (remove (fn [[v h]] (contains? (get roster v) h))) scoped)
              grounds   (into #{} (filter #(tax/derives-from? (reasoning/taxonomy kb) %)) clears)
              defeat!   (fn [handles]
                          (phases/with-phase :belief
                            (jtms/defeat (reasoning/tms kb) handles)
                            (res/reconcile-withdrawn! kb)
                            (let [t (jtms/touched (reasoning/tms kb))]
                              (refresh-after-defeat kb t)
                              (delay t))))]
          (cond
            ;; the network does not move, so the shared region stands
            (seq fresh)
            (do (note-vantage-disagreements! kb weighed)
                (scope-defeats! kb fresh)
                (recur rejoin scan region (inc round)))

            (seq grounds)
            (let [region (defeat! grounds)]
              (note-vantage-disagreements! kb weighed)
              (recur (into rejoin (preserved-rejoins-for kb grounds)) scan region (inc round)))

            (seq clears)
            (let [region (defeat! clears)]
              (note-vantage-disagreements! kb weighed)
              (recur (into rejoin (preserved-rejoins-for kb clears)) scan region (inc round)))

            :else
            {:violated (vec (distinct (keep :hard decisions)))
             :dilemmas (vec (distinct (keep :dilemma decisions)))
             :rejoin   rejoin
             :region   region}))))))

(defn exposed-clashes
  "`core/exposed-clashes`' body: every jointly-visible disjointness clash the KB holds,
  in `violations`' entry shape, filed nowhere.  A term is a candidate iff it holds two
  believed memberships, so the walk over every stored sentex finds each candidate and
  takes no instance budget.  The `separations?` gate answers `[]` with no record fetched
  for a KB that separates nothing."
  [kb]
  (let [tax (reasoning/taxonomy kb)]
    (if-not (separations? tax)
      []                                             ; nothing separates anything
      (let [probes (exposure-probes tax)
            terms  (into #{}
                         (comp (believed-xf kb)
                               (keep (fn [s]
                                       (let [sen (:sentence s)]
                                         (when (and (sequential? sen) (= 2 (count sen))
                                                    (symbol? (first sen))
                                                    (symbol? (second sen)))
                                           (second sen))))))
                         (p/sentex-ids (:records kb)))]
        (into [] (comp (mapcat #(exposed-clashes-for-term kb % probes))
                       (distinct))
              ;; terms are symbols — a bare sort is the same content order
              (sort terms))))))

;; ---- the arity declaration that arrives after the facts ------------------
;;
;; `arity`'s retroactive half reports: it cannot refuse, and it cannot arbitrate
;; (docs/taxonomy.md, "What each constraint does in each arrival order").

(defn- arity-bound-by
  "The predicate whose binding arity `sen`, read in `context`, may newly supply, or nil:
  a root of the subtree `report-arity-reach!` sweeps.  `(arity P n)` and an exact-arity
  class membership of `P` declare a length; `(genl sub super)` binds `sub` to `super`'s
  (`checks/inherited-arity`), so its root is `sub` and never `super`.  A `genlCx` edge
  names no predicate; its ends are `predicates-below-context` and
  `arity-bindings-above-context`."
  [kb sen context]
  (let [f (nm/functor sen)
        as (rest sen)]
    (when-let [pred (cond
                      (= 'arity f) (when (= 2 (count as)) (first as))
                      (= 'genl f)  (when (= 2 (count as)) (first as))
                      ;; through the `genl` closure, as `checks/membership-arity` reads it
                      (= 1 (count as)) (when (checks/membership-arity kb f context)
                                         (first as)))]
      (when (symbol? pred) pred))))

;; A `genlCx` edge's reach has two ends, each complete alone, and the pass walks the
;; smaller (docs/taxonomy.md, "What each constraint does in each arrival order").

(defn- ancestor-extent
  "How many sentexes are stored across `contexts`, at one O(1) `count-in-context` each.
  It picks which end of an edge to enumerate, so a miscount costs a worse choice of end
  and never an answer."
  [kb contexts]
  (transduce (comp (filter symbol?) (map #(reads/stored-count-in-context (:index kb) %)))
             + 0 contexts))

(defn- predicates-below-context
  "The functors of the believed facts stored in the contexts that see `sub`: the lower
  end of a `(genlCx sub super)` edge's reach, as roots for the spec expansion.  Lazy,
  and in the ancestor set's own order, since a context cycle makes that set the whole
  graph (`members-in-ancestors`); the sweep beneath the roots is content-ordered."
  [kb sub]
  (for [s     (believed-in-ancestors kb (tax/context-down (reasoning/taxonomy kb) sub))
        :let  [sen (:sentence s)
               f   (when (sequential? sen) (nm/functor sen))]
        :when (symbol? f)]
    f))

(defn- arity-bindings-above-context
  "The predicates a believed binding stored in the contexts `super` sees binds, in every
  spelling `arity-bound-by` reads: the upper end of the edge's reach.  Lazy and
  unsorted, as `predicates-below-context`."
  [kb super]
  (for [s     (believed-in-ancestors kb (tax/context-up (reasoning/taxonomy kb) super))
        :let  [sen  (:sentence s)
               pred (when (sequential? sen) (arity-bound-by kb sen (:context s)))]
        :when pred]
    pred))

(defn- any-arity-declared?
  "Has the KB declared any predicate's arity?  The gate that turns `report-arity-reach!`
  off.  Reads the arity table, and the index cardinality of every sub-collection of
  `checks/exact-arity-class-gates`: a KB without CxCore's derivation rules holds only
  the membership spelling, which `checks/membership-arity` reads through the `genl`
  closure."
  [kb]
  (let [tax (reasoning/taxonomy kb)]
    (or (seq (tax/arity-declarations tax))
        (boolean (some (fn [t]
                         (some #(pos? (reads/stored-count-with-functor (:index kb) %))
                               (tax/specs-global tax t)))
                       checks/exact-arity-class-gates)))))

(defn- believed-context-edges
  "The `(genlCx sub super)` edges among the sentexes `believed`, in content order, so a
  budget cut reaches the same ancestor sets in every arrival order."
  [believed]
  (content-order
   (filterv (fn [s]
              (let [sen (:sentence s)]
                (and (sequential? sen)
                     (= 'genlCx (nm/functor sen))
                     (= 2 (count (nm/args sen)))
                     (every? symbol? (nm/args sen)))))
            believed)))

(defn- stored-specs
  "The spec subtrees of `roots`, expanded in one `tax/specs-of-all` walk and kept to the
  predicates holding a stored fact, as a sorted set: an index cardinality per predicate
  and no record read (docs/taxonomy.md, \"What a batch of edges costs the passes that
  read it\")."
  [kb tax roots]
  (into (sorted-set)
        (filter #(pos? (reads/stored-count-with-functor (:index kb) %)))
        (tax/specs-of-all tax roots)))

(def ^:private max-arity-findings
  "The most `:arity` entries one `report-arity-reach!` pass files; past it one
  `:arity-report-truncated` entry counts the rest (docs/taxonomy.md)."
  8)

(defn- report-arity-reach!
  "File the stored wrong-arity facts an arity binding in the moved region `touched`
  convicts, and decide nothing: the facts stay believed.  One `:arity` entry per
  convicted predicate, carrying `:count`, `:sample`, `:via` and the declaration's handle
  in `:declared-after`, at most `max-arity-findings` of them and then one
  `:arity-report-truncated`.  The roots are what `arity-bound-by` names plus the smaller
  end of each `genlCx` edge, swept over their spec subtrees on one instance budget; a cut
  files one `:arity-truncated` entry whether or not anything was found.  Runs under
  either constraint policy, since it moves no belief; off while `*rebuilding?*` and for a
  KB that declares no arity.  docs/taxonomy.md, \"What each constraint does in each
  arrival order\"."
  [kb touched]
  (when (and (not *rebuilding?*)
             (seq touched)
             (any-arity-declared? kb))
    (let [left    (volatile! (long *exposure-instance-budget*))
          unswept (volatile! [])       ; predicates the budget cut, in content order
          unreached (volatile! [])
          believed (into [] (believed-xf kb) touched)
          named (into #{} (keep #(arity-bound-by kb (:sentence %) (:context %))) believed)
          edges (believed-context-edges believed)
          roots (reduce
                 (fn [acc e]
                   (let [tax         (reasoning/taxonomy kb)
                         [sub super] (nm/args (:sentence e))
                         ends        (if (<= (ancestor-extent kb (tax/context-down tax sub))
                                             (ancestor-extent kb (tax/context-up tax super)))
                                       (predicates-below-context kb sub)
                                       (arity-bindings-above-context kb super))
                         ;; the same budget the sweep below spends
                         [taken cut?] (take-budgeted left ends)]
                     (when cut? (vswap! unreached conj (:sentence e)))
                     (into acc taken)))
                 named
                 edges)
          preds (stored-specs kb (reasoning/taxonomy kb) roots)
          ;; one membership reader per context met, so its memo serves every fact there
          reader (let [cache (volatile! {})]
                   (fn [ctx]
                     (or (get @cache ctx)
                         (let [r (kb/membership-reader kb ctx)]
                           (vswap! cache assoc ctx r)
                           r))))
          sweep (fn [findings pred]
                  (let [[taken cut?] (take-budgeted left (predicate-sentexes kb pred))
                        found (into []
                                    (keep #(some->> (checks/arity-violation
                                                     kb (:sentence %) (:context %)
                                                     (reader (:context %)))
                                                    (vector %)))
                                    taken)]
                    (when cut? (vswap! unswept conj pred))
                    (if-not (seq found)
                      findings
                      (let [found (nm/sort-by-content-key
                                   (fn [[s _]] [(:sentence s) (:context s)]) found)
                            [s v] (first found)]
                        (conj findings
                              {:violation :arity
                               :sentence  (:sentence s)
                               :context   (:context s)
                               :detail    {:predicate      pred
                                           :expected       (:expected v)
                                           :count          (count found)
                                           :sample         (mapv (comp :sentence first)
                                                                 (take 3 found))
                                           :declared-after (:opposing-handle v)
                                           :truncated      cut?
                                           :budget         (when cut?
                                                             *exposure-instance-budget*)
                                           :via            (:via v)
                                           :message
                                           ;; worded as the entry point words it
                                           (str "arity declared after the facts: " pred
                                                " "
                                                (checks/arity-binding-clause
                                                 pred (:via v) (:expected v))
                                                " and " (count found)
                                                " stored fact(s) of it disagree"
                                                (when cut?
                                                  (str " — the sweep was cut short at "
                                                       *exposure-instance-budget*
                                                       " facts, so there may be more")))}})))))]
      (let [findings (reduce sweep [] preds)
            ;; a finding spends at least one fact, so the budget bounds `findings`
            over     (- (count findings) max-arity-findings)
            entries  (vec (take max-arity-findings findings))
            entries
            (cond-> entries
              (pos? over)
              (conj {:violation :arity-report-truncated
                     :detail    {:predicates (count findings)
                                 :filed      max-arity-findings
                                 :facts      (transduce (map #(get-in % [:detail :count]))
                                                        + 0 findings)
                                 :sample     (mapv #(get-in % [:detail :predicate])
                                                   (take 3 (drop max-arity-findings findings)))
                                 :message
                                 (str "arity report bounded at " max-arity-findings
                                      " entries: " (count findings)
                                      " predicate(s) hold facts a binding convicts and "
                                      over " of them are named by no entry")}})

              (or (seq @unswept) (seq @unreached))
              (conj {:violation :arity-truncated
                     :detail    {:predicates  (count @unswept)
                                 :sample      (vec (take 3 @unswept))
                                 :edges       (count @unreached)
                                 :edge-sample (vec (take 3 @unreached))
                                 :budget      *exposure-instance-budget*
                                 :message
                                 (str "arity sweep cut short at "
                                      *exposure-instance-budget* " facts: "
                                      (when (seq @unswept)
                                        (str (count @unswept)
                                             " predicate(s) went unswept, so wrong-arity"
                                             " facts they hold are unreported"))
                                      (when (and (seq @unswept) (seq @unreached)) "; ")
                                      (when (seq @unreached)
                                        (str (count @unreached)
                                             " genlCx edge(s) went unswept, so predicates"
                                             " their visibility move binds are unreported")))}}))]
        (when (seq entries)
          (violations/report kb entries))))))

(def ^:private unarbitrable-mark-kinds
  "The two marks whose conviction names nothing to weigh, by the functor that declares
  each, against the taxonomy prop it is cached under: `(irreflexive P)` convicts a lone
  self tuple, and `(anti_symmetric P)` a converse no merge can reconcile."
  {'irreflexive :irreflexive, 'anti_symmetric :anti-symmetric})

(defn- unarbitrable-mark-root
  "The predicate whose spec subtree believed sentence `sen` puts back in question for an
  unarbitrable mark, or nil.  Two sentences name one: the mark's own declaration names
  the predicate it marks, and a `(genl sub super)` edge names `sub` when a mark stands at
  or above `super`, since the sub's tuples then answer to it (`tax/props-over`, unscoped
  here — the per-fact check reads the scoped closure)."
  [tax sen]
  (when (sequential? sen)
    (let [f  (nm/functor sen)
          as (nm/args sen)]
      (cond
        (and (contains? unarbitrable-mark-kinds f) (= 1 (count as)) (symbol? (first as)))
        (first as)

        (and (= 'genl f) (= 2 (count as)) (every? symbol? as)
             (some #(seq (tax/props-over tax % (second as))) (vals unarbitrable-mark-kinds)))
        (first as)))))

(defn- unarbitrable-reach-entry
  "The ledger entry for the stored facts `found` convicts under one mark — `kind` and the
  marked predicate `via` — each `found` element a `[sentex problem]` pair in content
  order.  The kind is written out per arm so the ledger roster reads it at the filing site."
  [kind via found]
  (let [[s]    (first found)
        detail {:via     via
                :count   (count found)
                :sample  (mapv (comp :sentence first) (take 3 found))
                :message (case kind
                           :irreflexive
                           (str "irreflexive reached stored content: " via " cannot hold of a"
                                " thing and itself, and " (count found) " stored self"
                                " tuple(s) of it or a predicate beneath it do")
                           :anti-symmetric
                           (str "anti_symmetric reached stored content: " (count found)
                                " stored fact(s) of " via " or a predicate beneath it"
                                " have a converse whose arguments no merge can make one"
                                " thing"))}]
    (merge (case kind
             :irreflexive    {:violation :irreflexive}
             :anti-symmetric {:violation :anti-symmetric})
           {:sentence (:sentence s) :context (:context s) :detail detail})))

(defn- report-unarbitrable-reach!
  "File the stored facts an `irreflexive` or `anti_symmetric` mark convicts once the
  moved region `touched` brings the mark to them, and decide nothing: the facts stay
  believed.  One entry per mark kind and marked predicate (`unarbitrable-reach-entry`),
  bounded by the marks the KB declares.  The roots are the predicates
  `unarbitrable-mark-root` names, swept over their spec subtrees as
  `report-arity-reach!` sweeps; a `genlCx` edge sweeps the smaller of the facts below
  its sub and every marked subtree's extent.  Each candidate is asked
  `checks/unarbitrable-mark-problems` from its own context.  One instance budget; a cut
  files one `:unarbitrable-reach-truncated` entry whether or not anything was found.
  Off while `*rebuilding?*` and for a KB declaring neither mark.  docs/nmtms.md,
  \"Which entry point the content came through\"."
  [kb touched]
  (let [tax (reasoning/taxonomy kb)]
    (when (and (not *rebuilding?*)
               (seq touched)
               (some #(seq (tax/props tax %)) (vals unarbitrable-mark-kinds)))
      (let [left      (volatile! (long *exposure-instance-budget*))
            unswept   (volatile! [])
            unreached (volatile! [])
            ;; keyed on handle and kind: a fact reached from both ends is one finding
            found     (volatile! {})
            examine!  (fn [s]
                        (when (nil? (:antecedent s))
                          (doseq [v (checks/unarbitrable-mark-problems
                                     kb (:sentence s) (:context s))]
                            (vswap! found assoc [(:id s) (:type v)] [s v]))))
            believed  (into [] (believed-xf kb) touched)
            named     (into #{} (keep #(unarbitrable-mark-root tax (:sentence %))) believed)
            ;; the upper end of a context edge's reach, built at most once
            marked    (delay
                        (let [preds (stored-specs kb tax
                                                  (into #{} (mapcat #(tax/props tax %))
                                                        (vals unarbitrable-mark-kinds)))]
                          {:preds  preds
                           :extent (transduce
                                    (map #(reads/stored-count-with-functor (:index kb) %))
                                    + 0 preds)}))
            edges     (believed-context-edges believed)
            ;; each edge sweeps its lower end here or asks for the marked extents below
            wide?     (reduce
                       (fn [wide? e]
                         (let [below (tax/context-down tax (first (nm/args (:sentence e))))]
                           (if (<= (ancestor-extent kb below) (:extent @marked))
                             (let [[taken cut?] (take-budgeted
                                                 left (believed-in-ancestors kb below))]
                               (run! examine! taken)
                               (when cut? (vswap! unreached conj (:sentence e)))
                               wide?)
                             true)))
                       false edges)
            preds     (cond-> (stored-specs kb tax named)
                        wide? (into (:preds @marked)))]
        (doseq [pred preds]
          (let [[taken cut?] (take-budgeted left (predicate-sentexes kb pred))]
            (run! examine! taken)
            (when cut? (vswap! unswept conj pred))))
        (let [groups  (group-by (fn [[_ v]] [(:type v) (:pred v)]) (vals @found))
              entries (into []
                            (map (fn [[kind via]]
                                   (unarbitrable-reach-entry
                                    kind via
                                    (nm/sort-by-content-key
                                     (fn [[s _]] [(:sentence s) (:context s)])
                                     (get groups [kind via])))))
                            (sort (keys groups)))
              entries
              (cond-> entries
                (or (seq @unswept) (seq @unreached))
                (conj {:violation :unarbitrable-reach-truncated
                       :detail    {:predicates  (count @unswept)
                                   :sample      (vec (take 3 @unswept))
                                   :edges       (count @unreached)
                                   :edge-sample (vec (take 3 @unreached))
                                   :budget      *exposure-instance-budget*
                                   :message
                                   (str "irreflexive / anti_symmetric sweep cut short at "
                                        *exposure-instance-budget* " facts: "
                                        (when (seq @unswept)
                                          (str (count @unswept)
                                               " predicate(s) went unswept"))
                                        (when (and (seq @unswept) (seq @unreached)) " and ")
                                        (when (seq @unreached)
                                          (str (count @unreached)
                                               " genlCx edge(s) went unswept below"))
                                        ", so facts the marks convict there are"
                                        " unreported")}}))]
          (when (seq entries)
            (violations/report kb entries)))))))

(defn- report-arbitration-cut!
  "File what `*arbitration-cut*` collected over the settle's passes as one
  `:arbitration-truncated` entry, deduped by sentence.  Nothing on a rebuild, where
  `settle*` binds the sink nil so nothing is collected."
  [kb]
  (when-let [sink *arbitration-cut*]
    (when-let [cut (cut-notice :arbitration-truncated (distinct @sink)
                               {:sweep       "arbitration"
                                :unit        "instances"
                                :noun        "declaration"
                                :count-key   :triggers
                                :consequence (str "content they implicate is undecided"
                                                  " until a later settle's sweep, which"
                                                  " resumes past the cut, reaches it")})]
      (violations/report kb [cut]))))

(defn- carry-arbitration-sweeps!
  "Hand the sweeps the settle's last pass left unfinished (`*arbitration-progress*`) to
  the next settle: their keys to `:clashes`' `:pending`, which an image carries, and their
  unread tails to `:arbitration-cursors`, which it does not.  A settle whose passes swept
  nothing keeps the carried sweeps, with the tails pruned to the keys `:pending` still
  names."
  [kb]
  (let [cursors (reasoning/arbitration-cursors kb)]
    (if-some [m (some-> *arbitration-progress* deref)]
      (do (swap! (reasoning/clashes kb)
                 #(if (seq m) (assoc % :pending (set (keys m))) (dissoc % :pending)))
          (reset! cursors m))
      (swap! cursors select-keys (:pending @(reasoning/clashes kb))))))

(defn- report-partner-cut!
  "File what `*partner-cut*` collected over the settle as one `:partner-sweep-truncated`
  entry naming the `[predicate arity]` determinant sweeps `partner-contexts` capped, in
  content order.  Nothing when the sink is nil: on a rebuild, and at the assert entry
  point.  What its cut costs (a vantage never asked): docs/taxonomy.md, \"What a
  declaration reaches back over\"."
  [kb]
  (when-let [sink *partner-cut*]
    (when-let [sweeps (seq (nm/sort-by-content-key
                            (juxt (comp nm/name-key :pred) :arity) compare @sink))]
      (violations/report
       kb [{:violation :partner-sweep-truncated
            :detail    {:sweeps (vec sweeps)
                        :budget *exposure-instance-budget*
                        :message
                        (str "partner discovery bounded at " *exposure-instance-budget*
                             " instances for "
                             (str/join ", " (map #(str (:pred %) "/" (:arity %)) sweeps))
                             "; a vantage that sees a clashing pair past the cap is not"
                             " asked, so the pair is undecided, and the prefix is"
                             " stable, so a later settle re-reads it rather than"
                             " reaching past it")}}]))))

(def ^:dynamic *scoped-before*
  "What the settle in progress read about the scoped defeats before it cleared them
  (`scoped-snapshot`), or nil when there were none.  `settle-finish` reads it to publish the
  belief a scoped defeat moved, which no relabel records."
  nil)

(defn- scoped-snapshot
  "`{:region :withdrawn}` for the current scoped defeats, or nil when there are none.
  `:region` is the forward consequence closure of the scoped-defeated handles, the only
  handles whose own-context belief a scoped defeat can move.  `:withdrawn` is the part of
  it that is IN in the network and withdrawn from its own context (`res/believed-at?`)."
  [kb]
  (let [sd @(reasoning/scoped-defeats kb)]
    (when (seq sd)
      (let [tms    (reasoning/tms kb)
            recs   (:records kb)
            region (:region (jtms/grounded-in-region tms (into #{} (mapcat val) sd)))]
        {:region    region
         :withdrawn (into #{} (filter (fn [h]
                                        (and (jtms/in? tms h)
                                             (when-let [s (p/get-sentex recs h)]
                                               (not (res/believed-at? kb h (:context s)))))))
                          region)}))))

(defn- scoped-moves
  "The belief the scoped defeats moved in this settle, which no relabel records, as
  `{:moved :was-in :withdrawn-before}` for `settle-finish`'s window.  `:moved` is the
  scoped defeats' closure before the settle and after it; `:was-in` is the part of it
  outside the relabelled `region` that is IN in the network, a label the settle did not
  relabel being the one it began with; `:withdrawn-before` is the part its own context
  read as withdrawn when the settle began."
  [kb region]
  (let [before *scoped-before*
        cand   (into (set (:region before)) (:region (scoped-snapshot kb)))]
    (if (empty? cand)
      {:moved #{} :was-in #{} :withdrawn-before #{}}
      {:moved            cand
       :was-in           (into #{} (filter #(and (not (contains? region %))
                                                 (jtms/in? (reasoning/tms kb) %)))
                               cand)
       :withdrawn-before (set (:withdrawn before))})))

(defn- settle-finish
  "Reconcile the derived caches with settled belief, file the reports, publish the
  moved region to the sinks and the feed, clear the touched window, and return
  `violated`.  `belief-moved?` gates the first `refresh-beliefs` reconcile.  The order
  and each gate: docs/nmtms.md, \"What `settle-finish` reconciles\"."
  [kb passes moved violated dilemmas belief-moved?]
  ;; the depth repair a `with-deferred-settle` batch owes; free when nothing deferred
  (tax/restore-depths (reasoning/taxonomy kb))
  (let [region   (delay (jtms/touched (reasoning/tms kb)))
        extra    (volatile! #{})     ; region members no relabel recorded
        extra-in (volatile! #{})     ; ...of which these were believed until this settle
        before (jtms/superseded (reasoning/tms kb))]
    ;; forces the region only on a timing run (`settle_region_cost_test` counts reads)
    (when (phases/profiling?) (phases/note-region! (count @region)))
    (when belief-moved?
      (special/reconcile-belief-change kb @region)
      ;; the reconcile can open or close a cycle (docs/taxonomy.md)
      (tax/restore-depths (reasoning/taxonomy kb)))
    ;; the data a moved `except` can re-spell join the region (`special/take-except-moves!`)
    (let [{:keys [extra full?] moved :region} (special/take-except-moves! kb)]
      (special/refresh-supersessions kb extra (cond full?        nil
                                                    (seq moved)  (into @region moved)
                                                    :else        @region)))
    ;; `moved` is every datum whose supersession entry changed since the last settle
    ;; finished, by this refresh or an earlier one on the assert path, so each set below
    ;; filtered out of it is the one filtered out of `before` and `after` whole
    (let [after (jtms/superseded (reasoning/tms kb))
          moved (or (special/take-supersession-moves! kb)
                    (into (set (keys before)) (keys after)))]
      (vswap! extra into moved)
      ;; a datum superseded by this settle was believed until now, and no relabel says so
      (vswap! extra-in into (filter #(and (contains? after %) (not (contains? before %)))) moved)
      (note-supersession-flips! kb (select-keys before moved) (select-keys after moved))
      ;; a merge supersedes a declaration with no label moving, after the reconcile above
      (when (seq moved)
        (special/reconcile-belief-change kb (into @region moved)))
      ;; the spellings an un-merge gave back, for `settle` to re-seed
      (when-let [sink (and (not *rebuilding?*) *unmerged-sink*)]
        (vswap! sink into
                (filter #(and (contains? before %) (not (contains? after %))
                              (jtms/in? (reasoning/tms kb) %)))
                moved)))
    ;; the re-arm queue's reader has run
    (reset! (reasoning/sib-exc-dirty kb) #{})
    (carry-arbitration-sweeps! kb)
    (report-arbitration-cut! kb)
    (report-partner-cut! kb)
    ;; the `*rebuilding?*` gates here keep a rebuild from forcing the region
    (when-not *rebuilding?*
      (report-arity-reach! kb @region))
    (when-not *rebuilding?*
      (report-unarbitrable-reach! kb @region))
    ;; before the region is cleared: it decides which standing reports are rebuilt
    (record-clashes! kb violated dilemmas @region)
    ;; the window is built only when a sink is bound or a listener registered
    (let [sink    *touched-sink*
          in-sink *touched-in-sink*
          fed?    (and (not *rebuilding?*) (feed/wants-region? kb))]
      (when (or sink in-sink fed?)
        (let [scoped (scoped-moves kb @region)
              moved  (-> @extra (into @region) (into (:moved scoped)))
              was-in (-> @extra-in
                         (into (jtms/touched-in (reasoning/tms kb)))
                         (into (:was-in scoped))
                         (set/difference (:withdrawn-before scoped)))]
          (when sink    (swap! sink into moved))
          (when in-sink (swap! in-sink into was-in))
          (when fed?    (feed/note-region! kb moved was-in)))))
    ;; the last read of the touched window before the reset, and the first to see what
    ;; the refreshes above moved
    (res/reconcile-withdrawn! kb)
    (jtms/reset-touched! (reasoning/tms kb))
    (swap! (reasoning/settle-stats kb)
           (fn [s] (-> s
                       (assoc :iterations moved :passes passes)
                       (update-in [:histogram moved] (fnil inc 0))))))
  ;; the pass count says whether the KB's exceptions have started to interact
  (trove/log! {:level :debug :id ::settled
               :data {:passes     passes
                      :iterations moved
                      :moved?     belief-moved?
                      :conflicts  (count violated)
                      :dilemmas   (count dilemmas)}})
  violated)

(defn- finish-settle
  "Close one settle: note the pass count for `settle-phases`, run `settle-finish` inside
  the `:finish` span, and file this settle's record.  Every `settle*` return runs
  through here."
  [kb passes moved violated dilemmas belief-moved?]
  (phases/note-passes! passes)
  (res/reconcile-withdrawn! kb)
  (let [r (phases/with-phase :finish
            (settle-finish kb passes moved violated dilemmas belief-moved?))]
    (phases/end-settle!)
    r))

(defn- settle*
  "Relabel, resolve the nogoods, and re-evaluate the `exceptWhen` exceptions the
  triggers queued, to a joint fixpoint of at most `max-settle-passes` passes.  Records
  the unsatisfiable clashes in `conflicts` and the dilemmas in `contradictions`, and
  returns the former.  `clear-defeats!` runs first, so a contradiction no longer present
  revives its loser.  A pass that leaves the blocked set as it was (`set-blocked`
  replaces) and queues, revives and releases nothing ends the loop; every other pass
  counts in `settle-stats`' `:iterations`.  The sweep-cut sinks
  `*arbitration-cut*` and `*partner-cut*` are bound for the whole settle, and nil on a
  rebuild; `*arbitration-progress*` is bound for the whole settle, rebuild or not."
  [kb]
  ;; one `settle-phases` record per settle, filed by `finish-settle` at each return
  (phases/begin-settle!)
  ;; `scoped-snapshot` reads each reader's withdrawal as the writes before this settle left it
  (res/reconcile-withdrawn! kb)
  (binding [*arbitration-cut*      (when-not *rebuilding?* (volatile! []))
            *arbitration-progress* (volatile! nil)
            *partner-cut*          (when-not *rebuilding?* (volatile! #{}))
            ;; read before the settle clears the scoped defeats, for `settle-finish`'s window
            *scoped-before*        (scoped-snapshot kb)]
    ;; a label flips by a revival, a defeat, a block change or a caller's relabel before
    ;; the settle, and `moved?` is the `belief-moved?` gate over all four
    (let [defeated-before  (jtms/defeated (reasoning/tms kb))
          defeated-before? (boolean (seq defeated-before))
          scoped-before?   (boolean (seq @(reasoning/scoped-defeats kb)))
          moved? (fn [moved] (or defeated-before? scoped-before? *relabelled-before?*
                                 (boolean (seq (jtms/defeated (reasoning/tms kb))))
                                 (boolean (seq @(reasoning/scoped-defeats kb)))
                                 (pos? moved)))]
      (phases/with-phase :belief
        (jtms/clear-defeats! (reasoning/tms kb))
        (clear-scoped-defeats! kb))
      ;; reconcile the caches with what `clear-defeats!` revived, or a caller relabelled,
      ;; before discovery reads them: a revived `genl` or `genlCx` edge can make a pair
      ;; jointly visible.  The region is read once per pass into a delay (docs/nmtms.md,
      ;; "The runtime view").
      (let [region        (delay (jtms/touched (reasoning/tms kb)))
            revival-flips (phases/with-phase :belief
                            (when (or defeated-before? *relabelled-before?*)
                              (special/reconcile-belief-change kb @region)
                              (tax/restore-depths (reasoning/taxonomy kb))
                              ;; ...and an except among the revived is a visibility flip:
                              ;; what it hid is seeable again, and only this settle knows
                              ;; the defeat was lifted
                              (recheck-flipped-excepts kb defeated-before)))
            ;; the records asked the subsumption question this settle, in each direction
            ;; (`subsumed-blocks`, `released-subsumed`), and the mints it withdrew
            subsumption-asked (volatile! #{})
            release-asked     (volatile! #{})
            withdrawn         (volatile! #{})]
        (loop [pass 1, moved 0, flips (or revival-flips #{}), reseeded #{}, relost #{}
               region region]
          ;; definitional clashes per pass: a re-chain can store content, a defeat cannot
          (let [_      (res/reconcile-withdrawn! kb)
                ngs    (phases/with-phase :discovery (constraint-nogoods kb region))
                watch  (resolution-watch kb region)
                defeated-pre (set (jtms/defeated (reasoning/tms kb)))
                region-in region
                {:keys [violated dilemmas rejoin region]}
                (phases/with-phase :resolution (resolve-contradictions kb ngs region))
                flipped (resolution-flips kb watch region-in region)
                ;; a resolution that defeated (or revived) a visibility except flipped
                ;; what its ancestor set can see — queue the same re-check its arrival or
                ;; departure queues, and carry the marked rules to the re-chain, since a
                ;; reveal moves no blocked justification for the drain to notice
                flips  (into flips
                             (recheck-flipped-excepts
                              kb (let [e (reads/stored-count-with-functor
                                          (:index kb) sx/except-functor)]
                                   ;; one record fetch per flipped handle, or the
                                   ;; functor root when that is smaller; belief is
                                   ;; what `flipped` already decided
                                   (if (<= (count flipped) e)
                                     flipped
                                     (filter #(contains? flipped %)
                                             (reads/as-stored-with-functor
                                              (:index kb) sx/except-functor))))))
                ;; ...and one that flipped a denial of an equation instance moved the
                ;; rewrites it blocks, which `except-move-seeds` below sweeps
                _      (special/note-denial-flips! kb flipped)
                ;; ...and a datum this resolution newly defeated may have released a
                ;; watched rule's `unknown` or exception, whose swept firing no instrument
                ;; below can find (`released-by-defeat`)
                flips  (into flips
                             (released-by-defeat
                              kb (remove (into defeated-pre defeated-before)
                                         (jtms/defeated (reasoning/tms kb)))))
                queued (drain-recheck! kb)
                ;; a visibility transition owes the blanket re-join even when nothing
                ;; blocked, so it is read before the unproductive-pass gate
                forced (vec (forced-recheck-rules queued))
                ;; ...and the datums whose belief came back; `reseeded` seeds each once per
                ;; settle, since the window spans the settle
                revived (revived-seeds kb reseeded region)
                ;; ...and the facts under an edge a firing named that this settle defeated,
                ;; whose second route nothing else re-joins (`departed-seeds`)
                out      (departed-handles kb region)
                departed (departed-seeds kb reseeded out)
                ;; ...and the firings a reader below a scoped defeat or an `except` reads as
                ;; withdrawn while it still reaches over a second route (`lost-firing-seeds`)
                lost   (lost-firing-seeds kb relost)
                ;; ...and the firings an argument constraint dropped that the content this
                ;; settle stored no longer convicts (`released-constraint-refusals`)
                cfree  (released-constraint-refusals kb region)
                ;; ...and the types a declaration could not mint until its type reached
                ;; `thing`, minted now that it has (`released-mints`)
                mnew   (-> (released-mints kb)
                           (into (released-lifts kb region))
                           ;; ...and the merges and lifts a revived mark owes the facts
                           ;; that arrived while it was OUT (`revived-mark-seeds`)
                           (into (revived-mark-seeds kb revived))
                           ;; ...and the twins an `except` that began or stopped hiding
                           ;; an equality or a merge mark owes (`except-move-seeds`)
                           (into (except-move-seeds kb))
                           ;; ...and the entailments and equalities a defeated genl
                           ;; edge took OUT while a second route still licenses them
                           ;; (`defeated-derivation-seeds`)
                           (into (defeated-derivation-seeds kb out)))
                ;; the relabelled records, read once for both halves of the subsumption question
                rsx    (delay (into [] (keep #(p/get-sentex (:records kb) %)) @region))
                mnew   (into mnew (released-subsumed kb rsx release-asked @withdrawn))
                ;; ...and the other direction of the same question: the mints a
                ;; membership arriving this settle has made redundant, whose
                ;; justifications this pass blocks so the sweep collects the records
                wdrawn (subsumed-blocks kb rsx (jtms/touched-in (reasoning/tms kb))
                                        subsumption-asked)]
            (if (and (empty? queued) (empty? revived) (empty? rejoin) (empty? departed)
                     (empty? lost) (empty? cfree) (empty? mnew)
                     (empty? (:blocked wdrawn)))
              (finish-settle kb pass moved violated dilemmas (moved? moved))
              (let [was  (jtms/blocked (reasoning/tms kb))
                    new  (into (exception-blocked-set kb queued) (:blocked wdrawn))
                    ;; a rule an arrival can release is owed a re-join whether or not anything
                    ;; blocked
                    aggs (rejoin-on-arrival-rules kb queued)
                    ;; ...and so is a firing refused before it could be blocked
                    {free :free over :overflow} (released-refusals kb queued)]
                (if (and (= new was) (empty? forced) (empty? aggs)
                         (empty? free) (empty? over) (empty? flips)
                         (empty? revived) (empty? rejoin) (empty? departed) (empty? lost)
                         (empty? cfree) (empty? mnew))
                  (finish-settle kb pass moved violated dilemmas (moved? moved))   ; unproductive pass: converged
                  ;; read before the sweep, which deletes justifications
                  (let [released (released-rules kb was new)]
                    (vswap! withdrawn into (:withdrawn wdrawn))
                    (jtms/set-blocked (reasoning/tms kb) new)
                    (sweep-excepted! kb (into #{} (remove was) new))
                    ;; released refusals re-placed from their recorded bindings, on one
                    ;; agenda with the revived datums and the mints
                    (let [seeds (-> (into [] (mapcat (fn [[rh e]] (chain/release-refusal! kb rh e)))
                                          (concat free cfree))
                                    (into revived)
                                    (into mnew))]
                      (when (seq seeds) (rechain-seeds kb seeds)))
                    ;; the re-join a defeated witness owes, silent where it places nothing,
                    ;; as the retraction path's is (`chain/*report-no-placement?*`)
                    (when (seq departed)
                      (binding [chain/*report-no-placement?* false] (rechain-seeds kb departed)))
                    ;; each reader's lost firings, re-derived with every witness search
                    ;; asked from that reader
                    (doseq [[r pairs] lost]
                      (binding [chain/*witness-view*         r
                                chain/*report-no-placement?* false]
                        (rechain-seeds kb (into [] (comp (mapcat second) (distinct)) pairs))))
                    ;; only the rules this pass released, never every rule it touched: a
                    ;; rule seed joins over the whole extent
                    (rechain-exception-rules kb (into released
                                                      (concat (blanket-recheck-rules queued)
                                                              aggs
                                                              over
                                                              flips
                                                              rejoin
                                                              (keys @(reasoning/recheck kb)))))
                    (if (< pass max-settle-passes)
                      (recur (inc pass) (inc moved) #{} (-> reseeded (into revived) (into departed))
                             (into relost (for [[r pairs] lost, [h _] pairs] [r h]))
                             (delay (jtms/touched (reasoning/tms kb))))
                      (do (trove/log! {:level :warn :id ::exception-fixpoint
                                       :msg  (str "exception re-check did not converge in "
                                                  max-settle-passes " passes; giving up")
                                       :data {:passes pass :blocked (count new)}})
                          (finish-settle kb pass (inc moved) violated dilemmas (moved? (inc moved)))))))))))))))

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
  the network already.  The network (`jtms/hold!`) and both scoped rosters
  (`observe/hold-atom!`) are held before `observe/open-hold!` registers the hold, so a
  reader switches to all three at once (docs/nmtms.md, \"Two representations of the same
  network\")."
  [kb]
  (when-not *rebuilding?*
    (let [tms (reasoning/tms kb)
          sd  (reasoning/scoped-defeats kb)
          vd  (reasoning/vantage-disagreements kb)
          h   (observe/new-hold)]
      (when (jtms/hold! tms h)
        (observe/hold-atom! sd h)
        (observe/hold-atom! vd h)
        (observe/open-hold! h)
        [tms h sd vd]))))

(defn- publish-belief!
  "Publish what the settle decided under `held` (`hold-belief!`'s answer): close the hold,
  so every reader reads the belief the settle reached in one step, then drop what the
  network and the rosters kept for it."
  [held]
  (when-let [[tms h sd vd] held]
    (observe/close-hold! h)
    (jtms/release! tms h)
    (observe/release-atom! sd)
    (observe/release-atom! vd)))

(defn settle
  "Settle belief (`settle*`) under a belief hold, re-settle while an un-merge gives
  spellings back (at most `max-unmerge-rounds` rounds), then deliver the moved region to
  the feed listeners, outside the relabel so a listener's write starts a fresh settle.
  Returns the last round's unsatisfiable clashes.  The un-merge rounds:
  docs/nmtms.md, \"The other half: a spelling an un-merge gives back\"."
  [kb]
  (let [held (hold-belief! kb)
        violated
        ;; the last round's reading is where the KB landed
        (try
          (loop [round 1]
            (let [seeds (volatile! #{})
                  v     (binding [*unmerged-sink* seeds] (settle* kb))
                  back  (into (vec @seeds) (respelled-seeds kb))]
              (cond
                (empty? back) v
                (>= round max-unmerge-rounds)
                (do (trove/log! {:level :warn :id ::unmerge-fixpoint
                                 :msg  (str "un-merge re-seeding did not converge in "
                                            max-unmerge-rounds " rounds; giving up")
                                 :data {:rounds round :seeds (count back)}})
                    v)
                ;; a given-back spelling is also a fact a descended equality is drawn
                ;; from, and the merge it rests on may have lost its route while the
                ;; spelling was superseded (`lost-derivation-seeds`)
                :else (do (rechain-seeds
                           kb (into back (lost-derivation-seeds
                                          kb (special/lost-descended-derivations kb back false))))
                          (recur (inc round))))))
          ;; a settle that throws leaves the carried sweeps as they were, and every later
          ;; write would resume a throwing sweep off them; their pairs go undecided instead
          (catch Throwable t
            (swap! (reasoning/clashes kb) dissoc :pending)
            (reset! (reasoning/arbitration-cursors kb) {})
            (throw t))
          (finally
            ;; a settle that throws while reading the re-arm queue leaves it populated,
            ;; and every later write would re-run the throwing sweep off it; the pairs
            ;; it held go un-rearmed instead
            (reset! (reasoning/sib-exc-dirty kb) #{})
            (publish-belief! held)))]
    (feed/deliver! kb)
    violated))

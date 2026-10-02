;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.discovery
  "The one nogood family a settle finds: the clashes argument preservation infers between
  a stored claim and a known-true claim no one stored, each with the most general
  contexts that read it whole, installed in the candidate index for every reader below a
  vantage to decide.  The memo `:preserved-clashes` carries a clash whose inputs did not
  move.  See docs/nmtms.md, \"The inherited-clash memo\"."
  (:require [taoensso.trove :as trove]
            [vaelii.impl.capabilities :as cap]
            [vaelii.impl.clashes :as clashes]
            [vaelii.impl.decide.inherited :as inherited]
            [vaelii.impl.inherit :as inherit]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.special :as special]
            [vaelii.impl.strength :as strength]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]))

(def ^:dynamic *whole-store-region?*
  "True while `recover` runs the settle that follows `rebuild-tms`, whose region is the
  whole store.  `preserving-entries` skips its store-wide sweep under it, and only
  when the region is also at least the store's sentex count (docs/nmtms.md, \"Which
  entry point the content came through\")."
  false)

(defn clear-inherited!
  "Empty the inherited clashes, so the discovery that follows reads no verdict: a pair one
  reader's verdict hides from the context that asks it is still a pair a reader below
  that context can read (docs/nmtms.md, \"A defeat is scoped to its vantage\")."
  [kb]
  (when (inherited/clear-inherited! kb)
    (res/clear-withdrawn! kb)
    (observe/note-change)))

(defn- install-inherited!
  "Record `ngs`, the nogoods a discovery found with their vantages, in the candidate index
  (`inherited/install-inherited!`).  Moves the change clock and empties the withdrawal cache,
  since every reader below a vantage now decides the nogood."
  [kb ngs]
  (when (inherited/install-inherited! kb ngs)
    (res/clear-withdrawn! kb)
    (observe/note-change)))

(defn inherited-losers
  "The members of the inherited clashes some vantage of theirs takes OUT
  (`res/verdicts`)."
  [kb]
  (into #{}
        (for [[ms {:keys [vantages]}] (inherited/inherited-clashes kb)
              v vantages
              :let [h (:defeat (get (res/verdicts kb v) ms))]
              :when h]
          h)))

(defn- ground-reading
  "`(fn [g k])` → what reader `k` (nil: the whole KB) sees of the grounds `s` could clash
  on, `g` being the contexts holding the other members: for a membership, the types held
  of its term in `g` that `k` proves disjoint from `s`'s type, and nothing for any other
  sentence.  Read off the taxonomy's cached closures; no check runs.  Two readers with
  equal readings convict `s` on the same grounds."
  [kb s]
  (let [tax (reasoning/taxonomy kb)
        sen (:sentence s)
        f   (nm/functor sen)
        as  (nm/args sen)]
    (if (and (sequential? sen) (symbol? f) (= 1 (count as)))
      (if (and (symbol? (first as)) (clashes/separations? tax))
        (let [held (group-by second (clashes/believed-memberships kb (first as)))]
          (fn [g k]
            (into #{}
                  (comp (mapcat held)
                        (map first)
                        (remove #(= f %))
                        (filter #(if k (tax/disjoint? tax f % k) (tax/disjoint? tax f %))))
                  g)))
        (constantly #{}))
      (constantly #{}))))

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
  to its vantage\").  A group holding only `s`'s context has that context as its maximum,
  so it adds only the readers below it that read a ground `s`'s context does not."
  [kb s groups]
  (let [tax     (reasoning/taxonomy kb)
        c       (:context s)
        reading (ground-reading kb s)]
    (into #{}
          (comp (map set)
                (filter seq)
                (mapcat (fn [g]
                          (let [cs    (into [c] (sort (disj g c)))
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
  "`s`'s inherited clash, or nil: `{:pred :askers :classes :class :nogoods}`.  The
  clashing claims are `inherit/clashing-claim`'s answers from `s`'s own context and from
  each vantage (`group-vantages` over `inherit/denial-contexts`): a vantage that sees a
  stronger reading than the own context reads decides from that reading.  `:askers` is
  every context asked, `:classes` the defeat-class of every member but `s`, `:class`
  `s`'s own, and `:nogoods` `inherited-nogoods`.  An answer of no clash is an entry with
  no nogoods while some claim would deny `s` in a reader that saw both, so the `genlCx`
  edge that makes that reader is asked again, and while an asker reads something
  withdrawn, so the settle that clears the withdrawal asks again."
  [kb s]
  (let [sen    (:sentence s)
        tms    (reasoning/tms kb)
        denial (inherit/denial-contexts kb sen)
        askers (cons (:context s) (sort (group-vantages kb s denial)))
        cs     (into [] (mapcat #(keep (fn [f] (f kb sen %))
                                       [inherit/clashing-claim inherit/converse-claim]))
                     askers)]
    (when (or (seq cs) (seq denial) (some #(seq (res/withdrawn-set kb %)) askers))
      {:pred    (nm/functor (kb/body-under-not sen))
       :askers  (set askers)
       :classes (into {} (map (juxt identity #(jtms/defeat-class tms %)))
                      (mapcat #(cons (:claim %) (:handles %)) cs))
       :class   (jtms/defeat-class tms (:id s))
       :nogoods (inherited-nogoods kb (:id s) sen cs)})))

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

(defn note-removed!
  "Record `sentex`, leaving the store, as `{handle sentence}` under `:left` in
  `:preserved-clashes` while the memo holds an entry, so the next `preserving-entries`
  reads what a handle without a record moved.  `preserving-nogoods` empties `:left` with
  the rest of the memo.  Called from `integrate/sentex-removed!`."
  [kb sentex]
  (let [memo (reasoning/preserved-clashes kb)]
    (when (seq (:entries @memo))
      (swap! memo assoc-in [:left (:id sentex)] (sx/sentence-of sentex)))))

(defn- preserving-moves
  "What the moved handles `moves` (`[handle region?]`, `region?` false for a withdrawal
  alone) re-open, as `[whole reached]`: the preserved predicates whose stored extent is
  re-asked (`inherit/moved-channels`' other channels, and a `genl` edge between
  predicates), and the stored facts a moved claim reaches
  (`inherit/claim-reach-extent`).  A claim reaches when it is believed and known-true,
  and, moved in the region, when `vantaged` holds its predicate: the claims of every
  class decide which vantages ask.  `narrow?` false re-opens the stored extent of every
  predicate a claim moves.  A handle with no record is read from `left`, the sentences
  `note-removed!` recorded: it is OUT, so it reaches as a claim moved in the region.  The
  `genl` closures are global, since what a moved edge re-opens is asked from every context
  that reads it."
  [kb pairs left moves vantaged narrow?]
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
         (if-let [sen (if-let [s (p/get-sentex recs h)] (sx/sentence-of s) (get left h))]
           (let [body  (kb/body-under-not sen)
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
  An entry is carried when the stamp (`preserving-stamp`) did not move, every handle in
  the region without a record has its sentence in `:left` (`note-removed!`), its
  predicate's extent was not re-opened, no moved claim reaches it
  (`preserving-moves`, over the region and `withdrawal-moves`), and its members hold the
  classes it recorded.  Every other entry, the region, and what the moves re-open are
  asked.  An entry whose candidate is OUT is kept and publishes nothing.  The region is
  what the touched window recorded since the last call's mark (`jtms/touched-since`), so a
  later pass of one settle asks only what the passes before it moved, and `region`, the
  settle's whole window, when the mark is from an earlier window.  Under
  `*whole-store-region?*` with a region the store's size, nothing is carried, no extent
  is swept, and the questions are the preserved predicates' stored extents (docs/nmtms.md,
  \"The inherited-clash memo\")."
  [kb pairs region prev stamp]
  (let [recs    (:records kb)
        tms     (reasoning/tms kb)
        handles (if-some [m (when *incremental-preserving* (:mark prev))]
                  (jtms/touched-since tms m)
                  @region)
        entries (:entries prev {})
        left    (:left prev {})
        whole?  (and *whole-store-region?* (>= (count handles) (cap/count-sentexes recs)))
        why     (cond whole?                          :whole-store
                      (not *incremental-preserving*)  :exhaustive
                      (not= stamp (:stamp prev))      :stamp
                      ;; nothing reads what a handle with no record and no `left` sentence moved
                      (some #(and (not (contains? left %)) (nil? (p/get-sentex recs %))) handles)
                      :retraction)
        fresh?  (some? why)
        [whole reached]
        (if whole?
          [#{} #{}]
          (preserving-moves kb pairs left
                            (concat (map #(vector % true) handles)
                                    (when-not fresh?
                                      (map #(vector % false) (withdrawal-moves kb (:seen prev)))))
                            (into #{} (map (comp :pred val)) entries)
                            *incremental-preserving*))
        kept    (if fresh?
                  {}
                  (into {} (filter (fn [[h e]] (and (not (contains? whole (:pred e)))
                                                    (not (contains? reached h))
                                                    (some? (p/get-sentex recs h))
                                                    (entry-live? tms e))))
                        entries))
        idx     (:index kb)
        preds   (into #{} (map first) pairs)
        ;; the whole store's claims are the preserved predicates' stored extents, read
        ;; off the index rather than off a record per region handle
        ask     (-> #{}
                    (into (keys entries))
                    (into (if whole? (mapcat #(reads/as-stored-with-functor idx %) preds) handles))
                    (into reached)
                    (into (mapcat #(reads/as-stored-with-functor idx %)) whole)
                    (->> (remove kept)))]
    (trove/log! {:level :debug :id ::asked
                 :data  {:region (count handles) :carried (count kept) :asked (count ask)
                         :fresh why}})
    ;; one memo over every question: belief does not move while they are asked
    (inherit/with-memo
      (into kept
            (keep (fn [h]
                    (when (jtms/in? tms h)
                      (when-let [s (p/get-sentex recs h)]
                        (when (contains? preds (nm/functor (kb/body-under-not (:sentence s))))
                          (when-let [e (preserving-entry kb s)] [h e]))))))
            ;; sorted so the queries run in a reproducible order
            (sort ask)))))

(defn preserving-nogoods
  "The clashes between a stored claim and a known-true claim argument preservation reads
  at its own tuple, as nogood maps (`inherited-nogoods`).  Resets `:preserved-clashes`,
  the memo `preserving-entries` carries.

  The members are the stored claim and the reading's reasons (`inherit/clashing-claim`'s
  `:claim` and `:handles`).  `:priority` is the rebuttal range, 1–2.  A candidate is asked
  from its own context and from every vantage (`preserving-entry`).  A body stored in both
  polarities is a negation pair (`negation-nogoods`, `decide/nogoods-at`), excluded by
  `clashing-claim`.  Behind an `empty?` on `kb`'s `:preserving` roster (docs/nmtms.md, \"What qualifies as a nogood\";
  docs/inherit.md).  The memo keeps a mark of the touched window taken before the
  questions (`jtms/touch-mark`), where the next call's region starts."
  [kb region]
  (let [pairs @(reasoning/preserving kb)]
    (if (empty? pairs)
      (do (reset! (reasoning/preserved-clashes kb) {}) #{})
      (let [tms     (reasoning/tms kb)
            mark    (jtms/touch-mark tms)
            stamp   (preserving-stamp kb)
            entries (preserving-entries kb (set (keys pairs)) region
                                        @(reasoning/preserved-clashes kb) stamp)]
        (reset! (reasoning/preserved-clashes kb)
                {:stamp   stamp
                 :mark    mark
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

(defn- discovery-view
  "`kb` as the inherited family's discovery reads it: the taxonomy with every handle
  withdrawn at its own context (`::special/own-out`) back at its network label, in a
  detached copy (`tax/detached-copy`) with a match, closure and withdrawal cache of its
  own, so a
  member an inherited verdict took out of the unscoped caches is read as the verdict-free
  network holds it, and the live caches learn nothing of the read.  The view holds a candidate
  index of its own, synced under the copy (`decide/synced`).  A reader's verdicts on
  the other families still apply at the askers, through the scoped reads.  `kb` itself
  while nothing is withdrawn at its own context."
  [kb]
  (let [tax (reasoning/taxonomy kb)
        out (::special/own-out @tax)]
    (if (empty? out)
      kb
      (let [tms  (reasoning/tms kb)
            copy (tax/detached-copy tax)]
        (tax/refresh-beliefs copy #(jtms/in? tms %) out)
        (assoc kb :reasoning (atom (assoc (reasoning/of kb)
                                          :taxonomy copy
                                          :nogood-candidates (atom @(reasoning/nogood-candidates kb))
                                          :matches (atom {})
                                          :closures (atom {})
                                          :withdrawn (atom {}))))))))

(defn discover-inherited!
  "Find the inherited clashes (`preserving-nogoods`) and record them in the candidate
  index for the readers (`install-inherited!`).  The index's inherited clashes are emptied
  first, and the discovery reads `discovery-view`, so it reads no inherited verdict.  Every
  clash found whose members the network believes is recorded with its vantages, where each
  reader at or below a vantage decides it for itself (`decide/nogoods-at`).  The network
  records no defeat (docs/nmtms.md, \"The runtime view\")."
  [kb region]
  (clear-inherited! kb)
  (let [tms (reasoning/tms kb)
        in? #(jtms/in? tms %)]
    (install-inherited! kb (into []
                                 (comp (filter #(every? in? (:nogood %)))
                                       (filter #(seq (:vantages %)))
                                       (distinct))
                                 (preserving-nogoods (discovery-view kb) region)))))

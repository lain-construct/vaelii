;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.decide
  "The nogoods a reader decides.  Each family keeps its rows of one candidate index
  (`:nogood-candidates`) and finds its nogoods at a reader; this namespace runs the
  families as one index, and decides each nogood from the classes the reader reads
  (`verdict`, `losers`).  `res/withdrawal` adds a reader's losers to what that reader
  withdraws.  See docs/nmtms.md, \"Nogoods decided at the reader\"."
  (:require [vaelii.impl.decide.arity :as arity]
            [vaelii.impl.decide.inherited :as inherited]
            [vaelii.impl.decide.membership :as membership]
            [vaelii.impl.decide.negation :as negation]
            [vaelii.impl.decide.related :as related]
            [vaelii.impl.decide.tuple :as tuple]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.strength :as strength]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]))

(defn write-view
  "The unscoped closures of `tax`, under their `tax/…-global` names, and `tax` itself as
  `:tax`: the taxonomy a family keeps its rows through, handed to `:note!`, `:replayed`
  and `:sync`.  The rows are a superset over every reader, kept where no reader exists,
  and each reader scopes what it reads; `:nogoods` is handed no view."
  [tax]
  {:tax                 tax
   :genls-global        (partial tax/genls-global tax)
   :specs-global        (partial tax/specs-global tax)
   :genl?-global        (partial tax/genl?-global tax)
   :genls-global-among  (partial tax/genls-global-among tax)
   :genls-global-union  (partial tax/genls-global-union tax)
   :specs-global-while  (partial tax/specs-global-while tax)
   :context-up-global   (partial tax/context-up-global tax)
   :context-down-global (partial tax/context-down-global tax)})

(def registry
  "Every family, each a map of the parts the candidate index runs, `w` a `write-view`:

  * `:note!` `(fn [kb w sx stored? replay?])`, at the store and removal choke points and
    for each record of a replay; absent for a family the settle installs.
  * `:replay` `(fn [] bindings)`, the var bindings a replay holds, and `:replayed` `(fn
    [kb w c] c)`, the rows the family computes once the replay has seen every record.
  * `:synced?` `(fn [tax c])` and `:sync` `(fn [w c] c)`: rows derived from the
    taxonomy, read again when it moved.
  * `:handles` `(fn [c])`, every handle some reader can read as a member, and
    `:watched` `(fn [c])`, the other handles a reading reads.
  * `:live?` `(fn [tax c])`: can some reader read a loser of the family?
  * `:unstamped`, the family's keys `stamp` leaves out, and `:stamp` `(fn [tax c])`, a
    stamp part of its own.
  * `:nogoods` `(fn [kb c up hidden?])`, the family's nogoods a reader with ancestor set
    `up` reads, each `{:members #{h} :marks #{h} :kind k}`.
  * `:pass`, a var holding a cache one pass of many readers shares (`with-pass`).

  The order is the order `nogoods-at` reads the families in."
  [tuple/converse-family arity/family negation/family tuple/marks-family membership/family
   related/family inherited/family])

(defn note-candidate!
  "Keep `:nogood-candidates` in step with the fact `sx` arriving (`stored?` true) or
  leaving.  Runs at the store primitive and the removal choke point, as
  `kb/note-opposed!` does.  A bulk load reads a stale index, so a nogood stored inside one
  bulk load enters only at the rebuild (`rebuild-candidates!`)."
  [kb sx stored?]
  (let [w (write-view (reasoning/taxonomy kb))]
    (doseq [{:keys [note!]} registry :when note!]
      (note! kb w sx stored? false))))

(defn offer!
  "Offer the stored facts `sxs` to the tuple candidates again (`tuple/offer!`), with
  `only` `:converse` to the converse candidates alone."
  ([kb sxs] (offer! kb sxs nil))
  ([kb sxs only]
   (let [w (write-view (reasoning/taxonomy kb))]
     (doseq [sx sxs] (tuple/offer! kb w sx only)))))

(defn rebuild-candidates!
  "Recompute `:nogood-candidates` from storage, for `recover`: every stored record is
  fetched once and offered to each family as arriving, under the bindings the families
  replay with, and each family then computes the rows it defers to the end of the
  replay."
  [kb]
  (let [cands (reasoning/nogood-candidates kb)
        recs  (:records kb)
        w     (write-view (reasoning/taxonomy kb))]
    (reset! cands {})
    (with-bindings (into {} (keep #(some-> (:replay %) (apply []))) registry)
      (doseq [h (p/sentex-ids recs)
              :let [sx (p/get-sentex recs h)]
              :when sx
              {:keys [note!]} registry
              :when note!]
        (note! kb w sx true true))
      (doseq [{:keys [replayed]} registry :when replayed]
        (swap! cands #(replayed kb w %))))))

(defn synced
  "The candidate index after each family's rows derived from the taxonomy are read again
  where it moved (`:synced?`, `:sync`)."
  [kb]
  (let [tax   (reasoning/taxonomy kb)
        cands (reasoning/nogood-candidates kb)]
    (reduce (fn [c {:keys [synced? sync]}]
              (if (or (nil? sync) (synced? tax c))
                c
                (swap! cands #(if (synced? tax %) % (sync (write-view tax) %)))))
            @cands registry)))

(defn candidate-handles
  "Every handle some reader can read as a nogood member of a family."
  [kb]
  (let [c (synced kb)]
    (into #{} (mapcat #((:handles %) c)) registry)))

(defn reach-handles
  "`candidate-handles` and the other handles the families read (`:watched`).  The
  candidate index part of `stamp` follows from these handles, their contexts and the
  taxonomy parts of `stamp`, so a reader whose ancestor set holds the context of no
  handle that entered or left this set reads the same nogoods before and after
  (`readings/reader-moves`)."
  [kb]
  (let [c (synced kb)]
    (into (candidate-handles kb) (mapcat #(some-> (:watched %) (apply [c]))) registry)))

(defn live?
  "Can some reader read a loser of a family?  A few map reads per family."
  [kb]
  (let [c (synced kb)]
    (boolean
     (when (seq c)
       (let [tax (reasoning/taxonomy kb)]
         (some #((:live? %) tax c) registry))))))

(defn stamp
  "What a reader's losers read besides the handles its watch names: the candidate index
  without each family's `:unstamped` keys, the declarations the taxonomy's flat caches
  hold and the contexts they are stated in (by identity, `tax/flat-contexts-key`), the
  `genl` generation, and each family's own `:stamp` part.  nil while `live?` is false.
  `res/withdrawal-stamp` carries it, so a mark, a binding, a candidate or a predicate
  edge arriving empties the per-reader cache, and reads no tuple."
  [kb]
  (when (live? kb)
    (let [tax (reasoning/taxonomy kb)
          c   (synced kb)]
      (into [(apply dissoc c (mapcat :unstamped registry))
             (tax/flat-contexts-key tax)
             (tax/relation-gen tax :genl)]
            (for [{f :stamp} registry :when f] (f tax c))))))

(defn nogoods-at
  "The nogoods every family reads at a reader with ancestor set `up` (`:nogoods`), each
  `{:members #{h} :marks #{h} :kind k}`, one per kind and member set with the marks of
  each.  A `:merge` nogood is one `losers` decides nothing of and watches, and a
  `:definitional?` one is read again once the reader withdraws a ground or an equality
  supporter.  `hidden?` is
  the reader's `except` filter, or nil.  Members are not tested for belief here."
  [kb up hidden?]
  (let [c (synced kb)]
    (vals (reduce (fn [m ng] (update m [(:kind ng) (:members ng)]
                                     #(if % (update % :marks into (:marks ng)) ng)))
                  {} (mapcat #((:nogoods %) kb c up hidden?) registry)))))

(defn pass-bindings
  "Each family's pass cache (`:pass`) for a span in which many readers decide over one
  taxonomy, as `with-bindings` takes them: a fresh one when `fresh?`, else the one bound
  already or a fresh one."
  [fresh?]
  (into {} (keep (fn [{v :pass}] (when v [v (or (when-not fresh? @v) (volatile! nil))])))
        registry))

(defmacro with-pass
  "`body` under `pass-bindings`."
  [fresh? & body]
  `(with-bindings (pass-bindings ~fresh?) ~@body))

(defn verdict
  "The verdict on nogood `members` from `class-of` (`handle -> defeat-class`):
  `{:defeat h}` for a unique weakest member that is defeasible, `:dilemma` for a
  defeasible minimum two members share, `:hard` for an all-`:monotonic` nogood
  (docs/reference.md, item 7 of \"The function\")."
  [class-of members]
  (let [ranked  (mapv (fn [h] [h (class-of h)]) members)
        floor   (reduce min (map #(strength/rank-of (peek %)) ranked))
        weakest (filterv #(= floor (strength/rank-of (peek %))) ranked)]
    (cond
      (not (strength/defeasible? (peek (first weakest)))) :hard
      (= 1 (count weakest))                               {:defeat (ffirst weakest)}
      :else                                               :dilemma)))

(defn losers
  "`{:losers #{h} :verdicts {members verdict} :watch #{h}}`: the members a reader with
  ancestor set `up` takes OUT, its verdict on every nogood it decides, and the handles the
  answer reads.  `seeds` is what the reader withdraws already (its `except` targets),
  `hidden?` its `except` filter or nil, and `belief-only` the argument
  `jtms/grounded-in-region` takes.  `reread` is `(fn [ngs provisional])` → the member sets of the
  definitional nogoods among `ngs` the reader still convicts when it withdraws
  `provisional` (`{:region :in}`).

  Rounds, as docs/reference.md item 8 states them: each round forces the seeds and the
  losers so far OUT, reads each member's class over that region
  (`jtms/classes-in-region`), decides every nogood whose members all stay believed, and
  adds the unique weakest defeasible members.  A round after the first decides again only
  the nogoods with a member in its region, which grows from round to round, and keeps the
  verdict before it on the rest.  A round whose new losers include a ground
  (`tax/derives-from?`) adds those alone.  A round whose region withdraws a set of grounds
  and equality supporters (`tax/equality-supporter?`) no earlier round's re-read was asked
  under asks `reread` of each definitional nogood before it is decided, and one the reader
  no longer reads stays dropped.  A re-read reads the reader's withdrawal only through the
  grounds, the equality partition (the spellings the reader retires) and the members,
  which stay believed while the nogood is decided, so a round withdrawing no other ground
  or equality supporter re-asks none.  Only an `except` seed withdraws an equality
  supporter: the equality relations are on the forced-monotonic roster, so no loser is one.
  A round that adds no loser ends the loop, and no round removes one.  `:verdicts` holds
  each loser's `{:defeat h}` from the round that applied it and the last round's `:hard`
  and `:dilemma` verdicts.  `:watch` is every member and every mark read, a merging pair's
  included, so a member's class moving re-decides the reader."
  [kb up seeds hidden? belief-only reread]
  (let [all   (vec (nogoods-at kb up hidden?))
        ngs   (filterv #(not= :merge (:kind %)) all)
        watch (into #{} (mapcat #(concat (:members %) (:marks %))) all)]
    (if (empty? ngs)
      {:losers #{} :verdicts {} :watch watch}
      (let [tms  (reasoning/tms kb)
            tax  (reasoning/taxonomy kb)
            sets (into [] (comp (map :members) (distinct)) ngs)
            defs (filterv :definitional? ngs)]
        ;; `vs` is the last round's verdict on each member set it read believed, `ds` the
        ;; `{:defeat h}` ones among them
        (loop [out #{} applied {} dropped #{} read-under #{} vs nil ds nil]
          (let [forced     (into (set seeds) out)
                {:keys [region in]} (when (seq forced)
                                      (jtms/grounded-in-region tms forced belief-only))
                region     (or region #{})
                in         (or in #{})
                classes    (delay (jtms/classes-in-region tms region in))
                withdrawn? #(and (contains? region %) (not (contains? in %)))
                class-of   #(if (contains? region %) (get @classes %) (jtms/defeat-class tms %))
                ;; the region only grows from round to round, so a member set with no
                ;; member in it reads the belief and classes it read the round before and
                ;; keeps that round's verdict
                redo       (if vs (filterv (fn [ms] (some #(contains? region %) ms)) sets) sets)
                [vs ds]    (let [[v d] (reduce
                                        (fn [[v d] ms]
                                          (if (and (not (contains? dropped ms))
                                                   (every? #(and (jtms/in? tms %) (not (withdrawn? %))) ms))
                                            (let [x (verdict class-of ms)]
                                              [(assoc! v ms x) (if (map? x) (assoc! d ms x) (dissoc! d ms))])
                                            [(dissoc! v ms) (dissoc! d ms)]))
                                        [(transient (or vs {})) (transient (or ds {}))] redo)]
                             [(persistent! v) (persistent! d)])
                live?      #(contains? vs (:members %))
                ;; a definitional clash is read through the grounds and the spellings the
                ;; reader elects, so it is re-read once this reader withdraws a ground or an
                ;; equality supporter, and again only when the withdrawn ones move
                grounds-out (when (some live? defs)
                              (into #{} (filter #(and (withdrawn? %)
                                                      (or (tax/derives-from? tax %)
                                                          (tax/equality-supporter? tax %))))
                                    region))
                asked      (when (and (seq grounds-out) (not= grounds-out read-under))
                             (filterv live? defs))
                kept       (when (seq asked) (reread asked {:region region :in in}))
                gone       (into #{} (comp (map :members) (remove #(contains? kept %))) asked)
                vs         (if (seq gone) (apply dissoc vs gone) vs)
                ds         (if (seq gone) (apply dissoc ds gone) ds)
                fresh      (into {} (remove #(contains? out (:defeat (val %)))) ds)
                grounds    (into {} (filter #(tax/derives-from? tax (:defeat (val %)))) fresh)
                add        (if (seq grounds) grounds fresh)]
            (if (empty? add)
              {:losers   out
               :verdicts (into applied (remove (comp map? val)) vs)
               :watch    watch}
              (recur (into out (map (comp :defeat val)) add)
                     (into applied add)
                     (into dropped gone)
                     (if asked grounds-out read-under)
                     vs
                     ds))))))))

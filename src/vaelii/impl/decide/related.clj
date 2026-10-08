;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.decide.related
  "The declarations over related types: a `disjoint` over two types one reaches the other
  of through `genl`, a cover naming a part a `disjoint` separates from its whole, and an
  `orthogonal` over two types a `genl` edge or a separation contradicts.  See
  docs/reference.md, decision 8."
  (:require [vaelii.impl.caches :as caches]
            [vaelii.impl.journal :as journal]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]))

;; ---- declarations over related types -------------------------------------------
;;
;; A `disjoint` over two types one reaches the other of through `genl` is a one-member hard
;; clash of the declaration, and a cover naming a part the `disjoint` separates from its
;; whole a two-member one of the cover and the declaration (docs/reference.md, decision 8).
;; Both are found from the declarations' own arguments, read off the argument trie: the
;; `disjoint`s naming a type at argument 1 or 2, and the covers naming a whole at argument
;; 1.  `:related-dj` keeps the `disjoint`s whose arguments are related over the unscoped
;; `genl` closure, read again for the declarations naming a type at or below the lower end
;; of an edge moved since the generation `::genl-seen` (`tax/moves-since`).
;; `:cover-pairs` keeps each `#{cover disjoint}` whose `disjoint` separates the whole from
;; a part, read off the index when either side arrives (`pairs-of`), with each member's
;; pairs under `::cover-of`.
;;
;; An `(orthogonal a b)` says the two types are not disjoint and neither is a `genl` of the
;; other.  It exempts nothing, so what contradicts it is a `genl` edge between the two, one
;; type named twice, or a separation of the two or of two supertypes: a one-member clash of
;; the declaration, as a `disjoint` over related types is.  A fact whose functor the
;; unscoped `genl` closure places under `orthogonal` states one too
;; (`(genl siblingDisjointException orthogonal)`), and its own exemption from the
;; separation marks (`tax/exemption`) is the one a reader reads.  The stored ones are read
;; off the extents and the argument trie of those functors (`orthogonal-functors`), and
;; `:related-orth` keeps those whose pair some reader can read contradicted — related over
;; the unscoped `genl` closure, or separated by `disjointness-test` with no exemption
;; read.  One is read when it is stored, again with the `disjoint`s when an edge moves its
;; argument's ancestor set or its functor's place under `orthogonal`, and again when the
;; settle relabels a separation declaration over a type at or above an argument
;; (`reread-separated!`).

(def ^:private cover-functors
  "The functors of a whole-and-parts declaration (`tax/installed-edges`)."
  '[covering partition separating])

(defn- disjoint-args
  "`[a b]` for a stored fact `(disjoint a b)` over two distinct plain symbols, else nil."
  [sx]
  (let [s (:sentence sx)]
    (when (and (nil? (:antecedent sx)) (seq? s) (= 3 (count s)) (= 'disjoint (first s)))
      (let [[_ a b] s]
        (when (and (sx/plain-symbol? a) (sx/plain-symbol? b) (not= a b)) [a b])))))

(defn- cover-args
  "`[whole #{part}]` for a stored `covering`, `separating` or `partition` fact, else nil."
  [sx]
  (let [s (:sentence sx)]
    (when (and (nil? (:antecedent sx)) (seq? s) (some #{(first s)} cover-functors))
      (when-let [[w ps] (tax/cover-parts s)] [w (set ps)]))))

(defn- orthogonal-functors
  "`orthogonal` and every predicate the unscoped `genl` closure (the write view `w`) places
  under it, in content order."
  [w]
  (into (sorted-set) (filter symbol?) (conj ((:specs-global w) 'orthogonal) 'orthogonal)))

(defn- orthogonal-args
  "`[a b]` for a stored fact `(f a b)` over two plain symbols whose functor `f` states an
  `orthogonal` (`orthogonal-functors`), else nil.  `a` and `b` may be one symbol: a type
  subsumes itself, so that declaration is contradicted outright."
  [w sx]
  (let [s (:sentence sx)]
    (when (and (nil? (:antecedent sx)) (seq? s) (= 3 (count s)) (symbol? (first s))
               (or (= 'orthogonal (first s)) (contains? ((:specs-global w) 'orthogonal) (first s))))
      (let [[_ a b] s]
        (when (and (sx/plain-symbol? a) (sx/plain-symbol? b)) [a b])))))

;; ---- the stored declarations, read off the index ---------------------------------

(defn- read-args
  "`{h args}` for the stored records of the handles `hs` that `args-of` reads."
  [kb args-of hs]
  (let [recs (:records kb)]
    (into {} (keep (fn [h] (when-let [ab (some-> (p/get-sentex recs h) args-of)] [h ab]))) hs)))

(defn- naming
  "The handles of the stored facts of the functors `fs` naming a type of `ts` at one of
  the argument positions `ps` (`reads/as-stored-with-args`), or every stored fact of
  them (`reads/as-stored-with-functor`) when that set is the smaller."
  [kb fs ps ts]
  (let [idx (:index kb)
        all (transduce (map #(reads/stored-count-with-functor idx %)) + fs)]
    (if (<= all (* (count ps) (count ts)))
      (into #{} (mapcat #(reads/as-stored-with-functor idx %)) fs)
      (into #{} (for [f fs, pos ps, t ts, h (reads/as-stored-with-args idx f [[pos t]])] h)))))

(defn- disjoints
  "`{h [a b]}` of the stored `disjoint`s naming a type of `ts`, or every one when `ts` is
  nil."
  [kb ts]
  (read-args kb disjoint-args
             (if (nil? ts)
               (reads/as-stored-with-functor (:index kb) 'disjoint)
               (naming kb ['disjoint] [1 2] ts))))

(defn- orthogonals
  "`{h [a b]}` of the stored facts stating an `orthogonal` (`orthogonal-args`) that name a
  type of `ts`, or every one when `ts` is nil."
  [kb w ts]
  (let [fs (orthogonal-functors w)]
    (read-args kb #(orthogonal-args w %)
               (if (nil? ts)
                 (into #{} (mapcat #(reads/as-stored-with-functor (:index kb) %)) fs)
                 (naming kb fs [1 2] ts)))))

(defn- related?
  "Does one of the types `a`, `b` reach the other over the unscoped `genl` closure (the
  write view `w`)?"
  [w [a b]]
  (let [genl? (:genl?-global w)] (or (genl? a b) (genl? b a))))

(defn- separates-part?
  "Does the `disjoint` over `[a b]` separate cover `[w ps]`'s whole from one of its parts?"
  [[w ps] [a b]]
  (or (and (= a w) (contains? ps b)) (and (= b w) (contains? ps a))))

(defn- pairs-of
  "The cover pairs, each `#{cover disjoint}`, the stored fact `sx` is a side of, the other
  side read off the index: a `disjoint`'s covers have one of its arguments as their
  whole, and a cover's `disjoint`s name its whole.  Empty for any other fact."
  [kb sx]
  (let [h (:id sx)]
    (if-let [ab (disjoint-args sx)]
      (into #{} (keep (fn [[cv wp]] (when (separates-part? wp ab) (hash-set cv h))))
            (read-args kb cover-args (naming kb cover-functors [1] ab)))
      (if-let [[whole _ :as wp] (cover-args sx)]
        (into #{} (keep (fn [[d ab]] (when (separates-part? wp ab) (hash-set h d))))
              (disjoints kb [whole]))
        #{}))))

(defn- every-pair
  "Every cover pair the store holds: each stored cover's (`pairs-of`)."
  [kb]
  (let [recs (:records kb)]
    (into #{} (comp (mapcat #(reads/as-stored-with-functor (:index kb) %))
                    (keep #(p/get-sentex recs %))
                    (mapcat #(pairs-of kb %)))
          cover-functors)))

(defn- noted
  "`c` with the handles `hs` journaled (`journal/note`) and queued under `::moved` for the
  settle to place their nogoods again (`take-moved!`)."
  [c hs]
  (-> (journal/note c hs) (update ::moved (fnil into #{}) hs)))

(defn- add-cover-pairs
  "`c` with the cover pairs `prs` under `:cover-pairs` and each member's under
  `::cover-of`."
  [c prs]
  (reduce (fn [c pr]
            (if (contains? (:cover-pairs c) pr)
              c
              (as-> c c
                (update c :cover-pairs (fnil conj #{}) pr)
                (reduce #(update-in %1 [::cover-of %2] (fnil conj #{}) pr) c pr)
                (noted c pr))))
          c prs))

(defn- drop-cover-pairs
  "`c` with every cover pair holding `h` removed."
  [c h]
  (reduce (fn [c pr]
            (as-> c c
              (update c :cover-pairs disj pr)
              (reduce (fn [c x] (let [left (disj (get-in c [::cover-of x]) pr)]
                                  (if (seq left)
                                    (assoc-in c [::cover-of x] left)
                                    (update c ::cover-of dissoc x))))
                      c pr)
              (noted c pr)))
          c (get-in c [::cover-of h])))

(defn- contradicted-somewhere?
  "Can some reader read the `orthogonal` over `[a b]` contradicted?  One type twice, a
  `genl` edge between the two over the unscoped closure, or a separation
  `disjointness-test` reads with no exception exempting it — the superset
  over every reader that the placements scope."
  [w [a b]]
  (or (= a b)
      (related? w [a b])
      (boolean ((tax/disjointness-test (:tax w) a nil (constantly false)) b))))

(defn- orthogonals-under
  "`{h [a b]}` of the stored `orthogonal`s with an argument at or below one of the types
  `ends` over the unscoped `genl` closure: those a separation over `ends` can contradict
  or exempt.  Reads the stored ones whole, or those naming a specialization of `ends`,
  whichever is fewer."
  [kb w ends]
  (when (seq ends)
    (let [idx  (:index kb)
          ends (set ends)
          n    (transduce (map #(reads/stored-count-with-functor idx %)) + (orthogonal-functors w))]
      (if (< n (* 4 (count ends)))
        (into {} (filter (fn [[_ ab]] (some #(some ends ((:genls-global w) %)) ab)))
              (orthogonals kb w nil))
        (orthogonals kb w (into #{} (mapcat (:specs-global w)) ends))))))

(defn- reread-orthogonals
  "`c` with each `orthogonal` of `orths` (`{h [a b]}`, `[a b]` nil for a fact no longer
  stating one) in `:related-orth` exactly when it is contradicted somewhere, every one
  journaled."
  [w c orths]
  (-> c
      (assoc :related-orth
             (reduce-kv (fn [r h ab] (if (and ab (contradicted-somewhere? w ab)) (conj r h) (disj r h)))
                        (or (:related-orth c) #{}) orths))
      (journal/note (keys orths))))

(defn kind-of
  "The kind of the related-types nogood over the member handles `ms`, read off their
  sentences through the write view `w`: `:disjoint` for one `disjoint`, `:orthogonal` for
  one fact stating an `orthogonal` (`orthogonal-args`), `:cover` for a cover beside a
  `disjoint`, else nil."
  [w recs ms]
  (let [sxs (keep #(p/get-sentex recs %) ms)]
    (when (= (count sxs) (count ms))
      (case (count sxs)
        1 (let [[sx] sxs]
            (cond (disjoint-args sx)     :disjoint
                  (orthogonal-args w sx) :orthogonal))
        2 (when (and (some disjoint-args sxs) (some cover-args sxs)) :cover)
        nil))))

(defn- note-declaration!
  "Keep the related-types rows in step with the fact `sx` arriving (`stored?`) or leaving.
  A `disjoint` enters `:related-dj` when `::genl-seen` holds a generation it is read under
  (`sync-related` reads every one otherwise) and its arguments are related, and leaves it
  with its record; a `disjoint` or a cover arriving pairs with the stored other side it
  names (`pairs-of`), and one leaving takes its pairs with it.  A fact stating an
  `orthogonal` enters `:related-orth` likewise when it is contradicted somewhere, and a
  `siblingDisjointException` either way queues the contradicted `orthogonal`s with an
  argument at or below one of its own: its exemption moves where they are placed.  A
  `(contradicts …)` leaving queues its members for the settle to place again
  (`take-moved!`): a `genlCx` edge under the placement can have left with it.  Reads
  nothing for any other fact."
  [kb w sx stored?]
  (let [cands (reasoning/nogood-candidates kb)
        h     (:id sx)
        f     (nm/functor (:sentence sx))]
    (cond
      (and (not stored?) (= 'contradicts f))
      (let [hs (into #{} (keep sx/handle-id) (rest (:sentence sx)))]
        (when (kind-of w (:records kb) hs)
          (swap! cands update ::moved (fnil into #{}) hs)))

      (disjoint-args sx)
      (let [ab  (disjoint-args sx)
            prs (when stored? (pairs-of kb sx))]
        (swap! cands (fn [c]
                       (cond
                         (not stored?)
                         (-> c (update :related-dj #(some-> % (disj h))) (noted [h])
                             (drop-cover-pairs h))

                         (and (::genl-seen c) (related? w ab))
                         (-> c (update :related-dj (fnil conj #{}) h) (noted [h])
                             (add-cover-pairs prs))

                         :else (add-cover-pairs c prs)))))

      (cover-args sx)
      (let [prs (when stored? (pairs-of kb sx))]
        (when (or (seq prs) (contains? (::cover-of @cands) h))
          (swap! cands #(if stored? (add-cover-pairs % prs) (drop-cover-pairs % h)))))

      :else
      (let [ab (orthogonal-args w sx)]
        (when (or ab (and (not stored?) (contains? (:related-orth @cands) h)))
          (let [sib (when (= 'siblingDisjointException f)
                      (keys (orthogonals-under kb w ab)))]
            (swap! cands
                   (fn [c]
                     (let [c (if stored?
                               (if (and (::genl-seen c) (contradicted-somewhere? w ab))
                                 (-> c (update :related-orth (fnil conj #{}) h) (noted [h]))
                                 c)
                               (-> c (update :related-orth #(some-> % (disj h))) (noted [h])))]
                       (noted c (filter #(contains? (:related-orth c) %) sib)))))))))))

(defn- related-synced?
  "Is `c`'s `:related-dj` and `:related-orth` read under the `genl` generation as it
  stands?"
  [tax c]
  (= (tax/relation-gen tax :genl) (::genl-seen c)))

(defn- sync-related
  "`c` with `:related-dj` and `:related-orth` read again under the `genl` closure as it
  stands: every declaration when none was read or the relation was rebuilt from nothing,
  else those naming a type at or below the lower end of an edge that moved
  (`tax/moves-since`), since no other type's closure moved, the facts of a predicate at or
  below such a lower end, which the move can put under `orthogonal`, and the contradicted
  `orthogonal`s, whose functor it can take out.  The ones related or contradicted before
  or after are queued, since an edge moving moves their routes.  Reads the store only
  while it holds a `disjoint` or an `orthogonal`."
  [kb w c]
  (let [tax   (:tax w)
        idx   (:index kb)
        g     (tax/relation-gen tax :genl)
        seen  (::genl-seen c)
        full  (or (nil? seen) (< g seen))
        fs    (orthogonal-functors w)
        none? (and (zero? (reads/stored-count-with-functor idx 'disjoint))
                   (empty? (:related-orth c))
                   (not-any? #(pos? (reads/stored-count-with-functor idx %)) fs))]
    (if none?
      (assoc c :related-dj #{} ::genl-seen g)
      (let [types (when-not full
                    (into #{} (mapcat (:specs-global w)) (tax/moves-since tax :genl seen)))
            djs   (disjoints kb types)
            ;; the facts of a predicate the move can put under `orthogonal` or take out
            ;; from under it: those stored, and those `:related-orth` holds
            under (when-not full
                    (let [recs (:records kb)
                          fn-of #(some-> (p/get-sentex recs %) :sentence nm/functor)]
                      (-> (into #{} (comp (filter #(contains? types %))
                                          (mapcat #(reads/as-stored-with-functor idx %)))
                                fs)
                          (into (filter #(contains? types (fn-of %))) (:related-orth c)))))
            orths (if full
                    (orthogonals kb w nil)
                    (merge (zipmap under (repeat nil))
                           (read-args kb #(orthogonal-args w %) under)
                           (orthogonals kb w types)))
            rel   (reduce-kv (fn [r h ab] (if (related? w ab) (conj r h) (disj r h)))
                             (if full #{} (or (:related-dj c) #{}))
                             djs)
            old   c
            c     (as-> c c
                    (assoc c :related-dj rel ::genl-seen g)
                    (cond-> c full (assoc :related-orth #{}))
                    (reread-orthogonals w c orths)
                    (journal/note c (if full (concat (:related-dj old) (keys djs)) (keys djs))))
            held? (fn [c h] (or (contains? (:related-dj c) h) (contains? (:related-orth c) h)))]
        (update c ::moved (fnil into #{})
                (filter #(or (held? c %) (held? old %)))
                (concat (when full (concat (:related-dj old) (:related-orth old)))
                        (keys djs) (keys orths)))))))

(defn reread-separated!
  "Read again whether each stored `orthogonal` with an argument at or below one of the
  types `ends` is contradicted somewhere, and return those contradicted before or after:
  the ones whose routes a separation over `ends` moving can move.  The settle calls this
  for the separation declarations it relabels (`chain/place-related!`)."
  [kb w ends]
  (let [orths (orthogonals-under kb w ends)]
    (when (seq orths)
      (let [cands     (reasoning/nogood-candidates kb)
            [old new] (swap-vals! cands #(reread-orthogonals w % orths))]
        (filterv #(or (contains? (:related-orth old) %) (contains? (:related-orth new) %))
                 (sort (keys orths)))))))

(defn moved?
  "Has the index queued a declaration whose nogoods the settle places again
  (`take-moved!`)?"
  [c]
  (boolean (seq (::moved c))))

(defn orthogonals?
  "Does the store hold a fact of `orthogonal` or of a predicate under it, which a
  separation declaration the settle relabels can contradict (`reread-separated!`)?
  Count reads."
  [kb w]
  (boolean (some #(pos? (reads/stored-count-with-functor (:index kb) %)) (orthogonal-functors w))))

(defn take-moved!
  "The declarations whose related-types nogoods moved since the last call, and the queue
  emptied (`noted`)."
  [kb]
  (let [[old _] (swap-vals! (reasoning/nogood-candidates kb) dissoc ::moved)]
    (::moved old #{})))

(defn nogoods-holding
  "The related-types nogoods the candidate index `c` keeps with the declaration `h` among
  their members, each `{:members #{h} :kind k}`: a `disjoint` of `:related-dj`, kind
  `:disjoint`; each cover pair holding `h`, kind `:cover`; and an `orthogonal` of
  `:related-orth`, kind `:orthogonal`."
  [c h]
  (cond-> (mapv (fn [pr] {:members pr :kind :cover}) (get-in c [::cover-of h]))
    (contains? (:related-dj c) h)   (conj {:members #{h} :kind :disjoint})
    (contains? (:related-orth c) h) (conj {:members #{h} :kind :orthogonal})))

(defn routes
  "Each way the unscoped taxonomy convicts the related-types nogood `ng`, as
  `{:links [[sub super]] :keys #{k} :pair [x y]}` (`tax/separation-routes`' shape): a
  `disjoint` over `a` and `b`, the subsumption between them in each direction the
  closure holds; a cover pair, none; an `orthogonal` over one type twice, none, and
  otherwise the subsumption between the two in each direction the closure holds and
  each separation of the two (`tax/separation-routes`).  A fact whose functor `f` is a
  `genl` of `orthogonal` adds the subsumption `f` to `orthogonal` to each route.  `w` is
  `decide/write-view`'s."
  [w recs {:keys [members kind]}]
  (let [sx    (p/get-sentex recs (first members))
        genl? (:genl?-global w)
        links (fn [[a b]] (cond-> []
                            (genl? a b) (conj {:links [[a b]]})
                            (genl? b a) (conj {:links [[b a]]})))]
    (case kind
      :disjoint   (some-> (disjoint-args sx) links)
      :cover      [{:links []}]
      :orthogonal (when-let [[a b :as ab] (orthogonal-args w sx)]
                    (let [f  (nm/functor (:sentence sx))
                          rs (if (= a b)
                               [{:links []}]
                               (concat (links ab) (tax/separation-routes (:tax w) a b)))]
                      (if (= 'orthogonal f)
                        rs
                        (map #(update % :links (fnil conj []) [f 'orthogonal]) rs))))
      nil)))

(defn exempt-at?
  "Does a reader with ancestor set `up` read no conviction of the `orthogonal` nogood
  `members`: one declaration over two distinct types no `genl` edge relates over the
  unscoped closure (`w`, `decide/write-view`) and `tax/disjoint?` over `up` does not
  separate.  A `siblingDisjointException` the reader sees removes a mark separation its
  placement reads, as for a membership nogood (`membership/exempt-at?`).  False for any
  other nogood."
  [w recs members up]
  (boolean
   (when (= 1 (count members))
     (when-let [[a b :as ab] (some->> (p/get-sentex recs (first members)) (orthogonal-args w))]
       (let [tax (:tax w)]
         (and (not= a b) (not (related? w ab))
              (not (tax/disjoint? tax a b up)) (not (tax/disjoint? tax b a up))))))))

(def family
  "The related-types family's entry in `decide/registry`.  It keeps no stored declaration:
  recover reads the cover pairs off the cover extents (`every-pair`) and leaves
  `::genl-seen` unread, so the first read reads every declaration (`sync-related`).  Each
  nogood of it is placed as a conclusion (`chain/place-related!`)."
  {:note!     (fn [kb w sx stored?] (note-declaration! kb w sx stored?))
   :recovered (fn [kb _] (swap! (reasoning/nogood-candidates kb) add-cover-pairs (every-pair kb)))
   :synced?   related-synced?
   :sync      sync-related
   :handles   (fn [c] (concat (:related-dj c) (apply concat (:cover-pairs c)) (:related-orth c)))
   :holds?    (fn [c h] (or (contains? (:related-dj c) h) (contains? (::cover-of c) h)
                            (contains? (:related-orth c) h)))})

;; ---- derived state (docs/caches.md, "The derived-state register") ----------------

(caches/register-derived
 {:id :N6 :label "Related declaration candidates" :kind :cache :keyed-by :handle
  :reads [:index :records :T1 :J5]
  :retired-by {:stored :K :removed :K :respelled :K :edge :K :declared :K :edge-belief :K
               :settle-pass :K :recover :R :image-install :R}
  :computed :read :imaged? :state
  :at [[:nogood-candidates :related-dj] [:nogood-candidates :related-orth]
       [:nogood-candidates ::genl-seen] [:nogood-candidates :cover-pairs]
       [:nogood-candidates ::cover-of] [:nogood-candidates ::moved]]
  :bound "one handle per stored `disjoint` and per stored fact stating an `orthogonal`, and one pair per stored cover and `disjoint` separating its whole from a part"
  :note "the `disjoint`s over related types, the contradicted `orthogonal`s and the cover pairs, read off the argument trie and the extents; synced at a read by the relation moves (J5), and an orthogonal read again by the separation declarations a settle relabels"})

;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.decide.related
  "The declarations over related types: a `disjoint` over two types one reaches the other
  of through `genl`, a cover naming a part a `disjoint` separates from its whole, and an
  `orthogonal` over two types a separation or a `genl` edge contradicts.  See
  docs/reference.md, decision 8."
  (:require [vaelii.impl.protocols :as p]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]))

;; ---- declarations over related types -------------------------------------------
;;
;; A `disjoint` over two types one reaches the other of through `genl` is a one-member hard
;; clash of the declaration, and a cover naming a part the `disjoint` separates from its
;; whole a two-member one of the cover and the declaration (docs/reference.md, decision 8).
;; Both are found from the declarations' own arguments.  `::djs` keeps every stored
;; `(disjoint a b)` over two symbols, `::dj-by-type` its handles by argument, and
;; `:related-dj` those whose arguments are related over the unscoped `genl` closure, read
;; again for the declarations naming a type at or below the lower end of a moved edge
;; (`tax/moves-since`); `::cvs` keeps every stored cover by handle, `::cv-by-whole` by its
;; whole, and `:cover-pairs` each `#{cover disjoint}` whose `disjoint` separates the whole
;; from a part.
;;
;; An `(orthogonal a b)` says the two types may overlap and neither subsumes the other, so a
;; separation of the pair, however it is reached, and a `genl` edge between the two
;; contradict it: a one-member clash of the declaration, as a `disjoint` over related types
;; is.  `::orths` keeps every stored `orthogonal` by handle, and `:related-orth` those whose
;; pair some reader can read contradicted — related over the unscoped `genl` closure, or
;; separated by `disjointness-test` with no exception read — under the `genl` generation and
;; `tax/separation-stamp` it was read at (`::orth-seen`).  The `orthogonal`s are few, so a
;; move of either reads every one again rather than tracking which a move touched.

(defn- disjoint-args
  "`[a b]` for a stored fact `(disjoint a b)` over two distinct plain symbols, else nil."
  [sx]
  (let [s (:sentence sx)]
    (when (and (nil? (:antecedent sx)) (seq? s) (= 3 (count s)) (= 'disjoint (first s)))
      (let [[_ a b] s]
        (when (and (sx/plain-symbol? a) (sx/plain-symbol? b) (not= a b)) [a b])))))

(defn- cover-args
  "`[whole #{part}]` for a stored cover, `separating` or `partition` fact, else nil."
  [sx]
  (when (nil? (:antecedent sx))
    (when-let [[w ps] (tax/cover-parts (:sentence sx))] [w (set ps)])))

(defn- orthogonal-args
  "`[a b]` for a stored fact `(orthogonal a b)` over two plain symbols, else nil.  `a` and
  `b` may be one symbol: a type subsumes itself, so that declaration is contradicted
  outright."
  [sx]
  (let [s (:sentence sx)]
    (when (and (nil? (:antecedent sx)) (seq? s) (= 3 (count s)) (= 'orthogonal (first s)))
      (let [[_ a b] s]
        (when (and (sx/plain-symbol? a) (sx/plain-symbol? b)) [a b])))))

(defn- related?
  "Does one of the types `a`, `b` reach the other over the unscoped `genl` closure (the
  write view `w`)?"
  [w [a b]]
  (let [genl? (:genl?-global w)] (or (genl? a b) (genl? b a))))

(defn- separates-part?
  "Does the `disjoint` over `[a b]` separate cover `[w ps]`'s whole from one of its parts?"
  [[w ps] [a b]]
  (or (and (= a w) (contains? ps b)) (and (= b w) (contains? ps a))))

(defn- drop-cover-pairs
  "`c` with every cover pair holding `h` removed."
  [c h]
  (cond-> c
    (some #(contains? % h) (:cover-pairs c))
    (update :cover-pairs #(into #{} (remove (fn [pr] (contains? pr h))) %))))

(defn- note-declaration
  "`c` with the stored fact `sx` (`stored?`) or its removal read into the related-types
  rows: a `disjoint` enters `::djs`, and `:related-dj` when `::dj-seen` holds a generation
  it is read under (`sync-related` reads every one otherwise); a cover enters `::cvs`; and
  either pairs with the stored other side it names."
  [w c sx stored?]
  (let [h (:id sx)]
    (if-let [[a b :as ab] (disjoint-args sx)]
      (if stored?
        (let [c (-> c
                    (assoc-in [::djs h] ab)
                    (update-in [::dj-by-type a] (fnil conj #{}) h)
                    (update-in [::dj-by-type b] (fnil conj #{}) h))
              c (if (and (::dj-seen c) (related? w ab))
                  (update c :related-dj (fnil conj #{}) h)
                  c)
              ps (for [t [a b], cv (get-in c [::cv-by-whole t])
                       :when (separates-part? (get-in c [::cvs cv]) ab)]
                   (hash-set cv h))]
          (cond-> c (seq ps) (update :cover-pairs (fnil into #{}) ps)))
        (-> c
            (update ::djs dissoc h)
            (update-in [::dj-by-type a] #(some-> % (disj h)))
            (update-in [::dj-by-type b] #(some-> % (disj h)))
            (update :related-dj #(some-> % (disj h)))
            (drop-cover-pairs h)))
      (if-let [[whole _ :as wp] (cover-args sx)]
        (if stored?
          (let [c  (-> c
                       (assoc-in [::cvs h] wp)
                       (update-in [::cv-by-whole whole] (fnil conj #{}) h))
                prs (for [d (get-in c [::dj-by-type whole])
                          :when (separates-part? wp (get-in c [::djs d]))]
                      (hash-set h d))]
            (cond-> c (seq prs) (update :cover-pairs (fnil into #{}) prs)))
          (-> c
              (update ::cvs dissoc h)
              (update-in [::cv-by-whole whole] #(some-> % (disj h)))
              (drop-cover-pairs h)))
        c))))

(defn- note-orthogonal
  "`c` with the stored `orthogonal` `sx` (`stored?`) or its removal read into `::orths`,
  and `::orth-seen` cleared, so `sync-orthogonal` reads every one again."
  [c sx stored?]
  (let [h (:id sx)]
    (-> (if stored?
          (assoc-in c [::orths h] (orthogonal-args sx))
          (-> c
              (update ::orths dissoc h)
              (update :related-orth #(some-> % (disj h)))))
        (dissoc ::orth-seen))))

(defn- note-declaration!
  "Keep the related-types rows in step with the fact `sx` arriving (`stored?`) or leaving
  (`note-declaration`).  Reads nothing for any other fact."
  [kb w sx stored?]
  (cond
    (or (disjoint-args sx) (cover-args sx))
    (swap! (reasoning/nogood-candidates kb) #(note-declaration w % sx stored?))

    (orthogonal-args sx)
    (swap! (reasoning/nogood-candidates kb) #(note-orthogonal % sx stored?))))

(defn- orth-key
  "What `:related-orth` is read under: the `genl` generation and the separations."
  [tax]
  [(tax/relation-gen tax :genl) (tax/separation-stamp tax)])

(defn- related-synced?
  "Is `c`'s `:related-dj` read under the `genl` generation as it stands, and its
  `:related-orth` under that generation and the separations as they stand?"
  [tax c]
  (and (or (empty? (::djs c)) (= (tax/relation-gen tax :genl) (::dj-seen c)))
       (or (empty? (::orths c)) (= (orth-key tax) (::orth-seen c)))))

(defn- contradicted-somewhere?
  "Can some reader read the `orthogonal` over `[a b]` contradicted?  One type twice, a
  `genl` edge between the two over the unscoped closure, or a separation
  `disjointness-test` reads with no `orthogonal` exempting it — the superset
  over every reader that `related-nogoods` scopes."
  [w [a b]]
  (or (= a b)
      (related? w [a b])
      (boolean ((tax/disjointness-test (:tax w) a nil (constantly false)) b))))

(defn- sync-orthogonal
  "`c` with `:related-orth` read again over every stored `orthogonal`, unless it is read
  under the `genl` generation and the separations as they stand."
  [w c]
  (let [k (orth-key (:tax w))]
    (cond
      (empty? (::orths c))  (-> c (dissoc :related-orth) (assoc ::orth-seen k))
      (= k (::orth-seen c)) c
      :else (assoc c
                   :related-orth (into #{}
                                       (keep (fn [[h ab]] (when (contradicted-somewhere? w ab) h)))
                                       (::orths c))
                   ::orth-seen k))))

(defn- sync-disjoint
  "`c` with `:related-dj` read again under the `genl` closure as it stands: every
  `disjoint` when none was read or the relation was rebuilt from nothing, else those
  naming a type at or below the lower end of an edge that moved (`tax/moves-since`),
  since no other type's closure moved."
  [w c]
  (let [tax  (:tax w)
        g    (tax/relation-gen tax :genl)
        seen (::dj-seen c)
        full (or (nil? seen) (< g seen))
        hs   (if full
               (keys (::djs c))
               (into #{}
                     (comp (mapcat (:specs-global w))
                           (mapcat #(get-in c [::dj-by-type %])))
                     (tax/moves-since tax :genl seen)))
        rel  (reduce (fn [r h]
                       (if-let [ab (get-in c [::djs h])]
                         (if (related? w ab) (conj r h) (disj r h))
                         r))
                     (if full #{} (or (:related-dj c) #{}))
                     hs)]
    (assoc c :related-dj rel ::dj-seen g)))

(defn- sync-related
  "`c` with `:related-dj` and `:related-orth` read again where they moved."
  [w c]
  (->> c (sync-disjoint w) (sync-orthogonal w)))

(defn- related-nogoods
  "The related-types clashes a reader with ancestor set `up` reads, among the declarations
  it sees, in `up` and not `hidden?`: a `disjoint` of `:related-dj` whose arguments one
  reaches the other of through the `genl` edges stated in `up` (`tax/genl-asserted-in?`),
  `{:members #{h} :marks #{} :kind :disjoint}`, a cover pair,
  `{:members #{cover disjoint} :marks #{} :kind :cover}`, and an `orthogonal` of
  `:related-orth` over one type twice, over two types the `genl` edges stated in `up`
  relate, or over two types `up` separates (`tax/disjoint?` over the ancestor set),
  `{:members #{h} :marks #{} :kind :orthogonal}`."
  [kb c up hidden?]
  (when (or (seq (:related-dj c)) (seq (:cover-pairs c)) (seq (:related-orth c)))
    (let [tax   (reasoning/taxonomy kb)
          recs  (:records kb)
          seen? (fn [h] (when-let [sx (p/get-sentex recs h)]
                          (and (or (nil? (:context sx)) (contains? up (:context sx)))
                               (not (and hidden? (hidden? h))))))]
      (concat
       (for [h (sort (:related-dj c))
             :let [[a b] (get-in c [::djs h])]
             :when (and a (seen? h)
                        (or (tax/genl-asserted-in? tax a b up)
                            (tax/genl-asserted-in? tax b a up)))]
         {:members #{h} :marks #{} :kind :disjoint})
       (for [pr (:cover-pairs c)
             :when (every? seen? pr)]
         {:members pr :marks #{} :kind :cover})
       (for [h (sort (:related-orth c))
             :let [[a b] (get-in c [::orths h])]
             :when (and a (seen? h)
                        (or (= a b)
                            (tax/genl-asserted-in? tax a b up)
                            (tax/genl-asserted-in? tax b a up)
                            (tax/disjoint? tax a b up)))]
         {:members #{h} :marks #{} :kind :orthogonal})))))

(def family
  "The related-types family's entry in `decide/registry`."
  {:note!     (fn [kb w sx stored? _] (note-declaration! kb w sx stored?))
   :synced?   related-synced?
   :sync      sync-related
   :handles   (fn [c] (concat (:related-dj c) (apply concat (:cover-pairs c)) (:related-orth c)))
   :live?     (fn [_ c] (or (seq (:related-dj c)) (seq (:cover-pairs c)) (seq (:related-orth c))))
   :unstamped #{::djs ::dj-by-type ::dj-seen ::cvs ::cv-by-whole ::orths ::orth-seen}
   :nogoods   related-nogoods})

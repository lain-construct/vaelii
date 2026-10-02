;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.decide.related
  "The declarations over related types: a `disjoint` over two types one reaches the other
  of through `genl`, and a cover naming a part a `disjoint` separates from its whole.  See
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

(defn- note-declaration!
  "Keep the related-types rows in step with the fact `sx` arriving (`stored?`) or leaving
  (`note-declaration`).  Reads nothing for any other fact."
  [kb w sx stored?]
  (when (or (disjoint-args sx) (cover-args sx))
    (swap! (reasoning/nogood-candidates kb) #(note-declaration w % sx stored?))))

(defn- related-synced?
  "Is `c`'s `:related-dj` read under the `genl` generation as it stands?"
  [tax c]
  (or (empty? (::djs c)) (= (tax/relation-gen tax :genl) (::dj-seen c))))

(defn- sync-related
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

(defn- related-nogoods
  "The related-types clashes a reader with ancestor set `up` reads, among the declarations
  it sees, in `up` and not `hidden?`: a `disjoint` of `:related-dj` whose arguments one
  reaches the other of through the `genl` edges stated in `up` (`tax/genl-asserted-in?`),
  `{:members #{h} :marks #{} :kind :disjoint}`, and a cover pair,
  `{:members #{cover disjoint} :marks #{} :kind :cover}`."
  [kb c up hidden?]
  (when (or (seq (:related-dj c)) (seq (:cover-pairs c)))
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
         {:members pr :marks #{} :kind :cover})))))

(def family
  "The related-types family's entry in `decide/registry`."
  {:note!     (fn [kb w sx stored? _] (note-declaration! kb w sx stored?))
   :synced?   related-synced?
   :sync      sync-related
   :handles   (fn [c] (concat (:related-dj c) (apply concat (:cover-pairs c))))
   :live?     (fn [_ c] (or (seq (:related-dj c)) (seq (:cover-pairs c))))
   :unstamped #{::djs ::dj-by-type ::dj-seen ::cvs ::cv-by-whole}
   :nogoods   related-nogoods})

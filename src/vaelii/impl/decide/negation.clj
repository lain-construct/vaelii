;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.decide.negation
  "The negation family: a stored `(not B)` and a stored `B` whose contexts one reader sees.
  See docs/nmtms.md, \"Nogoods decided at the reader\"."
  (:require [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]))

;; ---- negation -------------------------------------------------------------
;;
;; A body stored in both polarities (`:opposed`, `kb/note-opposed!`) holds a negation
;; nogood wherever one context sees a stored `(not B)` and a stored `B`.  `::negation`
;; keeps, per opposed body, `{:neg {h context} :pos {h context} :reader [pair]}`, read off
;; the index at each store or removal of either polarity.  A reader decides every pair:
;; the body is under `::cross` and the members under `:negation`.

(defn- body-of
  "The body a fact sentence keys its polarity under: `s` with one leading `not` removed."
  [s]
  (if (sx/negation? s) (second s) s))

(defn- polarity-handles
  "`{h context}` of the stored facts whose sentence is `s`, in every context: one trie
  read under a variable context."
  [kb s]
  (let [sx0  (sx/sentex s '?c)
        s    (:sentence sx0)
        recs (:records kb)]
    (into {}
          (keep (fn [h]
                  (when-let [sx (p/get-sentex recs h)]
                    (when (and (nil? (:antecedent sx)) (= s (:sentence sx)))
                      [h (:context sx)]))))
          (reads/as-stored-at-path (:index kb) (sx/path sx0)))))

(defn- place-entry
  "`c` with body `b`'s entry `old` replaced by `new` (either nil): `::negation`,
  `::cross` and `:negation` lose what `old` gave them and take what `new` gives, and
  `::moved` takes `b` when its pairs changed."
  [c b old new]
  (let [was (:reader old)
        now (:reader new)]
    (cond-> (-> c
                (update :negation #(-> (reduce disj (or % #{}) (mapcat identity was))
                                       (into (mapcat identity now))))
                (update ::cross #(if (seq now) (conj (or % #{}) b) (some-> % (disj b)))))
      new                  (assoc-in [::negation b] new)
      (nil? new)           (update ::negation dissoc b)
      (not= (set was) (set now)) (update ::moved (fnil conj #{}) b))))

(defn- note-negation
  "`c` with body `b`'s negation entry read again from storage, its pairs under
  `:reader`."
  [kb c b]
  (let [neg   (polarity-handles kb (list 'not b))
        pos   (when (seq neg) (polarity-handles kb b))
        entry (when (and (seq neg) (seq pos))
                {:neg neg :pos pos :reader (vec (for [n (keys neg), p (keys pos)] [n p]))})]
    (place-entry c b (get-in c [::negation b]) entry)))

(defn- note-negation!
  "Read the negation entry of the fact `sx`'s body again when the body is opposed or
  holds an entry.  A body stored in one polarity only reads nothing: one set lookup."
  [kb sx]
  (let [s (:sentence sx)]
    (when (and (nil? (:antecedent sx)) (seq? s))
      (let [b     (body-of s)
            cands (reasoning/nogood-candidates kb)]
        (when (or (contains? @(reasoning/opposed kb) b)
                  (contains? (::negation @cands) b))
          (swap! cands #(note-negation kb % b)))))))

(defn take-moved-negations!
  "The bodies whose negation pairs may have moved a verdict since the last call, and the
  record emptied: every body whose pairs a store or removal changed, and, when the
  `genlCx` generation moved, every opposed body, since a context edge forms or removes the
  joint view that decides a pair."
  [kb]
  (let [gen     (tax/relation-gen (reasoning/taxonomy kb) :genlCx)
        [old _] (swap-vals! (reasoning/nogood-candidates kb)
                            #(cond-> (dissoc % ::moved)
                               (not= gen (::genlcx %)) (assoc ::genlcx gen)))]
    (cond-> (set (::moved old))
      (not= gen (::genlcx old)) (into (::cross old)))))

(defn negation-bodies
  "The bodies of the members of `(handles)` that a reader decides a negation pair over.
  `handles` is called only when the KB holds such a pair."
  [kb handles]
  (let [ns (:negation @(reasoning/nogood-candidates kb))]
    (when (seq ns)
      (into #{} (comp (filter ns)
                      (keep #(p/get-sentex (:records kb) %))
                      (map (comp body-of :sentence)))
            (handles)))))

(defn- negation-nogoods
  "The negation nogoods a reader with ancestor set `up` reads: every pair of a stored
  `(not B)` and a stored `B` whose two contexts it sees, neither `hidden?`, `{:members #{n
  p} :marks #{} :kind :negation}`.  Reads the entries and no body."
  [cands up hidden?]
  (let [seen? (fn [h c] (and (or (nil? c) (contains? up c))
                             (not (and hidden? (hidden? h)))))]
    (for [b (::cross cands)
          :let [{:keys [neg pos reader]} (get-in cands [::negation b])]
          [n p] reader
          :when (and (seen? n (get neg n)) (seen? p (get pos p)))]
      {:members #{n p} :marks #{} :kind :negation})))

(defn negation-vantages
  "The vantages of the negation nogood `members` a reader decides, the maximal common
  descendants of its two members' contexts, or nil when `members` is not such a pair."
  [kb members]
  (let [c @(reasoning/nogood-candidates kb)]
    (when (and (= 2 (count members)) (every? #(contains? (:negation c) %) members))
      (let [recs (:records kb)
            [a b] (map #(p/get-sentex recs %) members)]
        (when (and a b (let [sa (:sentence a) sb (:sentence b)]
                         (or (= sa (list 'not sb)) (= sb (list 'not sa)))))
          (tax/maximal-common-descendant-contexts (reasoning/taxonomy kb)
                                                  [(:context a) (:context b)]))))))

(def family
  "The negation family's entry in `decide/registry`.  A replay reads each body of
  `:opposed` once, after it, since `kb/rebuild-opposed!` rebuilds that roster first."
  {:note!     (fn [kb _ sx _ replay?] (when-not replay? (note-negation! kb sx)))
   :replayed  (fn [kb _ c] (reduce #(note-negation kb %1 %2) c @(reasoning/opposed kb)))
   :handles   :negation
   :live?     (fn [_ c] (seq (:negation c)))
   :unstamped #{::negation ::cross ::moved ::genlcx}
   :nogoods   (fn [_ c up hidden?] (negation-nogoods c up hidden?))})

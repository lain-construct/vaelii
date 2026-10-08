;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.journal
  "A journal of the handles each update of a persistent map can move, kept in the map and
  written in the update that moves them, so a reader reads what moved since its last
  position instead of the whole map: the candidate index's candidates and the flat-cache
  keys the taxonomy's `:cache-moves` journals; and an
  index of a map's handles by context read again off its journal (`indexed`).  See
  docs/nmtms.md, \"The candidate journal\" and \"The inherited-clash memo\".")

(def ^:private bound
  "The most handles the journal holds.  An update past it starts a new journal, and a
  reader whose position is not in the new one reads the whole map once."
  16384)

(defn- started
  "A journal holding no handle: one cell, which no earlier position is."
  []
  {:cells (list ::start) :n 0})

(defn note
  "`c` with the handles `hs` journaled."
  [c hs]
  (let [hs (set hs)]
    (if (empty? hs)
      c
      (let [j (or (::journal c) (started))
            j (if (<= (+ (long (:n j)) (count hs)) bound) j (started))]
        (assoc c ::journal {:cells (conj (:cells j) hs) :n (+ (long (:n j)) (count hs))})))))

(defn position
  "The journal's position in `c`, for `since`: nil when `c` journals nothing."
  [c]
  (:cells (::journal c)))

(defn since
  "The handles `c` journaled after position `pos` (`position` of an earlier value of the
  map): none when neither journals anything, and nil when `pos` is not in `c`'s journal,
  after a `restart`, a journal started past `bound`, or a copy of the map that journaled
  apart."
  [c pos]
  (if (nil? pos)
    (when (nil? (::journal c)) #{})
    (loop [cells (:cells (::journal c)), acc (transient #{})]
      (cond (identical? cells pos)     (persistent! acc)
            (not (set? (first cells))) nil
            :else                      (recur (next cells) (reduce conj! acc (first cells)))))))

(defn restart
  "`c` with a journal no earlier position is in: the map a rebuild leaves, equal to any
  other holding the same rows."
  [c]
  (assoc c ::journal (started)))

(defn indexed
  "`c` with `::at` holding the handles `(holds? c h)` answers true of by context, the
  context `(context-of h)` answers: read again for the handles journaled since the
  index's position, and built from `(every c)` when `c` holds no index or the journal
  does not reach back to its position.  A handle's context never moves, so a handle
  leaving is taken out under the context it entered with."
  [c holds? context-of every]
  (let [{:keys [pos by of] :as at} (::at c)
        now   (position c)
        moved (when at (since c pos))]
    (cond
      (and at (identical? pos now)) c

      (some? moved)
      (let [[by of] (reduce (fn [[by of :as acc] h]
                              (let [was (find of h)]
                                (cond
                                  (and (nil? was) (holds? c h))
                                  (let [cx (context-of h)]
                                    [(update by cx (fnil conj #{}) h) (assoc of h cx)])

                                  (and was (not (holds? c h)))
                                  (let [cx (val was), hs (disj (get by cx) h)]
                                    [(if (seq hs) (assoc by cx hs) (dissoc by cx)) (dissoc of h)])

                                  :else acc)))
                            [by of] moved)]
        (assoc c ::at {:pos now :by by :of of}))

      :else
      (let [of (into {} (map (fn [h] [h (context-of h)])) (every c))]
        (assoc c ::at {:pos now
                       :by  (reduce-kv (fn [by h cx] (update by cx (fnil conj #{}) h)) {} of)
                       :of  of})))))

(defn at
  "The handles `indexed` keeps under the contexts of the set `up` or under no context, as
  a set: read off whichever of the index's contexts and `up` holds fewer, and the one set
  kept under a context itself when no other context contributes."
  [c up]
  (let [by   (:by (::at c))
        sets (if (< (count by) (count up))
               (into [] (keep (fn [[cx hs]] (when (or (nil? cx) (contains? up cx)) hs))) by)
               (into [] (keep #(get by %)) (cons nil up)))]
    (case (count sets)
      0 #{}
      1 (first sets)
      (let [big (reduce #(if (< (count %1) (count %2)) %2 %1) sets)]
        (persistent! (reduce (fn [acc hs] (if (identical? hs big) acc (reduce conj! acc hs)))
                             (transient big) sets))))))

(defn without
  "`c` with no journal and no index read off it, as an image holds it."
  [c]
  (dissoc c ::journal ::at))

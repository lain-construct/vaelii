;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.reroute
  "The firings a reader reads as withdrawn only because a witness edge on a path they
  name is withdrawn there, while the reader still reaches the path's ends over a second
  route, as the facts a settle pass re-chains per reader under `chain/*witness-view*`.  A
  pass reads them through `lost-firing-seeds`, which keeps its memos in `:own-readings`
  under this namespace's keys.  See docs/nmtms.md, \"Where the layer stops\"."
  (:require [vaelii.impl.decide :as decide]
            [vaelii.impl.decide.inherited :as inherited]
            [vaelii.impl.inherit :as inherit]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]))

(defn- witness-paths
  "The witness edges among `sentences` (`{handle sentence}`, one justification's
  antecedents) joined into paths, as `{:rel :a :b :edges}`: the `genl` and `genlCx` edges,
  and the edges of a relation some `transitiveInArgInverse` among them preserves a claim along.
  A path is what the firing depends on, so its two ends are the reachability a second
  route can answer for."
  [sentences]
  (let [binary    (fn [s] (when (and (seq? s) (= 2 (count (nm/args s))))
                            [(nm/functor s) (first (nm/args s)) (second (nm/args s))]))
        preserved (into #{} (keep (fn [s] (when (and (seq? s) (= 'transitiveInArgInverse (nm/functor s)))
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

(defn- lost-firing-tops
  "`[tops target? edge?]` for `lost-firing-seeds`: the contexts whose readers can lose a firing
  over a withdrawn witness edge — an inherited clash's vantage, an excepting context and
  the context of a candidate edge a reader decides — and whether a handle is a member or
  target, which a reader withdraws by name, and whether a sentex is a witness edge.
  Memoized in `:own-readings` under the
  candidate index part of `decide/stamp` and the rosters it reads, so a settle that moves
  none of them reads no candidate."
  [kb inh ex live?]
  (let [pres (keys @(reasoning/preserving kb))
        k    [(when live? (first (decide/stamp kb))) inh ex pres]
        memo (::lost-tops @(reasoning/own-readings kb))]
    (if (and memo (= k (:key memo)))
      (:value memo)
      (let [cands (if live? (decide/candidate-handles kb) #{})
            ;; a firing is re-routed around a withdrawn witness edge, so a candidate is a
            ;; reason to read its readers only when it is one: a closure-relation or a
            ;; preserved-relation fact, in either polarity
            rels  (into tax/closure-relations (map second) pres)
            edge? (fn [sx] (contains? rels (nm/functor (kb/body-under-not (:sentence sx)))))
            tops  (-> (into (into #{} (mapcat :vantages) (vals inh)) (keys ex))
                      (into (keep #(when-let [sx (p/get-sentex (:records kb) %)]
                                     (when (edge? sx) (:context sx))))
                            cands))
            ;; a reader's `:derived` leaves out its own seeds; a member or target is left
            ;; out for every reader, so ask the rosters per candidate rather than build
            ;; their union
            target? (fn [h] (or (some #(contains? % h) (vals ex))
                                (contains? cands h)))
            v       [tops target? edge?]]
        (swap! (reasoning/own-readings kb) assoc ::lost-tops {:key k :value v})
        v))))

(defn lost-firing-seeds
  "`[[reader seeds] …]`: the facts to re-chain, per reader, under `chain/*witness-view*`,
  for the firings a reader reads as withdrawn only because an edge of a path they name
  is withdrawn there, while the reader still reaches that path's ends and believes the
  firing's sentence through no other sentex.  The readers are the contexts that see an
  inherited clash's vantage, an excepting context or the context of a candidate edge a
  reader decides (`lost-firing-tops`).  `done` holds the `[reader handle]` pairs an
  earlier pass re-chained, and `region` is the pass's relabelled window.  Nil when no
  reader can withdraw anything.  `settle` does not call this during a rebuild
  (`settle/*rebuilding?*`).

  A firing is a candidate only in a reader's `:derived` set (`res/withdrawal`): an
  `except` target or a loser is withdrawn by name, not over a path, so the walk is
  proportional to what rests on those and not to how many there are.  A reader whose
  last scan found nothing is scanned again only when its withdrawal entry was recomputed
  or the window holds a witness edge or a sentex of a sentence that scan found
  re-routable, so a settle that moves nothing a reader reads scans no reader."
  [kb done region]
  (let [ex    @(reasoning/excepted kb)
        live? (decide/live? kb)]
    (when (or (seq ex) live?)
      (let [tx      (reasoning/taxonomy kb)
            tms     (reasoning/tms kb)
            [tops target? edge?] (lost-firing-tops kb (inherited/inherited-clashes kb) ex live?)
            ;; a top outside the `genlCx` lattice is its own only reader
            readers (sort (into (set (remove nil? tops))
                                (filter (fn [c] (some #(tax/sees? tx c %) tops)))
                                (tax/contexts tx)))
            clean   (::lost-clean @(reasoning/own-readings kb))
            ;; the window's sentences, and whether it holds a witness edge, which can open
            ;; a route no withdrawal entry watches
            moved   (delay (into [] (keep #(p/get-sentex (:records kb) %)) @region))
            msents  (delay (into #{} (map :sentence) @moved))
            edges?  (delay (boolean (some edge? @moved)))
            scan    (fn [r]
                      (let [w (res/withdrawal kb r)
                            c (get clean r)]
                        (if (and c (identical? w (:entry c)) (not @edges?)
                                 (not-any? #(contains? @msents %) (:sentences c)))
                          [r nil c]
                          (let [out   (or (:out w) #{})
                                seen  (volatile! #{})
                                seeds (into []
                                            (comp (remove target?)
                                                  (remove #(contains? done [r %]))
                                                  (keep (fn [h]
                                                          (let [js (keep #(jtms/justification tms %)
                                                                         (jtms/supports tms h))
                                                                ss (into [] (mapcat #(rerouteable kb r out %)) js)
                                                                s  (when (seq ss) (:sentence (p/get-sentex (:records kb) h)))]
                                                            (when s (vswap! seen conj s))
                                                            (when (and s (empty? (res/matches-visible kb s r)))
                                                              [h ss])))))
                                            (:derived w))]
                            [r seeds (when (empty? seeds) {:entry w :sentences @seen})]))))
            scanned (mapv scan readers)]
        (swap! (reasoning/own-readings kb) assoc ::lost-clean
               (into {} (keep (fn [[r _ c]] (when c [r c]))) scanned))
        (into [] (keep (fn [[r seeds _]] (when (seq seeds) [r seeds]))) scanned)))))

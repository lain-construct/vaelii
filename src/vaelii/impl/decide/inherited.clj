;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.decide.inherited
  "The inherited family's rows of the candidate index: the clashes the settle's discovery
  found (`discovery/discover-inherited!`), each with its vantages, which every reader at or
  below a vantage decides.  See docs/nmtms.md, \"The inherited-clash memo\"."
  (:require [vaelii.impl.naming :as nm]
            [vaelii.impl.types.reasoning :as reasoning]))

;; ---- the inherited clashes --------------------------------------------------
;;
;; A stored claim against a known-true claim argument preservation reaches at its tuple or
;; at its converse's (`inherit/clashing-claim`, `inherit/converse-claim`) is found by the
;; settle's one discovery (`discovery/preserving-nogoods`), which reads no verdict, with the
;; most general contexts that read it whole.  `:inherited` keeps them, `{:by-set {members
;; ngmap} :by-vantage {context #{members}}}`, and a reader at or below a vantage decides
;; each as it decides every other family.

(defn clear-inherited!
  "Empty `:inherited`.  True when it held a clash."
  [kb]
  (let [cands (reasoning/nogood-candidates kb)]
    (when (seq (:inherited @cands))
      (swap! cands dissoc :inherited)
      true)))

(defn install-inherited!
  "Keep the nogood maps `ngs` a discovery found under `:inherited`: one entry per member
  set, its vantages the union of every map's and its `:sentence` and `:inherited` the
  least map's by content.  True when `ngs` is not empty."
  [kb ngs]
  (when (seq ngs)
    (let [by-set (into {}
                       (map (fn [[ms es]]
                              (let [e (nm/min-by-content-key
                                       (juxt #(nm/print-key (:sentence %))
                                             #(nm/print-key (:inherited %)))
                                       compare es)]
                                [ms {:nogood   ms
                                     :sentence (:sentence e)
                                     :inherited (:inherited e)
                                     :vantages (into #{} (mapcat :vantages) es)}])))
                       (group-by :nogood ngs))]
      (swap! (reasoning/nogood-candidates kb) assoc :inherited
             {:by-set     by-set
              :by-vantage (reduce-kv (fn [m ms {:keys [vantages]}]
                                       (reduce #(update %1 %2 (fnil conj #{}) ms) m vantages))
                                     {} by-set)})
      true)))

(defn inherited-clashes
  "The inherited clashes, `{members {:nogood :sentence :inherited :vantages}}`."
  [kb]
  (:by-set (:inherited @(reasoning/nogood-candidates kb))))

(defn- inherited-nogoods
  "The inherited clashes a reader with ancestor set `up` decides: those with a vantage in
  `up`, each `{:members :marks #{} :kind :inherited :report ngmap}`."
  [c up]
  (let [{:keys [by-set by-vantage]} (:inherited c)]
    (when (seq by-set)
      (let [sets (if (< (count up) (count by-vantage))
                   (into #{} (mapcat #(get by-vantage %)) up)
                   (into #{} (comp (filter #(contains? up (key %))) (mapcat val)) by-vantage))]
        (for [ms sets]
          {:members ms :marks #{} :kind :inherited :report (get by-set ms)})))))

(def family
  "The inherited family's entry in `decide/registry`.  Its rows are installed by the
  settle's discovery, not noted at the store, and they are a stamp part of their own,
  since a vantage moving moves no member."
  {:handles   (fn [c] (mapcat key (:by-set (:inherited c))))
   :live?     (fn [_ c] (seq (:by-set (:inherited c))))
   :unstamped #{:inherited}
   :stamp     (fn [_ c] (:inherited c))
   :nogoods   (fn [_ c up _] (inherited-nogoods c up))})

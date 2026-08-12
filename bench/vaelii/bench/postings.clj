;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.bench.postings
  "The measurement that decides HOW to densify the index's posting lists, before any
  is built.

  The index's handle-set families (trie leaves `[:trie :handles …]`, and the roots/indexes
  `[:context-root]` `[:functor-root]` `[:argument-root]` `[:term-index]` `[:rule-index]` `[:exception-index]`) are today
  `PersistentHashSet`s of **boxed `Long`** handles, which the scale harness measured as
  the fattest resident component.  The obvious replacement is `RoaringBitmap` — but this
  project has a cautionary tale: substrate.md *predicted* native structures ~10× denser and
  the measurement refuted it.  So this bench does not assume; it takes the **real posting
  sets from a loaded index** and re-encodes each one four ways, measuring what actually
  matters:

    - **Density (jol retained heap)** — the deciding axis, and structural, so trusted even
      while another load contends for the box.
    - **Intersection** (`kv-intersect`'s work) and **build** cost — wall-clock, so untrusted in
      absolute terms under contention, but the four run under the *same* contention so their
      ranking is informative.

  Encodings: the `PersistentHashSet<Long>` baseline; `RoaringBitmap`; a sorted `int[]`
  (dense, trivial, merge-intersectable, but O(n) to mutate); and fastutil `IntOpenHashSet`
  (primitive, O(1) insert, no compression).  Density turns on how *clustered* the handles in
  a posting are — handles are allocated in assertion order, so a predicate loaded in bursts
  packs into Roaring runs while a scattered term does not — which is exactly why it must be
  measured on the real distribution, not asserted.

  Run: `lein bench-postings [facts]`  (default 200000).  Uses space 24."
  (:require [clojure.set :as set]
            [vaelii.bench.util :as u :refer [zipf-sample]]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.protocols :as p])
  (:import [it.unimi.dsi.fastutil.ints IntOpenHashSet]
           [org.openjdk.jol.info GraphLayout]
           [org.roaringbitmap RoaringBitmap]))

;; ---- generation (same fact shape as the scale harness) ------------------

(defn- gen-fact
  [^java.util.Random rng {:keys [preds inds units ctxs pred-cum ind-cum compound-frac]}]
  (let [pred (nth preds (zipf-sample pred-cum rng))
        ctx  (nth ctxs (.nextInt rng (count ctxs)))
        arity (+ 2 (.nextInt rng 2))
        a    (nth inds (zipf-sample ind-cum rng))
        rst  (repeatedly (dec arity) #(nth inds (zipf-sample ind-cum rng)))
        rst  (if (< (.nextDouble rng) compound-frac)
               (concat (butlast rst) [(list 'qtyFn (.nextInt rng 1000)
                                            (nth units (.nextInt rng (count units))))])
               rst)]
    [(apply list pred a rst) ctx]))

(defn- load! [kb ^java.util.Random rng {:keys [n] :as cfg}]
  (dotimes [_ n] (let [[s c] (gen-fact rng cfg)] (kb/create-sentex kb s c))))

;; ---- encodings ----------------------------------------------------------

(defn- ->roaring ^RoaringBitmap [handles]
  (let [r (RoaringBitmap.)]
    (doseq [h (sort handles)] (.add r (int h)))   ; ascending add: Roaring's happy path
    (.runOptimize r)                              ; collapse contiguous runs (the whole point)
    r))

(defn- ->intarr ^ints [handles] (int-array (sort (map int handles))))

(defn- ->fastutil ^IntOpenHashSet [handles]
  (let [s (IntOpenHashSet. (count handles))]
    (doseq [h handles] (.add s (int h)))
    s))

;; sorted two-pointer intersection over int[] — the count is all we need to time the work.
(defn- intarr-inter-count ^long [^ints a ^ints b]
  (let [na (alength a) nb (alength b)]
    (loop [i 0 j 0 c 0]
      (if (or (>= i na) (>= j nb))
        c
        (let [x (aget a i) y (aget b j)]
          (cond (< x y) (recur (inc i) j c)
                (> x y) (recur i (inc j) c)
                :else   (recur (inc i) (inc j) (inc c))))))))

;; ---- measurement --------------------------------------------------------

(defn retained
  "Retained heap of the object graph rooted at `objs` (jol), deduping shared structure."
  ^long [objs]
  (.totalSize ^GraphLayout (GraphLayout/parseInstance (into-array Object objs))))

(defn- family [k]
  (when (vector? k)
    (case (first k)
      :idx  (when (= :l (second k)) :leaf)       ; :c is a counter, :s a label set — skip
      :context-root :ctx
      :functor-root :functor
      :argument-root :arg
      :term-index :term
      (:rule-index :exception-index) :rule
      nil)))

(defn- ms [t0] (/ (- (System/nanoTime) t0) 1e6))

(defn- time-build [f postings]
  (let [t0 (System/nanoTime)] (doseq [s postings] (f s)) (ms t0)))

;; ---- report -------------------------------------------------------------

(defn- fmt-row [label postings entries bytes]
  (format "%-10s %9s %11s %10.1f %11.1f"
          label (format "%,d" postings) (format "%,d" entries)
          (/ bytes 1048576.0) (double (/ bytes (max 1 entries)))))

(defn- measure-family [fam postings]
  (let [sets    (vec postings)
        entries (reduce + (map count sets))
        base    (retained sets)
        roars   (mapv ->roaring sets)
        arrs    (mapv ->intarr sets)
        fasts   (mapv ->fastutil sets)
        rb (retained roars) ab (retained arrs) fb (retained fasts)]
    (println (format "\n  %s — %,d postings, %,d entries" (name fam) (count sets) entries))
    (println (format "  %-10s %9s %11s %10s %11s" "encoding" "postings" "entries" "MB" "B/entry"))
    (println (str "  " (apply str (repeat 54 \-))))
    (doseq [[lbl b] [["baseline" base] ["roaring" rb] ["int[]" ab] ["fastutil" fb]]]
      (println (str "  " (fmt-row lbl (count sets) entries b))))
    {:fam fam :sets sets :entries entries :base base :roaring rb :intarr ab :fastutil fb}))

(defn- intersection-bench [families]
  ;; the two hottest term/functor postings (a hot∩hot), and hot∩rare.
  (let [pool (->> (concat (:sets (families :functor)) (:sets (families :term)))
                  (filter #(> (count %) 200))
                  (sort-by count >))
        big  (take 2 pool)
        rare (last (filter #(< 5 (count %) 60) (concat (:sets (families :term)) (:sets (families :arg)))))]
    (when (and (= 2 (count big)) rare)
      (let [[a b] big
            pairs {"hot ∩ hot"  [a b]
                   "hot ∩ rare" [a rare]}]
        (println "\n── intersection (UNTRUSTED absolute under contention; ratio is the signal) ──")
        (println (format "  %-12s %5s %14s %12s %10s %12s" "pair" "|res|" "persistent ms" "roaring ms" "int[] ms" "fastutil ms"))
        (doseq [[lbl [x y]] pairs]
          (let [rx (->roaring x) ry (->roaring y)
                ax (->intarr x)  ay (->intarr y)
                fx (->fastutil x) fy (->fastutil y)
                iters 2000
                warm  (fn [f] (dotimes [_ 200] (f)))
                run   (fn [f] (warm f) (let [t0 (System/nanoTime)] (dotimes [_ iters] (f)) (/ (ms t0) iters)))
                res   (count (set/intersection x y))
                pms (run #(set/intersection x y))
                rms (run #(.getCardinality (RoaringBitmap/and rx ry)))
                ims (run #(intarr-inter-count ax ay))
                fms (run #(let [c ^IntOpenHashSet (.clone fx)] (.retainAll c fy) (.size c)))]
            (println (format "  %-12s %5d %14.4f %12.4f %10.4f %12.4f" lbl res pms rms ims fms))))))))

(defn survey-index
  "Measure an already-loaded kb's index: composition (posting values vs keys/nodes),
  per-family + total posting density across all four encodings, build cost, and
  intersection.  Shared by the synthetic bake-off (`-main`) and the real-corpus survey
  (`vaelii.bench.survey`), so both report identically."
  [kb]
  (let [state  @(:state (:backend (:index kb)))
        by-fam (->> state
                    (keep (fn [[k v]] (when (and (family k) (set? v)) [(family k) v])))
                    (group-by first)
                    (into {} (map (fn [[f kvs]] [f (mapv second kvs)]))))
        ;; Composition first (heap cleanest before the encoding copies exist): how much of
        ;; the whole index map is posting VALUES — the only part Phase 1 touches — vs the
        ;; trie keys, counters, child-label sets and HAMT nodes a dense-KEY pass (Phase 2)
        ;; attacks.
        idx-total (retained [state])
        val-total (retained (mapcat val by-fam))]
    (println "\n══ index composition (what Phase 1 can even touch) ══")
    (println (format "  whole index map     : %.1f MB" (/ idx-total 1048576.0)))
    (println (format "  posting VALUES       : %.1f MB  (%.0f%% of the index — Phase 1's target)"
                     (/ val-total 1048576.0) (* 100.0 (/ (double val-total) idx-total))))
    (println (format "  keys+counters+nodes  : %.1f MB  (%.0f%% — the residual: Phase 2's target)"
                     (/ (- idx-total val-total) 1048576.0)
                     (* 100.0 (/ (double (- idx-total val-total)) idx-total))))
    (let [measured (into {} (map (fn [[f ps]] [f (measure-family f ps)])) by-fam)
          ;; TOTAL: baseline deduped across ALL families (a handle shared by :functor-root/:argument-root/
          ;; :term-index is one boxed Long counted once), vs the primitive encodings summed (no
          ;; cross-posting sharing).  The fair "heap to hold every posting".
          all-sets (mapcat :sets (vals measured))
          tot-entries (reduce + (map :entries (vals measured)))
          tot-base (retained all-sets)
          tot-roar (reduce + (map :roaring (vals measured)))
          tot-arr  (reduce + (map :intarr (vals measured)))
          tot-fast (reduce + (map :fastutil (vals measured)))]
      (println "\n══ TOTAL across all handle-posting families ══")
      (println (format "  %-10s %9s %11s %10s %11s %8s" "encoding" "postings" "entries" "MB" "B/entry" "vs base"))
      (println (str "  " (apply str (repeat 62 \-))))
      (doseq [[lbl b] [["baseline" tot-base] ["roaring" tot-roar] ["int[]" tot-arr] ["fastutil" tot-fast]]]
        (println (format "  %-10s %9s %11s %10.1f %11.1f %7.2f×"
                         lbl (format "%,d" (count all-sets)) (format "%,d" tot-entries)
                         (/ b 1048576.0) (double (/ b (max 1 tot-entries))) (/ (double tot-base) b))))
      (println "\n── build cost (UNTRUSTED; ratio is the signal — the write-path tradeoff) ──")
      (doseq [[lbl f] [["roaring" ->roaring] ["int[]" ->intarr] ["fastutil" ->fastutil]]]
        (println (format "  build all as %-9s : %.1f ms" lbl (time-build f all-sets))))
      (intersection-bench measured)
      (let [ranked (sort-by second [[:baseline tot-base] [:roaring tot-roar] [:intarr tot-arr] [:fastutil tot-fast]])]
        (println (format "\n▶ densest encoding: %s (%.2f× smaller than baseline). Density decides; intersection/build break ties."
                         (name (ffirst ranked)) (/ (double tot-base) (second (first ranked)))))))))

(defn -main [& args]
  (let [n (or (some-> (first args) Long/parseLong) 200000)
        P (max 50 (quot n 400)) M (max 1000 (quot n 4))
        cfg {:n n :preds (u/terms "pr" P) :inds (u/terms "Ind" M)
             :units (u/terms "unit" 10)
             :ctxs (mapv #(symbol (str "CxCtx" %)) (range 8))
             :pred-cum (u/zipf-cumulative P 1.2) :ind-cum (u/zipf-cumulative M 1.0)
             :compound-frac 0.1}
        kb (kb/open-kb {:backend :memory :space 24 :recover? false}
                       (fn [_] nil) (fn [_] nil))]
    (println (format "vaelii posting-encoding bake-off — %,d synthetic facts" n))
    (println "Density (jol retained heap) is TRUSTED; intersection/build wall-clock is UNTRUSTED under contention.")
    (p/clear-records! (:records kb)) (p/clear-index! (:index kb))
    (load! kb (java.util.Random. 42) cfg)
    (survey-index kb)
    (shutdown-agents)))

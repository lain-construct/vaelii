;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.bench.densetrie
  "Measure how much of the index's
  **keys+counters+nodes** (69–72% of the index, per the postings bake-off) a dense-KEY
  representation actually recovers, before building it.

  The current index is a flat `HashMap` keyed by structured **vectors of interned
  symbols** (`[:trie :count [genl a b ctx]]`, …), with `Long` counters and `PersistentHashSet`
  child-label sets.  Every trie node is three such entries, and a path's every prefix is a
  separate vector object — so the structure is redundant boxed keys + HAMT overhead.  Phase 2
  proposes interned `int` tokens and a real trie of nodes (an `int`-keyed child map per node,
  a primitive count), which shares prefixes structurally and drops the boxed keys.

  Two measurements, both jol retained heap (trusted under contention):

    1. **Decomposition** — split the live index into its subsystems (trie counters / trie
       child-sets / trie leaves / the context/functor/arg roots / term index / rule index) and
       size each, so the vague \"69% keys+nodes\" becomes an actionable breakdown.
    2. **Dense trie vs current trie structure** — build a faithful dense trie (real nodes,
       fastutil `Int2ObjectOpenHashMap` children, interned tokens) from the same paths and
       compare its retained size + the token dictionary against the current `:c`+`:s` trie
       structure.

  Run: `lein bench-densetrie [sample-n]`  (default 300000, uniform real facts; pass a number
  and `synthetic` to use the synthetic generator instead)."
  (:require [vaelii.bench.postings :as postings]
            [vaelii.bench.survey :as survey]
            [vaelii.impl.columnar :as columnar]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.protocols :as p])
  (:import [it.unimi.dsi.fastutil.ints Int2ObjectOpenHashMap]
           [it.unimi.dsi.fastutil.objects Object2IntOpenHashMap]))

;; ---- a faithful dense trie node -----------------------------------------
;; cnt: primitive subtree count.  kids: Int2ObjectOpenHashMap<TNode> (interned-token edges),
;; created lazily.  No leaves — this measures STRUCTURE only (leaves are Phase 1's int[]).

(defprotocol PNode
  (bump! [n])
  (child! [n t])
  (n-cnt [n])
  (n-kids [n]))

(deftype TNode [^{:unsynchronized-mutable true :tag long} cnt
                ^{:unsynchronized-mutable true} kids]
  PNode
  (bump! [_] (set! cnt (unchecked-inc cnt)))
  (child! [_ t]
    (let [^Int2ObjectOpenHashMap m (or kids (let [m (Int2ObjectOpenHashMap.)] (set! kids m) m))]
      (or (.get m (int t))
          (let [c (TNode. 0 nil)] (.put m (int t) c) c))))
  (n-cnt [_] cnt)
  (n-kids [_] kids))

;; A **columnar CSR trie** — the actual dense-native target: no per-node objects at all,
;; just parallel primitive int arrays.  counts[i] is node i's subtree count; node i's child
;; edges are [offsets[i], offsets[i+1]); edge e carries token edge-tok[e] to child node
;; edge-tgt[e].  This is the densest a trie gets; the fastutil-hashmap-per-node TNode above
;; is the naive strawman (per-node map overhead swamps the interning win).
(defn- to-csr [^TNode root]
  (let [ids   (java.util.IdentityHashMap.)
        order (java.util.ArrayList.)]
    (letfn [(num! [n]
              (when-not (.containsKey ids n)
                (.put ids n (int (.size ids))) (.add order n)
                (when-let [k (n-kids n)]
                  (doseq [t (sort (seq (.keySet ^Int2ObjectOpenHashMap k)))]
                    (num! (.get ^Int2ObjectOpenHashMap k (int t)))))))]
      (num! root))
    (let [nn      (.size order)
          counts  (int-array nn)
          offsets (int-array (inc nn))]
      (dotimes [i nn]
        (let [n (.get order i) k (n-kids n)]
          (aset counts i (int (n-cnt n)))
          (aset offsets (inc i) (int (+ (aget offsets i)
                                        (if k (.size ^Int2ObjectOpenHashMap k) 0))))))
      (let [ne       (aget offsets nn)
            edge-tok (int-array ne)
            edge-tgt (int-array ne)]
        (dotimes [i nn]
          (let [n (.get order i) k (n-kids n)]
            (when k
              (loop [ts (sort (seq (.keySet ^Int2ObjectOpenHashMap k))) e (aget offsets i)]
                (when (seq ts)
                  (let [t (int (first ts))]
                    (aset edge-tok e t)
                    (aset edge-tgt e (int (.get ids (.get ^Int2ObjectOpenHashMap k t))))
                    (recur (rest ts) (inc e))))))))
        {:nodes nn :edges ne :arrays [counts offsets edge-tok edge-tgt]}))))

(defn- intern! [^Object2IntOpenHashMap dict tok]
  (if (.containsKey dict tok)
    (.getInt dict tok)
    (let [id (.size dict)] (.put dict tok id) id)))

(defn- build-dense [paths]
  (let [dict (doto (Object2IntOpenHashMap.) (.defaultReturnValue -1))
        root (TNode. 0 nil)]
    (doseq [^clojure.lang.Indexed path paths]
      (loop [node root i 0]
        (bump! node)
        (when (< i (count path))
          (recur (child! node (intern! dict (nth path i))) (inc i)))))
    {:root root :dict dict}))

;; ---- decomposition of the current index ---------------------------------

(defn- subsystem [k]
  (when (vector? k)
    (case (first k)
      :idx  (case (second k) :c :trie-counters :s :trie-childsets :l :trie-leaves nil)
      :context-root :root-context
      :functor-root :root-functor
      :argument-root :root-arg
      :term-index :term-index
      (:rule-index :exception-index) :rule-index
      nil)))

(defn- mb [b] (/ (double b) 1048576.0))

(defn- decompose [state]
  (let [groups (group-by (comp subsystem key) state)
        order  [:trie-counters :trie-childsets :trie-leaves :root-context :root-functor
                :root-arg :term-index :rule-index]
        total  (postings/retained [state])]
    (println "\n══ current index decomposition (where the memory is) ══")
    (println (format "  %-16s %10s %10s %8s" "subsystem" "MB" "entries" "%"))
    (println (str "  " (apply str (repeat 48 \-))))
    (doseq [ss order]
      (when-let [entries (groups ss)]
        (let [b (postings/retained (mapv (fn [[_ v]] v) entries))     ; values only
              kb (postings/retained (mapv key entries))]              ; keys only
          (println (format "  %-16s %10.1f %10s %7.0f%%  (keys %.1f MB, values %.1f MB)"
                           (name ss) (mb (+ b kb)) (format "%,d" (count entries))
                           (* 100.0 (/ (double (+ b kb)) total)) (mb kb) (mb b))))))
    (println (format "  %-16s %10.1f  (whole index map, deduped)" "TOTAL" (mb total)))
    total))

;; ---- main ---------------------------------------------------------------

(defn- real-pairs
  ([n] (real-pairs n survey/default-dir))
  ([n dir]
   (survey/ensure-store! dir n)
   (survey/uniform-pairs dir n)))

(defn- load-into [pairs backend db]
  (let [kb (kb/open-kb {:backend backend :space db :recover? false}
                         (fn [_] nil) (fn [_] nil))]
    (p/clear-records! (:records kb)) (p/clear-index! (:index kb))
    (doseq [[s c] pairs] (try (kb/create-sentex kb s c) (catch Exception _ nil)))
    kb))

(defn -main [& args]
  (let [n     (or (some-> (first args) Long/parseLong) 300000)
        pairs (real-pairs n)
        kb    (load-into pairs :memory 28)
        state @(:state (:backend (:index kb)))
        stored (count (p/sentex-ids (:records kb)))]
    (println (format "vaelii Phase-2 dense-trie measurement — %,d real facts (uniform sample)" stored))
    ;; Phase 1 + 2 landed: the whole index store retained (trie + roots + term index),
    ;; measured the same way for each backend — :memory (flat map), :memory-dense
    ;; (int-postings values), :memory-columnar (native int-token trie + int-postings).
    (let [mem-idx  (postings/retained [(:index kb)])
          dkb      (load-into pairs :memory-dense 26)
          den-idx  (postings/retained [(:index dkb)])
          ckb      (load-into pairs :memory-columnar 24)
          col-idx  (postings/retained [(:index ckb)])]
      (println "\n══ Phase 1 + 2 (landed): whole index store, retained heap ══")
      (println (format "  :memory          %8.1f MB   (flat map of boxed vector keys — the baseline)" (mb mem-idx)))
      (println (format "  :memory-dense    %8.1f MB   (%.2f× — int-postings on the handle sets)"
                       (mb den-idx) (/ (double mem-idx) den-idx)))
      (println (format "  :memory-columnar %8.1f MB   (%.2f× — native int-token trie + int-postings)"
                       (mb col-idx) (/ (double mem-idx) col-idx)))
      ;; attribute the columnar RAM into NON-overlapping parts.  The trie and roots share
      ;; one token dictionary, so jol counts it in both; measure it once and subtract, so
      ;; the three parts sum to the whole.
      (let [dict-b  (postings/retained [(:dict (:index ckb))])
            trie-b  (- (postings/retained [(:trie (:index ckb))]) dict-b)
            roots-b (- (postings/retained [(:roots (:index ckb))]) dict-b)]
        (println (format "    ├─ native trie (nodes + leaf postings)    %8.1f MB   (was 471.5 MB flat: counters+childsets+leaves)"
                         (mb trie-b)))
        (println (format "    ├─ int-keyed roots + term index           %8.1f MB   (packed-long keys + int-postings — was ~208 MB boxed)"
                         (mb roots-b)))
        (println (format "    └─ shared token dictionary                %8.1f MB   (interns every trie token + root/term term, once)"
                         (mb dict-b)))
        ;; freeze the trie into CSR (the after-bulk-load, before-query move) and re-measure
        (columnar/compact! (:index ckb))
        (let [ctrie (- (postings/retained [(:trie (:index ckb))]) dict-b)
              whole (postings/retained [(:index ckb)])]
          (println "\n══ Phase 2 follow-up: trie CSR-compacted (read-optimized) ══")
          (println (format "  native trie   %8.1f MB → %.1f MB   (%.1f× — flat CSR int arrays, no per-node objects)"
                           (mb trie-b) (mb ctrie) (/ (double trie-b) ctrie)))
          (println (format "  whole index   %8.1f MB → %.1f MB   (%.2f× vs :memory baseline)"
                           (mb col-idx) (mb whole) (/ (double mem-idx) whole))))))
    (decompose state)
    ;; the current trie STRUCTURE (counters + child-label sets + their keys), Phase 2's target
    (let [cur-struct (postings/retained
                      (mapcat (fn [[k v]] (when (#{:trie-counters :trie-childsets} (subsystem k)) [k v]))
                              state))
          ;; the paths the trie indexes — the terminal path vectors under the :l keys
          paths (->> state (keep (fn [[k _]] (when (= :trie-leaves (subsystem k)) (nth k 2)))))
          {:keys [root dict]} (build-dense paths)
          naive-b      (postings/retained [root])
          csr          (to-csr root)
          csr-b        (postings/retained (:arrays csr))
          dict-b       (postings/retained [dict])
          toks         (postings/retained (into [] (remove nil?) (.keySet ^Object2IntOpenHashMap dict)))
          map-new      (max 0 (- dict-b toks))]
      (println "\n══ Phase 2: dense trie structure vs current (structure only — leaves are Phase 1) ══")
      (println (format "  current  (:c + :s, boxed vector keys, HAMT)     : %8.1f MB" (mb cur-struct)))
      (println (format "  naive    (fastutil int-map per node)            : %8.1f MB   (%.2f×) — per-node map overhead swamps it"
                       (mb naive-b) (/ (double cur-struct) naive-b)))
      (println (format "  CSR      (columnar int arrays, no node objects) : %8.1f MB   (%.1f×)  ← the dense-native target"
                       (mb csr-b) (/ (double cur-struct) csr-b)))
      (println (format "           %,d nodes, %,d edges = 4 int arrays" (:nodes csr) (:edges csr)))
      (println (format "  token dictionary (%,d tokens)                  : %8.1f MB   (tokens %.1f MB relocated from records + map %.1f MB new)"
                       (.size ^Object2IntOpenHashMap dict) (mb dict-b) (mb toks) (mb map-new)))
      (println (format "  → Phase 2 (CSR trie + new dict map): %.1f MB → %.1f MB  (%.1f× on the trie structure)"
                       (mb cur-struct) (+ (mb csr-b) (mb map-new)) (/ (double cur-struct) (+ csr-b map-new))))
      (println "\n  (tokens relocate from record bodies — Phase 4 stores int ids — so they are not net-new;")
      (println "   leaves/root/term postings are Phase 1's int[] target, in bench-postings.)"))
    (shutdown-agents)))

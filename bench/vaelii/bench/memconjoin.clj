;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.bench.memconjoin
  "The conjunctive-join benchmark with the index structures held **in RAM** — the
  access-path / leapfrog experiment on the memory backend.

  A star join on a shared variable `?x` in argument position 2:

      [(r0 ?a ?x) (r1 ?b ?x) (r2 ?c ?x)]

  Three executors, two kinds of metric.  The unify calls (candidate tuples
  examined) and the bindings threaded are pure functions of the data and the join
  order, so they measure the *algorithm*; wall-clock measures the substrate, where
  the extent, the argument roots, the `?x`-domains and the canonical trie are all
  Clojure maps.  Access-path selection is therefore a CPU difference — every access
  path is a HashMap probe — while leapfrog's edge is algorithmic: ~4.8× fewer unify
  calls, ~2.2× fewer bindings, which shows up as real CPU.


  Run: `lein bench-memconjoin [e0 e1 e2 xdom]`  (defaults 24000 14000 7000 9000).
  No server, no external dependency."
  (:require [clojure.set :as set]
            [vaelii.bench.util :as u :refer [zipf-sample]]))

(def ^:private rel-ids '[r0 r1 r2])

;; ---- generation (the reference conjoin bench's, RAM-only) ---------------

(defn- shuffled
  "A seeded Fisher-Yates shuffle — each relation gets its own `?x` ranking so hot
  values differ across relations and the domains do not trivially coincide."
  [v ^java.util.Random rng]
  (let [a (object-array v)]
    (dotimes [i (dec (alength a))]
      (let [j (+ i (.nextInt rng (- (alength a) i)))
            t (aget a i)]
        (aset a i (aget a j)) (aset a j t)))
    (vec a)))

(defn- gen
  "For each relation: `e` tuples `[a x]`, `a` uniform over a small domain, `x` Zipf
  over this relation's own shuffled `?x` domain."
  [rng {:keys [xdom-size a-size sizes]}]
  (let [xs  (u/terms "X" xdom-size)
        as  (u/terms "a" a-size)
        cum (u/zipf-cumulative xdom-size 1.1)]
    (into {}
          (map-indexed
           (fn [i e]
             (let [rank (shuffled xs rng)]
               [(nth rel-ids i)
                (mapv (fn [_] [(nth as (.nextInt rng a-size))
                               (nth rank (zipf-sample cum rng))])
                      (range e))]))
           sizes))))

;; ---- build the in-memory index structures -------------------------------

(defn- build-trie
  "The flattened count trie for arity-2 `[a x]` paths — root child set (the `a`s),
  the `[a x]` counts, and the leaves — the same node shape `index.clj` writes, in maps."
  [tuples]
  (reduce (fn [t [h [a x]]]
            (-> t
                (update-in [:count []]    (fnil inc 0))
                (update-in [:count [a]]   (fnil inc 0))
                (update-in [:count [a x]] (fnil inc 0))
                (update-in [:child []]    (fnil conj #{}) a)
                (update-in [:leaf [a x]]  (fnil conj #{}) h)))
          {:count {} :child {} :leaf {}}
          (map-indexed vector tuples)))

(defn- build [rels]
  {:tuples rels
   :argument-root   (into {} (map (fn [[rid ts]]
                           [rid (persistent!
                                 (reduce (fn [m [h [_ x]]] (assoc! m x (conj (get m x #{}) h)))
                                         (transient {}) (map-indexed vector ts)))]))
                 rels)
   :xdom   (into {} (map (fn [[rid ts]] [rid (into #{} (map second) ts)])) rels)
   :trie   (into {} (map (fn [[rid ts]] [rid (build-trie ts)])) rels)})

;; ---- access paths -------------------------------------------------------

(defn- arg-probe  [ix rid x] (count (get-in (:argument-root ix) [rid x])))

(defn- trie-probe
  "The canonical-trie count of tuples with `x` at position 2: fan the whole first-arg
  child set, then read `count-at [a x]` per branch — the after-a-variable fan."
  [ix rid x]
  (let [t (get-in ix [:trie rid])]
    (reduce (fn [acc a] (+ acc (long (get-in t [:count [a x]] 0))))
            0 (get-in t [:child []]))))

(defn- x-intersection [ix rids] (apply set/intersection (map (:xdom ix) rids)))

;; ---- executors (return {:results :unify :bindings}) ---------------------

(defn- left-deep
  "Lead with the smallest relation's extent, group it by the join value, and probe the
  other two once per value via `probe` — only the access path differs between the
  trie-walk and access-path strategies."
  [ix order probe]
  (let [[rs rm rl] order
        rs-tuples  (get-in ix [:tuples rs])
        by-x       (persistent!
                    (reduce (fn [m [_ x]] (assoc! m x (inc (long (get m x 0)))))
                            (transient {}) rs-tuples))
        u   (volatile! (long (count rs-tuples)))
        b   (volatile! (long (count rs-tuples)))
        res (volatile! 0)]
    (doseq [[x rsx] by-x]
      (let [ms (probe ix rm x)]
        (vswap! u + ms)
        (vswap! b + (* (long rsx) (long ms)))
        (when (pos? ms)
          (let [ls (probe ix rl x)]
            (vswap! u + ls)
            (let [r (* (long rsx) (long ms) (long ls))]
              (vswap! b + r)
              (vswap! res + r))))))
    {:results @res :unify @u :bindings @b}))

(defn- leapfrog
  "Intersect the join-variable domains first, then expand only the surviving `?x`."
  [ix order]
  (let [xs  (x-intersection ix order)
        u   (volatile! 0) b (volatile! 0) res (volatile! 0)]
    (doseq [x xs]
      (let [as (arg-probe ix (nth order 0) x)
            bs (arg-probe ix (nth order 1) x)
            cs (arg-probe ix (nth order 2) x)]
        (vswap! u + (+ as bs cs))
        (vswap! b + (+ (long as) (* (long as) (long bs)) (* (long as) (long bs) (long cs))))
        (vswap! res + (* (long as) (long bs) (long cs)))))
    {:results @res :unify @u :bindings @b :xstar (count xs)}))

;; ---- measurement --------------------------------------------------------

(defn- timed
  "Average `runs` timed executions of `f` after two warmups — at RAM speed one run is
  noisy, so amortize."
  [runs f]
  (dotimes [_ 2] (f))
  (let [t0 (System/nanoTime)
        r  (last (mapv (fn [_] (f)) (range runs)))
        ms (/ (- (System/nanoTime) t0) 1e6 runs)]
    (assoc r :ms ms)))

;; ---- report -------------------------------------------------------------

(defn -main [& args]
  (let [[e0 e1 e2 xd] (map #(when % (Long/parseLong %)) args)
        sizes [(or e0 24000) (or e1 14000) (or e2 7000)]
        xdsz  (or xd 9000)
        cfg   {:xdom-size xdsz :a-size 40 :sizes sizes}
        rng   (java.util.Random. 42)]
    (println "vaelii conjunctive-join benchmark — IN-MEMORY — star join on ?x (position 2)")
    (println (format "relations r0/r1/r2 = %,d / %,d / %,d tuples over an ?x-domain of %,d, |a|=40\n"
                     (nth sizes 0) (nth sizes 1) (nth sizes 2) xdsz))
    (let [rels  (gen rng cfg)
          ix    (build rels)
          exts  (into {} (map (fn [r] [r (count (get-in ix [:tuples r]))]) rel-ids))
          doms  (into {} (map (fn [r] [r (count (get-in ix [:xdom r]))]) rel-ids))
          order (vec (sort-by exts rel-ids))
          xs    (x-intersection ix order)]
      (println "counts the planner reads:")
      (doseq [r rel-ids]
        (println (format "  %s: extent %,d   distinct ?x %,d" r (exts r) (doms r))))
      (println (format "  join order (smallest extent first): %s" (vec order)))
      (println (format "  leapfrog lead (smallest ?x-domain): %s   |?x common to all three| = %,d"
                       (apply min-key doms rel-ids) (count xs)))

      (let [trie (timed 20 #(left-deep ix order trie-probe))
            argp (timed 20 #(left-deep ix order arg-probe))
            leap (timed 20 #(leapfrog  ix order))]
        (println)
        (println (format "%-14s %14s %16s %12s %10s"
                         "strategy" "unify calls" "bindings thread" "results" "ms"))
        (println (apply str (repeat 69 \-)))
        (doseq [[label m] [["trie-walk" trie] ["access-path" argp] ["leapfrog" leap]]]
          (println (format "%-14s %14d %16d %12d %10.3f"
                           label (:unify m) (:bindings m) (:results m) (:ms m))))
        (println (format "\nall strategies agree on the result set: %s"
                         (= (:results trie) (:results argp) (:results leap))))
        (println (format "1->2 (access-path selection): ms %.3f -> %.3f  (%.1fx)  — a CPU difference, every path a map probe"
                         (:ms trie) (:ms argp) (/ (:ms trie) (max 1e-6 (:ms argp)))))
        (println (format "2->3 (leapfrog): unify %,d -> %,d (%.1fx), bindings %,d -> %,d (%.1fx), ms %.3f -> %.3f (%.1fx)"
                         (:unify argp) (:unify leap) (/ (double (:unify argp)) (max 1 (:unify leap)))
                         (:bindings argp) (:bindings leap) (/ (double (:bindings argp)) (max 1 (:bindings leap)))
                         (:ms argp) (:ms leap) (/ (:ms argp) (max 1e-6 (:ms leap))))))
      (shutdown-agents))))

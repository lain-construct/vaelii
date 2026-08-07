;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.dense-kv
  "A dense in-memory `KvBackend` (`vaelii.impl.kv`) — the `:dense` index axis, under either
  record store (`:memory-dense`, `:disk-dense`).

  The index's handle-set families (trie leaves, the context / functor / argument roots, the
  rule and exception indexes) are the bulk of its RAM, and a bake-off across candidate
  encodings found a **packed sorted `int[]`** ~5.6× denser than the
  `PersistentHashSet<Long>` the memory backend stores, with `RoaringBitmap` winning only the
  few large/hot postings.  So a handle set here is an `IntPostings`: an exact sorted `int[]`
  while small, promoted to a `RoaringBitmap` once it crosses a threshold (dense for large,
  O(log) add, fast intersect).  The trie's child-*label* set (`[:trie :children …]`) holds tokens —
  including numbers — not handles, so it stays an ordinary set; counters stay `Long`s.  The
  backend dispatches on the key tag.

  `kv-intersect` narrows **in that representation** rather than in the sets it would make:
  `RoaringBitmap/and` where both sides are hot, a sorted merge where both are cold, and a
  probe of the cold side into the bitmap where the tiers differ, and a binary search of the
  short run into the long one where neither is a bitmap.  Smallest posting first, and one
  Clojure set built at the end at the size of the answer.  What that buys is not mainly
  speed on the big case (hot ∩ hot at 32k: 29.2 → 0.56 ms) but the *shape* of the common
  one: a query pins a rare argument on a hot predicate, and 4 handles against a root of n
  went from 4.73 ms at n=32,000 to 0.0015 ms at any n — flat in the extent the argument
  roots exist to avoid scanning.  `lein perf --only intersect-selectivity` is the gate on
  that, and what cost is left tracks the answer rather than the columns, which is the
  boundary contract and not the narrowing.

  Off by default (`:index :dense`); proven set-equal to `MemoryKvBackend` by
  `dense_kv_oracle_test`.  Single-writer: the int structures are mutated in place, and
  `kv-members` / `kv-intersect` materialize a fresh Clojure set at the boundary so a caller
  never holds the mutable structure.  Handles fit `int` through 2³¹ (≫ 100M)."
  (:require [clojure.set :as set]
            [vaelii.impl.kv :as kv])
  (:import [java.util Arrays]
           [org.roaringbitmap RoaringBitmap]))

(def ^:const promote 128)   ; int[] → RoaringBitmap above this many entries (public for the oracle)

;; ---- IntPostings: a sorted int[] while small, a RoaringBitmap when hot ----

(defprotocol IPostings
  (padd!    [p h] "Add handle h (in place); return p.")
  (prem!    [p h] "Remove handle h (in place); return p.")
  (pcard    [p]   "Cardinality.")
  (pcontains? [p h]
    "Is handle h present?  A binary search on the `int[]`, or the bitmap's own test —
    the O(log n) / O(1) probe that answers membership without building the set
    `pmembers` builds, which is what an index gate calling it per firing needs.")
  (pmembers [p]   "A fresh Clojure set of the handles (as Longs).")
  (pints    [p]
    "A fresh sorted `int[]` of the handles — the boxing-free read, for a caller that
    iterates rather than set-tests.  Fresh (never the live array) because callers walk
    it while mutating the posting, which is exactly what `vaelii.impl.dense-jtms` does
    when it pushes a node's justifications onto a worklist.")
  (pseed [p]
    "This posting as an intersection accumulator — its own `int[]` or its own
    `RoaringBitmap`, handed back rather than copied.  Safe because `pand` allocates its
    result on every arm, so nothing downstream can write through it.")
  (pand [p acc]
    "`acc` — a sorted `int[]` or a `RoaringBitmap` — narrowed to the handles this posting
    also holds, as a **fresh** accumulator.  Dispatches on both representations: two hot
    postings meet in `RoaringBitmap/and`, two cold ones in a sorted merge, and a mixed
    pair probes the cold side's entries into the bitmap.  So neither side is materialized,
    and neither side is mutated — `RoaringBitmap.and` the *instance* method would mutate
    its receiver, and a query that quietly shrank a posting is a corrupt index the oracle
    finds late rather than never."))

(defn- ints->set [^ints a]
  (loop [i 0, s (transient #{})]
    (if (< i (alength a)) (recur (inc i) (conj! s (long (aget a i)))) (persistent! s))))

;; ---- the intersection arms ----------------------------------------------
;; Each takes ascending runs and returns a fresh ascending run, which is what keeps every
;; `pand` arm allocating (see the protocol) and lets the arms compose in any order.  There
;; are three, and which one runs is a property of the two *values*: a bitmap probe, a
;; sorted merge, or — for a lopsided pair with no bitmap between them — a binary search of
;; the short run into the long one.

(def ^:private ^:const gallop
  "How many times longer one run must be before its partner is *searched into* it rather
  than merged with it.  A merge is O(na+nb) and a search O(ns·log nb), so the crossover is
  where the ratio passes log of the long side — under 20 for anything that fits an `int`.
  32 sits past it with room, so the arm is taken only where it clearly wins."
  32)

(defn- ints-merge
  "The intersection of two ascending `int[]`s of comparable length — one pass over each."
  ^ints [^ints a ^ints b]
  (let [na (alength a), nb (alength b), out (int-array (min na nb))]
    (loop [i 0, j 0, k 0]
      (if (or (>= i na) (>= j nb))
        (Arrays/copyOf out (int k))
        (let [x (aget a (int i)), y (aget b (int j))]
          (cond (< x y) (recur (inc i) j k)
                (> x y) (recur i (inc j) k)
                :else   (do (aset out (int k) x) (recur (inc i) (inc j) (inc k)))))))))

(defn- ints-probe
  "The entries of ascending `small` that ascending `big` holds, each found by binary search
  with the window advancing — `big` is never walked, only searched.  This is the no-bitmap
  form of the same idea `ints-in-roaring` has, and it is what a mapped root run needs,
  since a snapshot's postings are plain sorted runs with no hot tier to probe."
  ^ints [^ints small ^ints big]
  (let [ns (alength small), nb (alength big), out (int-array ns)]
    (loop [i 0, lo 0, k 0]
      (if (or (>= i ns) (>= lo nb))
        (Arrays/copyOf out (int k))
        (let [x (aget small (int i))
              j (Arrays/binarySearch big (int lo) nb x)]
          (if (>= j 0)
            (do (aset out (int k) x) (recur (inc i) (inc j) (inc k)))
            (recur (inc i) (- (inc j)) k)))))))       ; miss ⇒ -(insertion point) - 1

(defn- ints-and
  "The intersection of two ascending `int[]`s, merged or searched by their length ratio."
  ^ints [^ints a ^ints b]
  (let [na (alength a), nb (alength b)]
    (cond
      (< (* gallop na) nb) (ints-probe a b)
      (< (* gallop nb) na) (ints-probe b a)
      :else                (ints-merge a b))))

(defn- ints-in-roaring
  "The entries of ascending `a` that `r` holds — one bitmap test apiece, so the bitmap is
  probed rather than enumerated.  This is the arm that makes a rare ∩ hot narrowing cost
  the rare side."
  ^ints [^ints a ^RoaringBitmap r]
  (let [n (alength a), out (int-array n)]
    (loop [i 0, k 0]
      (if (>= i n)
        (Arrays/copyOf out (int k))
        (let [x (aget a (int i))]
          (if (.contains r x)
            (do (aset out (int k) x) (recur (inc i) (inc k)))
            (recur (inc i) k)))))))

(deftype IntPostings [^:unsynchronized-mutable ^ints arr
                      ^:unsynchronized-mutable ^RoaringBitmap roar]
  IPostings
  (padd! [this h]
    (let [h (int h)]
      (if roar
        (.add roar h)
        (let [i (Arrays/binarySearch arr h)]
          (when (neg? i)                                   ; absent → insert (sorted)
            (let [ip (dec (- i)), n (alength arr), b (int-array (inc n))]
              (System/arraycopy arr 0 b 0 ip)
              (aset b ip h)
              (System/arraycopy arr ip b (inc ip) (- n ip))
              (if (> (inc n) promote)                      ; grew hot → become a bitmap
                (let [r (RoaringBitmap.)]
                  (dotimes [k (inc n)] (.add r (aget b k)))
                  (set! roar r) (set! arr nil))
                (set! arr b)))))))
    this)
  (prem! [this h]
    (let [h (int h)]
      (if roar
        (.remove roar h)
        (let [i (Arrays/binarySearch arr h)]
          (when (>= i 0)
            (let [n (alength arr), b (int-array (dec n))]
              (System/arraycopy arr 0 b 0 i)
              (System/arraycopy arr (inc i) b i (- n i 1))
              (set! arr b))))))
    this)
  (pcard [_] (long (if roar (.getCardinality roar) (alength arr))))
  (pcontains? [_ h]
    (let [h (int h)]
      (if roar (.contains roar h) (>= (Arrays/binarySearch arr h) 0))))
  (pmembers [_] (if roar (ints->set (.toArray roar)) (ints->set arr)))
  (pints [_] (if roar (.toArray roar) (aclone arr)))
  (pseed [_] (or roar arr))
  (pand [_ acc]
    (if roar
      (if (instance? RoaringBitmap acc)
        (RoaringBitmap/and ^RoaringBitmap acc roar)    ; both hot — the native ∧
        (ints-in-roaring acc roar))                    ; acc is the cold side — probe it in
      (if (instance? RoaringBitmap acc)
        (ints-in-roaring arr ^RoaringBitmap acc)       ; this side is cold, so ≤ `promote`
        (ints-and arr acc)))))

;; public: the columnar trie (vaelii.impl.columnar) reuses IntPostings for its leaf
;; handle sets — this is where Phase 1's postings and Phase 2's trie unify.
(defn int-postings [] (->IntPostings (int-array 0) nil))

(defn- as-set [v] (if (instance? IntPostings v) (pmembers v) (or v #{})))

;; ---- intersection over the postings, not the sets they would make -------
;;
;; A posting here is an `IntPostings` or a bare ascending `int[]` (what a mapped run copies
;; out to — `vaelii.impl.dense-roots`), and the three helpers below are the generic form of
;; `pcard` / `pseed` / `pand` over both.  The accumulator is whatever the arms produce, an
;; `int[]` or a `RoaringBitmap`, and it is materialized into a Clojure set exactly once, at
;; the end, at the size of the *answer* rather than of the columns it came from.

(defn- card* ^long [p] (if (instance? IntPostings p) (pcard p) (alength ^ints p)))
(defn- seed* [p] (if (instance? IntPostings p) (pseed p) p))

(defn- and* [p acc]
  (if (instance? IntPostings p)
    (pand p acc)
    (if (instance? RoaringBitmap acc)
      (ints-in-roaring p ^RoaringBitmap acc)
      (ints-and p acc))))

(defn- acc-count ^long [acc]
  (if (instance? RoaringBitmap acc) (.getCardinality ^RoaringBitmap acc) (alength ^ints acc)))

(defn- acc->set [acc]
  (if (instance? RoaringBitmap acc) (ints->set (.toArray ^RoaringBitmap acc)) (ints->set acc)))

(defn intersect-postings
  "The intersection of `postings` — each an `IntPostings` or an ascending `int[]` — as a
  Clojure set of Longs.

  **Smallest first**, which is not the tie-break it looks like: the accumulator can only
  shrink, so seeding it with the narrowest column is what keeps every later step a probe of
  a few entries rather than a scan of a hot one.  An accumulator that empties stops the
  fold, since nothing after it can put a handle back.

  Public because `vaelii.impl.dense-roots` holds the same postings under its own keys and
  must narrow them the same way."
  [postings]
  (let [[p & more] (sort-by card* postings)]
    (acc->set
     (reduce (fn [acc q]
               (let [acc' (and* q acc)]
                 (if (zero? (acc-count acc')) (reduced acc') acc')))
             (seed* p)
             more))))

(defn postings-set
  "A posting — an `IntPostings` or an ascending `int[]` — as a fresh Clojure set of Longs,
  for the mixed fold a caller falls back to when one of the keys is not a handle family."
  [p]
  (if (instance? IntPostings p) (pmembers p) (ints->set p)))

(defn- intersect
  "Intersection of the posting values as a Clojure set.  A handle family holds
  `IntPostings`, and those narrow in their own representation; any other key holds an
  ordinary set whose members are not handles at all (path tokens, term names), so a list
  containing one folds `clojure.set/intersection` smallest-first instead."
  [vals]
  (if (every? #(instance? IntPostings %) vals)
    (intersect-postings vals)
    (let [sets (sort-by count (map as-set vals))]
      (reduce set/intersection sets))))

;; ---- the backend --------------------------------------------------------

(defn- handle-key?
  "Does `k` name a HANDLE set (int postings)?  Handle sets: trie leaves `[:trie :handles …]`, and
  the roots/indexes under `:context-root` `:functor-root` `:argument-root` `:term-index` `:rule-index` `:exception-index`.  The trie
  child-label set `[:trie :children …]` (tokens, incl. numbers), the counter `[:trie :count …]`
  and the term roster `[:term-roster]` (term *names*) are not — they stay an ordinary set / a Long.

  A key this fails to recognize is stored boxed and answers every read identically, so
  nothing behavioural can catch a spelling that drifts from the one `vaelii.impl.kv`
  writes; `dense_routing_test` checks the stored representation instead."
  [k]
  (and (vector? k)
       (case (first k)
         :trie (= :handles (second k))
         (:context-root :functor-root :argument-root :term-index :rule-index :exception-index) true
         false)))

(defrecord TieredKvBackend [state]
  kv/KvBackend
  (kv-get  [_ k]   (get @state k))
  (kv-put  [_ k v] (swap! state assoc k v) nil)
  (kv-delete  [_ k]   (swap! state dissoc k) nil)
  (kv-increment [_ k]   (long (get (swap! state update k (fnil inc 0)) k)))
  (kv-decrement [_ k]   (long (get (swap! state update k (fnil dec 0)) k)))

  (kv-add-to-set [_ k m]
    (if (handle-key? k)
      (padd! (or (get @state k) (let [p (int-postings)] (swap! state assoc k p) p)) m)
      (swap! state update k (fnil conj #{}) m))
    nil)
  (kv-remove-from-set [_ k m]
    (if (handle-key? k)
      (when-let [p (get @state k)]
        (prem! p m)
        (when (zero? (pcard p)) (swap! state dissoc k)))          ; empty set == absent
      (swap! state (fn [st] (let [s (disj (get st k) m)]
                              (if (empty? s) (dissoc st k) (assoc st k s))))))
    nil)
  (kv-members [_ k] (as-set (get @state k)))
  ;; the probe, straight into whichever representation the key holds — a handle set is
  ;; searched or bitmap-tested in place, so a caller asking "is this handle here?" never
  ;; pays for the Clojure set `kv-members` has to build
  (kv-member? [_ k m] (let [v (get @state k)]
                        (cond (nil? v)                  false
                              (instance? IntPostings v) (pcontains? v m)
                              :else                     (contains? v m))))
  (kv-count    [_ k] (let [v (get @state k)]
                       (cond (nil? v) 0
                             (instance? IntPostings v) (pcard v)
                             :else (count v))))
  (kv-intersect [_ ks]
    (if (empty? ks)
      #{}
      (let [st @state, vals (mapv #(get st %) ks)]
        (if (some nil? vals) #{} (intersect vals)))))       ; a missing key ⇒ empty

  (kv-batch [this ops]
    (mapv (fn [[op k a]]
            (case op
              :put  (do (kv/kv-put  this k a) nil)
              :delete  (do (kv/kv-delete  this k) nil)
              :increment (kv/kv-increment this k)
              :decrement (kv/kv-decrement this k)
              :add-to-set (do (kv/kv-add-to-set this k a) nil)
              :remove-from-set (do (kv/kv-remove-from-set this k a) nil)))
          ops))
  ;; the portable projection: an `IntPostings` is this backend's private representation
  ;; of a handle set, so it is materialized out on the way and rebuilt on the way back
  ;; in.  A `kv-put` of a plain set would look like it worked and then blow up on the
  ;; next `kv-add-to-set`, which is why the install is its own operation.
  (kv-entries [_] (map (fn [[k v]] [k (if (instance? IntPostings v) (pmembers v) v)]) @state))
  (kv-load [_ entries]
    (swap! state into
           (map (fn [[k v]]
                  [k (if (and (handle-key? k) (set? v))
                       (reduce padd! (int-postings) v)
                       v)]))
           entries)
    nil)

  (kv-clear! [_] (reset! state {}) nil))

;; ---- construction (space-number sharing, like the memory backend) ----------

(defonce ^:private index-spaces (atom {}))

(defn- space-atom [space]
  (or (@index-spaces space)
      (-> (swap! index-spaces (fn [m] (if (m space) m (assoc m space (atom {})))))
          (get space))))

(defn dense-kv-backend
  "A dense in-memory `KvBackend`.  Only `:space` matters (selects the shared state atom)."
  [{:keys [space] :or {space 0}}]
  (->TieredKvBackend (space-atom space)))

(defn dense-index-store
  "A dense in-memory `IndexStore` — `KvIndexStore` over a `TieredKvBackend`."
  [opts]
  (kv/->KvIndexStore (dense-kv-backend opts)))

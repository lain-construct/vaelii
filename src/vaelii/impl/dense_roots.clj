;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.dense-roots
  "A key-interning `KvBackend` (`vaelii.impl.kv`) for the columnar index's non-trie
  families — the secondary roots, the rule / exception indexes, and the inverted term
  index.

  Those families are flat `structured-vector-key → handle-set` maps, and the columnar
  measurement (`bench/…/densetrie.clj`) found their **boxed vector keys**
  (`[:term-index term]`, `[:functor-root pred]`, …) to be ~150 MB — the majority of the
  columnar index once the trie went native.  This backend keeps the *values* as
  `IntPostings` (Phase 1's tiered
  `int[]`/Roaring set) but collapses the keys: the term is interned to an `int` through
  the **shared trie dictionary** (`vaelii.impl.tokens`) — so a predicate/individual gets
  the same id the trie edges use — and the whole key becomes one packed `long`
  (`family | pos | term-id`) into a single primitive `Long2ObjectOpenHashMap`.  No boxed
  vectors, no HAMT nodes, one map.

  It stays a full `KvBackend` so the existing composition (an embedded `KvIndexStore`
  over it) is unchanged: only the recognized index families are int-routed; any other key
  — the argument roots and slot roster (see `route` for why neither packs), the term
  roster (term *names*, not handles), a scalar, a counter, the contract test's synthetic
  keys — falls back to a plain in-memory backend (in the columnar store the trie is
  native, so no `[:trie …]` key ever reaches here).  Single-writer, like every index;
  `kv-members` / `kv-intersect` materialize a fresh Clojure set at the boundary — but
  `kv-intersect` builds it at the size of the *answer*, narrowing through
  `dense/intersect-postings` in whichever representation each posting is in, a mapped run
  included.  Proven set-equal to `MemoryKvBackend` on the index families by
  `dense_roots_oracle_test` —
  which, like every behavioural check, cannot see a family that falls back when it should
  route, since the fallback answers identically; `dense_routing_test` reads the
  representation and covers that.

  **Single-*threaded*, which is narrower than single-writer.**  The mapped-section fields
  on `DenseRoots` are `^:unsynchronized-mutable`, so installing or thawing a snapshot
  publishes through no barrier and a second thread may read this backend mid-install —
  `mapped?` true against a `mkeys` it has not seen, say.  The atom- and lock-based
  backends give an incidental reader beside the writer a consistent view; this one does
  not.  Same trade as `vaelii.impl.columnar`, whose docstring states it: these fields are
  read on the hot lookup path, and a volatile read there buys a guarantee the engine's own
  single writer never needs."
  (:require [clojure.set :as set]
            [vaelii.impl.dense-kv :as dense]
            [vaelii.impl.kv :as kv]
            [vaelii.impl.memory :as mem]
            [vaelii.impl.tokens :as tok])
  (:import [it.unimi.dsi.fastutil.longs Long2ObjectOpenHashMap]
           [java.nio IntBuffer LongBuffer]))

;; family tags (bits 56-63); pos in bits 32-55; term-id in bits 0-31 (≫ 100M)
(def ^:private ^:const F-CTX     0)
(def ^:private ^:const F-PRED    1)
;; Reserved, never packed: the argument roots carry a predicate the packed long has no
;; room for, so `route` sends them to the fallback. The number stays claimed so no new
;; family can take a tag `unpack` already assigns a shape — a snapshot key must decode
;; exactly one way.
#_{:clj-kondo/ignore [:unused-private-var]}
(def ^:private ^:const F-ARG     2)
(def ^:private ^:const F-TERM    3)
(def ^:private ^:const F-RULE-A  4)
(def ^:private ^:const F-RULE-C  5)
(def ^:private ^:const F-EXC-P   6)
(def ^:private ^:const F-ROSTER  7)

(def ^:private roster-key (bit-shift-left (long F-ROSTER) 56))   ; the exception roster, a single posting

(defn- packed [family pos id]
  (bit-or (bit-shift-left (long family) 56) (bit-shift-left (long pos) 32) (long id)))

(defn- fam-key
  "The packed long for a family key over `term`, or `:absent` when a *read* names a term
  the dictionary has never interned (so the posting cannot exist).  `intern?` allocates."
  [dict family pos term intern?]
  (let [id (if intern? (tok/intern-token! dict term) (tok/token-id dict term))]
    (if (neg? id) :absent (packed family pos id))))            ; auto-boxes to Long

(defn- route
  "Map a structured index key to its packed long (a `Long`), `:absent` (a read of an
  unknown term), or `:fallback` (not an int-routed family — a scalar / counter / unknown)."
  [dict k intern?]
  (if-not (vector? k)
    :fallback
    (case (nth k 0)
      :context-root (fam-key dict F-CTX  0 (nth k 1) intern?)
      :functor-root (fam-key dict F-PRED 0 (nth k 1) intern?)
      ;; `[:argument-root pred pos term]` carries a predicate the packed long has no
      ;; room for (family 8 | pos 24 | term 32 is already full), so the argument roots
      ;; take the generic map path rather than the int-routed one. Same for the
      ;; `[:argument-slot pos term]` roster, whose members are predicates, not handles.
      :argument-root :fallback
      :term-index (fam-key dict F-TERM 0 (nth k 1) intern?)
      :rule-index (case (nth k 1)
                    :antecedent (fam-key dict F-RULE-A 0 (nth k 2) intern?)
                    :consequent (fam-key dict F-RULE-C 0 (nth k 2) intern?)
                    :fallback)
      :exception-index (if (= :rules (nth k 1))
                         roster-key                                         ; already a boxed Long
                         (fam-key dict F-EXC-P 0 (nth k 1) intern?))
      :fallback)))

(defn- unpack
  "The inverse of `route`'s packing: a packed long back to the structured key it stands
  for.  It covers every family `packed` can construct, so the two are each other's
  inverse whatever `route` chooses to send to the fallback — a family routed there
  instead comes back from the fallback's own enumeration, verbatim, and neither path can
  drop an entry."
  [dict ^long pk]
  (let [family (bit-shift-right pk 56)
        term   (tok/id-token dict (int (bit-and pk 0xffffffff)))]
    (case (int family)
      0 [:context-root term]
      1 [:functor-root term]
      ;; F-ARG (family 2) is reserved and nothing packs it: the real key is the
      ;; four-element `[:argument-root pred pos term]`, whose predicate the packed
      ;; long has no room for (see `route`).  Throwing pins that — reusing the tag
      ;; means designing a decode, not inheriting one with the wrong shape.
      2 (throw (ex-info "F-ARG is reserved; no packed key carries family 2"
                        {:type :reserved-family :packed pk}))
      3 [:term-index term]
      4 [:rule-index :antecedent term]
      5 [:rule-index :consequent term]
      6 [:exception-index term]
      7 [:exception-index :rules])))

;; ---- the mapped tail ----------------------------------------------------
;; A snapshot's roots are three columns: the packed keys sorted ascending (`mkeys`), the
;; start of each key's handle run (`moff`, one longer than the keys), and one shared run of
;; handles (`mhandles`) — the same CSR shape the trie's leaves take, over vocabulary-keyed
;; postings instead of path-keyed ones.  The keys and offsets are vocabulary-scaled and
;; resident; `mhandles` is the fact-scaled mass and is where the file is.
;;
;; While mapped, `m` is empty and every routed read binary-searches the key column.  A
;; **write thaws wholesale**: there is no mapped-plus-delta mode, because a delta would
;; need its own tombstones to hide a mapped entry and that is a second representation of
;; the same posting.  So the snapshot is a read-phase structure, exactly as the trie's is.

(defprotocol PMappedRoots
  (mapped? [b]
    "Are the routed families reading out of an mmap'd snapshot?  True exactly while nothing
    has been written since one was installed, since a write thaws.")
  (^:private -find-key [b pk] "Index of packed key `pk` in the mapped column, or -1.")
  (^:private -slice    [b i]  "The i'th mapped posting as `[lo hi)` into the handle run.")
  (^:private mapped-members [b i] "The i'th mapped posting as a Clojure set of Longs.")
  (^:private mapped-ints [b i]
    "The i'th mapped posting copied out of the buffer as an ascending `int[]` — the
    boxing-free read beside `mapped-members`, for the intersection, which discards most of
    what it reads and would otherwise box every handle on the way past.")
  (^:private -thaw-roots! [b] "Materialize every mapped posting into `m` and drop the map.")
  (snapshot-columns [b remap]
    "The routed families as `{:keys :offsets :handles}` heap arrays, keys sorted and their
    term ids taken through `remap` (an `int[]` from this dictionary's ids to the durable
    ones).  The roster key holds no term, so it is passed through unmapped.")
  (install-mapped! [b keys offsets handles n]
    "Install mapped columns (a `LongBuffer` and two `IntBuffer`s over a snapshot), replacing
    whatever the routed families held."))

(defn- members
  "The set at `k`, from whichever place the routed families live in."
  [this dict ^Long2ObjectOpenHashMap m fallback k]
  (let [r (route dict k false)]
    (cond
      (instance? Long r) (if (mapped? this)
                           (let [i (-find-key this (long r))]
                             (if (neg? i) #{} (mapped-members this i)))
                           (let [p (.get m (long r))] (if p (dense/pmembers p) #{})))
      (= :fallback r)    (kv/kv-members fallback k)
      :else              #{})))                                  ; :absent

(defn- posting
  "The set at `k` in the representation it is *stored* in — an `IntPostings` (heap), an
  ascending `int[]` (a mapped run), a Clojure set (a fallback family), or `nil` when the
  key holds nothing at all.  `kv-intersect` reads this rather than `members`, so a routed
  family never boxes a handle the narrowing is about to throw away."
  [this dict ^Long2ObjectOpenHashMap m fallback k]
  (let [r (route dict k false)]
    (cond
      (instance? Long r) (if (mapped? this)
                           (let [i (-find-key this (long r))]
                             (when-not (neg? i) (mapped-ints this i)))
                           (.get m (long r)))
      (= :fallback r)    (kv/kv-members fallback k)
      :else              nil)))                                  ; :absent

(deftype DenseRoots [dict ^Long2ObjectOpenHashMap m fallback
                     ^:unsynchronized-mutable mkeys      ; LongBuffer | nil
                     ^:unsynchronized-mutable moff       ; IntBuffer  | nil
                     ^:unsynchronized-mutable mhandles   ; IntBuffer  | nil
                     ^:unsynchronized-mutable ^int mn]   ; mapped key count
  PMappedRoots
  (mapped? [_] (some? mkeys))

  (-find-key [_ pk]
    (let [pk (long pk)
          ^LongBuffer ks mkeys]
      (loop [lo 0, hi (dec mn)]
        (if (> lo hi)
          -1
          (let [mid (unsigned-bit-shift-right (+ lo hi) 1)
                v   (.get ks (int mid))]
            (cond (< v pk) (recur (inc mid) hi)
                  (> v pk) (recur lo (dec mid))
                  :else    mid))))))

  (-slice [_ i]
    (let [^IntBuffer o moff, i (int i)]
      [(.get o i) (.get o (inc i))]))

  (mapped-members [this i]
    (let [[lo hi] (-slice this i)
          ^IntBuffer hs mhandles]
      (loop [e (long lo), s (transient #{})]
        (if (< e (long hi)) (recur (inc e) (conj! s (long (.get hs (int e))))) (persistent! s)))))

  (mapped-ints [this i]
    (let [[lo hi] (-slice this i)
          ^IntBuffer hs mhandles
          lo  (long lo)
          out (int-array (- (long hi) lo))]
      (dotimes [e (alength out)] (aset out e (.get hs (int (+ lo e)))))
      out))

  (-thaw-roots! [this]
    (when mkeys
      (let [^LongBuffer ks mkeys
            ^IntBuffer  hs mhandles]
        (dotimes [i mn]
          (let [[lo hi] (-slice this i)
                p       (dense/int-postings)]
            (loop [e (long lo)] (when (< e (long hi)) (dense/padd! p (.get hs (int e))) (recur (inc e))))
            (.put m (.get ks (int i)) p))))
      (set! mkeys nil) (set! moff nil) (set! mhandles nil) (set! mn (int 0)))
    nil)

  (snapshot-columns [this remap]
    (-thaw-roots! this)                                   ; write the live representation
    (let [^ints rm remap
          re  (fn ^long [^long pk]
                (if (= (long F-ROSTER) (bit-shift-right pk 56))
                  pk                                      ; no term in it to remap
                  (bit-or (bit-and pk (bit-not 0xffffffff))
                          (long (aget rm (int (bit-and pk 0xffffffff)))))))
          ks  (.toLongArray (.keySet m))
          n   (alength ks)
          out (long-array n)]
      (dotimes [i n] (aset out i ^long (re (aget ks i))))
      (let [order (let [^longs o (aclone ^longs out)]     ; sorted copy, so a read binary-searches
                    (java.util.Arrays/sort o) o)          ; Arrays/sort on the primitives — no boxing
            back  (java.util.HashMap.)]                   ; remapped key -> its posting
        (dotimes [i n] (.put back (aget out i) (.get m (aget ks i))))
        (let [^ints offs (int-array (inc n))
              total      (volatile! 0)]
          (dotimes [i n]
            (vswap! total + (long (dense/pcard (.get back (aget order i)))))
            (aset offs (inc i) (int @total)))
          (let [^ints hs (int-array (aget offs n))]
            (dotimes [i n]
              (let [^ints ph (dense/pints (.get back (aget order i)))
                    base     (aget offs i)]
                (System/arraycopy ph 0 hs base (alength ph))))
            {:keys order :offsets offs :handles hs})))))

  (install-mapped! [_ keys offsets handles n]
    (.clear m)
    (set! mkeys keys) (set! moff offsets) (set! mhandles handles) (set! mn (int n))
    nil)

  kv/KvBackend
  ;; scalars / counters are never a routed family — only the fallback holds them
  (kv-get  [_ k]   (kv/kv-get  fallback k))
  (kv-put  [_ k v] (kv/kv-put  fallback k v))
  (kv-delete  [_ k]   (kv/kv-delete  fallback k))
  (kv-increment [_ k]   (kv/kv-increment fallback k))
  (kv-decrement [_ k]   (kv/kv-decrement fallback k))

  (kv-add-to-set [this k mem]
    (let [r (route dict k true)]                                 ; intern ⇒ never :absent
      (if (instance? Long r)
        (let [_  (-thaw-roots! this)                             ; a write leaves the mapped tail
              pk (long r)
              p  (or (.get m pk) (let [p (dense/int-postings)] (.put m pk p) p))]
          (dense/padd! p mem))
        (kv/kv-add-to-set fallback k mem)))
    nil)
  (kv-remove-from-set [this k mem]
    (let [r (route dict k false)]
      (cond
        (instance? Long r) (do (-thaw-roots! this)
                               (when-let [p (.get m (long r))]
                                 (dense/prem! p mem)
                                 (when (zero? (dense/pcard p)) (.remove m (long r)))))
        (= :fallback r)    (kv/kv-remove-from-set fallback k mem)))          ; :absent ⇒ nothing to remove
    nil)
  (kv-members [this k] (members this dict m fallback k))
  ;; the probe routes exactly as `kv-count` does — a term the dictionary never interned
  ;; has no posting, so `:absent` is a false rather than a lookup
  (kv-member? [this k mem]
    (let [r (route dict k false)]
      (cond
        (instance? Long r) (if (mapped? this)
                             (let [i (-find-key this (long r))]
                               (if (neg? i)
                                 false
                                 (let [[lo hi] (-slice this i)
                                       ^IntBuffer hs mhandles
                                       h  (int mem)]
                                   ;; the run is sorted (a posting's own order), so the
                                   ;; probe stays the binary search the heap posting is
                                   (loop [lo (long lo), hi (dec (long hi))]
                                     (if (> lo hi)
                                       false
                                       (let [mid (unsigned-bit-shift-right (+ lo hi) 1)
                                             v   (.get hs (int mid))]
                                         (cond (< v h) (recur (inc mid) hi)
                                               (> v h) (recur lo (dec mid))
                                               :else   true)))))))
                             (let [p (.get m (long r))]
                               (boolean (and p (dense/pcontains? p mem)))))
        (= :fallback r)    (kv/kv-member? fallback k mem)
        :else              false)))
  (kv-count [this k]
    (let [r (route dict k false)]
      (cond
        (instance? Long r) (if (mapped? this)
                             (let [i (-find-key this (long r))]
                               (if (neg? i) 0 (let [[lo hi] (-slice this i)] (- (long hi) (long lo)))))
                             (let [p (.get m (long r))] (if p (dense/pcard p) 0)))
        (= :fallback r)    (kv/kv-count fallback k)
        :else              0)))
  ;; The narrowing runs in the postings' own representation (`dense/intersect-postings`),
  ;; which is what `sentexes-with-args` and `sentexes-with-terms` bottom out in.  A
  ;; fallback key holds a set of something other than handles, so a list containing one
  ;; falls back to folding sets — it cannot arise from an index read, only from a caller
  ;; naming a key this backend does not route.
  (kv-intersect [this ks]
    (if (empty? ks)
      #{}
      (let [ps (mapv #(posting this dict m fallback %) ks)]
        (cond
          (some nil? ps) #{}                                     ; a key holding nothing
          (some set? ps) (reduce set/intersection
                                 (sort-by count
                                          (map #(if (set? %) % (dense/postings-set %)) ps)))
          :else          (dense/intersect-postings ps)))))
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
  ;; The portable projection has to undo *both* of this backend's compressions: the
  ;; interned key (through `unpack`, against the shared dictionary) and the `IntPostings`
  ;; value.  The two sides are enumerated together because a key routed to the fallback
  ;; is as much an index entry as a packed one.
  (kv-entries [this]
    (concat (if (mapped? this)
              (map (fn [i]
                     (let [pk (.get ^LongBuffer mkeys (int i))]
                       [(unpack dict pk) (mapped-members this i)]))
                   (range mn))
              (map (fn [k] (let [pk (long k)] [(unpack dict pk) (dense/pmembers (.get m pk))]))
                   (iterator-seq (.iterator (.keySet m)))))
            (kv/kv-entries fallback)))
  (kv-load [this entries]
    (-thaw-roots! this)
    (doseq [[k v] entries]
      (let [r (route dict k true)]                                ; intern ⇒ never :absent
        (if (instance? Long r)
          (.put m (long r) (reduce dense/padd! (dense/int-postings) v))
          (kv/kv-put fallback k v))))
    nil)

  (kv-clear! [_]
    (.clear m)
    (set! mkeys nil) (set! moff nil) (set! mhandles nil) (set! mn (int 0))
    (kv/kv-clear! fallback)
    nil)

  ;; The predicate-scoped argument-root family is the one handle family this backend does
  ;; NOT int-route: `[:argument-root pred pos term]` carries a predicate the packed long
  ;; has no room for, so `route` sends it to the fallback (`unpackable-handle-families`).
  ;; The fallback is a `MemoryKvBackend`, which holds the family as its counted `::arg`
  ;; trie and answers `ArgColumns` off it NATIVELY — a scoped leaf and the agnostic union
  ;; by reference, the agnostic count as a node read, the multi-column probe as an
  ;; intersection of scoped leaves.  So the aggregate reads delegate straight to it, ints
  ;; and all, and get the whole collapse.
  ;;
  ;; Without this, `DenseRoots` took the `Object` default (`vaelii.impl.kv`), which
  ;; reconstructs the four-part `[:argument-root pred pos term]` VECTOR through `arg-key`
  ;; and calls the generic `kv-members`/`kv-count`/`kv-intersect` — routed to `:fallback`
  ;; and re-parsed by the fallback's `arg-root-key?` back into `pos`/`term`/`pred`.  That
  ;; cons-and-reparse per read, and the union rebuilt over the slot roster rather than read
  ;; off the maintained node, is exactly the cost the trie exists to remove; delegating
  ;; here is what carries the v2/v3 memory-backend win onto the columnar / disk-columnar
  ;; path, whose argument reads bottom out on this backend.
  ;;
  ;; **Both routing states, one path.**  The argument roots are resident in the fallback
  ;; whether or not a snapshot is mapped: unmapped they are *written* there (`route ⇒
  ;; :fallback`), and a mapped image loads them there from the resident `roots-fallback.nippy`
  ;; blob — they ride the resident blob, NOT the mapped run (`disk/index_snapshot.clj`,
  ;; "The residency split"; `mapped?` and the `m`/`mkeys` columns concern only the
  ;; int-routed families).  So this needs no mapped/unmapped branch: `mapped?` never moves
  ;; an argument-root posting out of the fallback's `::arg` trie, and the delegate is the
  ;; correct native read in either state.  (The fallback's own `ArgColumns` is the `Object`
  ;; default on any non-memory fallback, so this stays correct even were the fallback
  ;; swapped — it would only lose the trie collapse, never an answer.)
  kv/ArgColumns
  (arg-scoped-members   [_ pred pos term]   (kv/arg-scoped-members   fallback pred pos term))
  (arg-scoped-intersect [_ pred pos-terms]  (kv/arg-scoped-intersect fallback pred pos-terms))
  (arg-agnostic-members [_ pos term]        (kv/arg-agnostic-members fallback pos term))
  (arg-agnostic-count   [_ pos term]        (kv/arg-agnostic-count   fallback pos term)))

(defn dense-roots
  "A key-interning `KvBackend` sharing `dict` (the columnar trie's token dictionary) so a
  term interned by the trie and by a root get the same id."
  [dict]
  (->DenseRoots dict (Long2ObjectOpenHashMap.) (mem/->MemoryKvBackend (atom {}))
                nil nil nil 0))

(defn fallback-entries
  "The entries the routed families do **not** claim.  That is the term roster and the
  slot roster (names, not handles) — but also the predicate-scoped argument roots,
  which are **fact-scaled**: a posting per `[pred pos term]` triple the stored facts
  exhibit.  A snapshot writes all of it as one nippy blob rather than a column, and
  loads it resident, so the arg-root mass sits outside the mapped-run residency split
  (`disk/index_snapshot.clj`, \"The residency split\")."
  [^DenseRoots b] (kv/kv-entries (.-fallback b)))

(defn load-fallback! [^DenseRoots b entries] (kv/kv-load (.-fallback b) entries) nil)

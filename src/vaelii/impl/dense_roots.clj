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
  — the slot roster and the term roster (whose members are *names*, not handles), a
  scalar, a counter, the contract test's synthetic keys — falls back to a plain in-memory
  backend (in the columnar store the trie is native, so no `[:trie …]` key ever reaches
  here).

  **Every handle family routes**, the predicate-scoped argument roots included: their
  `(pred, pos)` scope is interned to a dense id of its own (`argfam-id`) and rides the
  `pos` field, which no other family uses.  So the fallback holds only vocabulary-scaled
  name sets, and the fact-scaled mass is one packed map — or, under a snapshot, one
  mapped run.  Single-writer, like every index;
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
;; The argument roots. `[:argument-root pred pos term]` carries two names where every
;; other family carries one, and the packed long has one term field — so the `(pred, pos)`
;; scope is interned to an id of its own and rides `pos`, which no other family uses
;; (they all pass 0). See `argfam-id`.
(def ^:private ^:const F-ARG     2)
(def ^:private ^:const F-TERM    3)
(def ^:private ^:const F-RULE-A  4)
(def ^:private ^:const F-RULE-C  5)
(def ^:private ^:const F-EXC-P   6)
(def ^:private ^:const F-ROSTER  7)

(def ^:private roster-key (bit-shift-left (long F-ROSTER) 56))   ; the exception roster, a single posting

;; Each field is masked to its own width, and those widths are the invariant that makes
;; `unpack` the *exact* inverse of `route` rather than an inverse over the values the
;; callers happen to pass.  A value one bit past its field would carry into the next one
;; and the key would decode as another family's — `[:argument-root …]` at a scope id of
;; 2²⁴ reads back as `[:term-index …]`, and a routed read answers a posting that is not
;; its own with nothing to signal it.  `argfam-id`'s ceiling is what keeps the scope in
;; range; the masks make the failure unrepresentable rather than merely unreached.  Three
;; `bit-and`s are free on a path every routed read and write takes, where a runtime width
;; assert would not be.
(defn- packed [family pos id]
  (bit-or (bit-shift-left (bit-and (long family) 0xff) 56)
          (bit-shift-left (bit-and (long pos) 0xffffff) 32)
          (bit-and (long id) 0xffffffff)))

(defn- fam-key
  "The packed long for a family key over `term`, or `:absent` when a *read* names a term
  the dictionary has never interned (so the posting cannot exist).  `intern?` allocates."
  [dict family pos term intern?]
  (let [id (if intern? (tok/intern-token! dict term) (tok/token-id dict term))]
    (if (neg? id) :absent (packed family pos id))))            ; auto-boxes to Long

;; ---- the argument family ------------------------------------------------
;; `[:argument-root pred pos term]` is the one key with two names in it, and `packed` has
;; one term field.  The room is in `pos`: 24 bits reserved for an argument position, which
;; never exceeds an arity, and which every other family passes 0.  So the *pair* is
;; interned — its own dense id space, in its own dictionary — and rides those 24 bits.
;;
;; The pair space is bounded by (distinct predicates × their arities), never by facts, so
;; a 24-bit field is the right size rather than a lucky one: the audited corpus holds ~86k
;; predicates against 16.7M pairs.  `argfam-ceiling` asserts that instead of assuming it.

(def ^:private ^:const argfam-bits 24)
;; a var rather than a `^:const`, so the refusal can be driven in a test by lowering it
;; instead of by minting 16.7M pairs.  It is read once per pair intern, against the
;; dictionary's size.
(def ^:private argfam-ceiling (bit-shift-left 1 argfam-bits))

(defn- argfam-id
  "The dense id for an argument root's `(pred, pos)` scope: `-1` when a *read* names a
  pair nothing has interned (so the posting cannot exist), else the id.

  `intern?` allocates, and allocating also interns `pred` into the **term** dictionary.
  That is not incidental — a snapshot writes this table as durable token ids, so a pair
  whose predicate the term dictionary never saw would have no id to write.  Every
  predicate carrying an argument root already has a functor root, so the intern is
  almost always a lookup; doing it here is what makes \"almost\" unnecessary to reason
  about.

  **The ceiling is consulted before the pair is minted, and that ordering is the whole
  of the refusal.**  An id allocated and *then* refused stays in the dictionary, where
  the read path — which does not intern and so never reaches the ceiling — finds it and
  packs a scope past 24 bits into a 24-bit field; `argfam-table` would write it into a
  snapshot too, and `load-argfam!`'s count check restores it happily.  So a caller that
  swallows the throw turns a refusal into a routed read answering another family's
  posting.  `token-count` is the id the dictionary hands out next (`vaelii.impl.tokens`:
  ids count up from 0, first-writer-wins), so asking it first costs one array-size read
  and mints nothing."
  ;; not a primitive-hinted fn: five args is one past what Clojure allows one to be.
  [dict argfam pred pos intern?]
  (if-not intern?
    (long (tok/token-id argfam [pred pos]))
    (if (< (long (tok/token-count argfam)) (long argfam-ceiling))
      (let [id (long (tok/intern-token! argfam [pred pos]))]
        (tok/intern-token! dict pred)
        id)
      ;; full, which refuses a *new* pair and not a scoped one: every id already handed
      ;; out is inside the field, so a pair the dictionary holds still answers.
      (let [id (long (tok/token-id argfam [pred pos]))]
        (when (neg? id)
          (throw (ex-info (str "the argument-root scope dictionary is full: "
                               (inc (long (tok/token-count argfam)))
                               " distinct (predicate, position) pairs against a ceiling of "
                               argfam-ceiling ". The pair rides 24 bits of the packed root"
                               " key, so a KB past this cannot int-route its argument roots"
                               " — take the reference index (`:index :memory`), whose keys"
                               " are boxed vectors and have no such ceiling.")
                          {:type :argument-family-ceiling :pred pred :position pos
                           :pairs (inc (long (tok/token-count argfam)))
                           :ceiling argfam-ceiling
                           :remedy {:index :memory}})))
        (tok/intern-token! dict pred)
        id))))

(defn- route
  "Map a structured index key to its packed long (a `Long`), `:absent` (a read of an
  unknown term), or `:fallback` (not an int-routed family — a scalar / counter / unknown)."
  [dict argfam k intern?]
  (if-not (vector? k)
    :fallback
    (case (nth k 0)
      :context-root (fam-key dict F-CTX  0 (nth k 1) intern?)
      :functor-root (fam-key dict F-PRED 0 (nth k 1) intern?)
      ;; the pair first: it is the half that can be absent without the term being, and a
      ;; read of an unscoped pair has no posting to find.  The
      ;; `[:argument-slot pos term]` roster stays in the fallback — its members are
      ;; predicates, not handles.
      :argument-root (let [af (argfam-id dict argfam (nth k 1) (nth k 2) intern?)]
                       (if (neg? af)
                         :absent
                         (fam-key dict F-ARG af (nth k 3) intern?)))
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
  [dict argfam ^long pk]
  (let [family (bit-shift-right pk 56)
        term   (tok/id-token dict (int (bit-and pk 0xffffffff)))]
    (case (int family)
      0 [:context-root term]
      1 [:functor-root term]
      ;; the scope dictionary is consulted on the way back out, which is what makes this
      ;; the inverse of `route` rather than a partial one: the pair id in `pos` decodes
      ;; to the two names the four-element key spells.
      2 (let [[pred pos] (tok/id-token argfam (int (bit-and (bit-shift-right pk 32) 0xffffff)))]
          [:argument-root pred pos term])
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
    whatever the routed families held.")
  (sections [b]
    "What this backend **holds**, by section — `{:routed :keys :offsets :handles :argfam
    :fallback}` — for a residency measurement (`vaelii.bench.budget`).  The objects
    themselves, never a copy: `snapshot-columns` builds fresh heap arrays to write, and
    sizing those would size a temporary rather than what a running KB holds.

    Which section carries the mass is the whole reading, so each says what it scales
    with:

    - `:routed` — the mutable map the routed families use before a snapshot is installed
      and after a write thaws one.  **Fact-scaled**: every handle family is in here.
    - `:keys` / `:offsets` / `:handles` — the installed columns.  The first two are
      vocabulary-scaled, `:handles` is the fact-scaled mass, and all three are buffers
      over the image, so they belong in a caller's *mapped* total rather than its heap
      one.
    - `:argfam` — the `(pred, pos)` scope dictionary the packed argument keys cite
      (`argfam-id`).  **Vocabulary-scaled**, bounded by distinct predicates × their
      arities.
    - `:fallback` — the backend under everything the routed families do not claim: the
      term roster and the slot roster, whose members are names rather than handles
      (`fallback-entries`).  **Vocabulary-scaled**, which is what lets a snapshot write
      it as one nippy blob.

    The heap/mapped split is the caller's to make from the objects — a buffer says
    whether it is direct — so this reports the shape and judges nothing."))

(defn- members
  "The set at `k`, from whichever place the routed families live in."
  [this dict argfam ^Long2ObjectOpenHashMap m fallback k]
  (let [r (route dict argfam k false)]
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
  [this dict argfam ^Long2ObjectOpenHashMap m fallback k]
  (let [r (route dict argfam k false)]
    (cond
      (instance? Long r) (if (mapped? this)
                           (let [i (-find-key this (long r))]
                             (when-not (neg? i) (mapped-ints this i)))
                           (.get m (long r)))
      (= :fallback r)    (kv/kv-members fallback k)
      :else              nil)))                                  ; :absent

(deftype DenseRoots [dict argfam ^Long2ObjectOpenHashMap m fallback
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

  (sections [_]
    {:routed m :keys mkeys :offsets moff :handles mhandles
     :argfam argfam :fallback fallback})

  kv/KvBackend
  ;; `kv-get` reads the fallback alone, and that is the contract rather than an omission:
  ;; a routed family holds a posting, never a scalar, so `kv-get` on one is nil — which is
  ;; what `dense_routing_test` reads to tell a routed key from a fallback key.  Counters
  ;; are scalars and route nowhere, so the two increments follow it down.
  (kv-get  [_ k]   (kv/kv-get  fallback k))
  (kv-increment [_ k]   (kv/kv-increment fallback k))
  (kv-decrement [_ k]   (kv/kv-decrement fallback k))

  ;; A whole-posting put and a delete are the two ops the index's own writes never issue
  ;; on a root family — `index-sentex` adds and removes members — so only `kv_backend_test`
  ;; exercises them, and only there does a routed key that took the fallback's answer show
  ;; up: it would write a boxed entry the routed reads cannot see, and leave the packed
  ;; posting standing under a key a dump reports as deleted.
  (kv-put [this k v]
    (let [r (route dict argfam k true)]                          ; intern ⇒ never :absent
      (if (instance? Long r)
        (do (-thaw-roots! this)
            (.put m (long r) (reduce dense/padd! (dense/int-postings) v)))
        (kv/kv-put fallback k v)))
    nil)
  (kv-delete [this k]
    (let [r (route dict argfam k false)]
      (cond
        (instance? Long r) (do (-thaw-roots! this) (.remove m (long r)))
        (= :fallback r)    (kv/kv-delete fallback k)))           ; :absent ⇒ nothing to drop
    nil)

  (kv-add-to-set [this k mem]
    (let [r (route dict argfam k true)]                                 ; intern ⇒ never :absent
      (if (instance? Long r)
        (let [_  (-thaw-roots! this)                             ; a write leaves the mapped tail
              pk (long r)
              p  (or (.get m pk) (let [p (dense/int-postings)] (.put m pk p) p))]
          (dense/padd! p mem))
        (kv/kv-add-to-set fallback k mem)))
    nil)
  (kv-remove-from-set [this k mem]
    (let [r (route dict argfam k false)]
      (cond
        (instance? Long r) (do (-thaw-roots! this)
                               (when-let [p (.get m (long r))]
                                 (dense/prem! p mem)
                                 (when (zero? (dense/pcard p)) (.remove m (long r)))))
        (= :fallback r)    (kv/kv-remove-from-set fallback k mem)))          ; :absent ⇒ nothing to remove
    nil)
  (kv-members [this k] (members this dict argfam m fallback k))
  ;; the probe routes exactly as `kv-count` does — a term the dictionary never interned
  ;; has no posting, so `:absent` is a false rather than a lookup
  (kv-member? [this k mem]
    (let [r (route dict argfam k false)]
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
    (let [r (route dict argfam k false)]
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
      (let [ps (mapv #(posting this dict argfam m fallback %) ks)]
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
              :remove-from-set (do (kv/kv-remove-from-set this k a) nil)
              ;; the one refusal every adapter spells — see `vaelii.impl.dense-kv`
              (kv/unknown-op! op)))
          ops))
  ;; The portable projection has to undo *both* of this backend's compressions: the
  ;; interned key (through `unpack`, against the shared dictionary) and the `IntPostings`
  ;; value.  The two sides are enumerated together because a key routed to the fallback
  ;; is as much an index entry as a packed one.
  (kv-entries [this]
    (concat (if (mapped? this)
              (map (fn [i]
                     (let [pk (.get ^LongBuffer mkeys (int i))]
                       [(unpack dict argfam pk) (mapped-members this i)]))
                   (range mn))
              (map (fn [k] (let [pk (long k)] [(unpack dict argfam pk) (dense/pmembers (.get m pk))]))
                   (iterator-seq (.iterator (.keySet m)))))
            (kv/kv-entries fallback)))
  (kv-load [this entries]
    (-thaw-roots! this)
    (doseq [[k v] entries]
      (let [r (route dict argfam k true)]                                ; intern ⇒ never :absent
        (if (instance? Long r)
          (.put m (long r) (reduce dense/padd! (dense/int-postings) v))
          (kv/kv-put fallback k v))))
    nil)

  (kv-clear! [_]
    (.clear m)
    (set! mkeys nil) (set! moff nil) (set! mhandles nil) (set! mn (int 0))
    ;; the scope ids are only meaningful against the keys citing them, and every one of
    ;; those has just gone — a surviving dictionary would hand the next load ids nothing
    ;; decodes.
    (tok/clear-tokens! argfam)
    (kv/kv-clear! fallback)
    nil))

;; ---- the argument columns, and why this backend takes the default ------
;;
;; `ArgColumns` (`vaelii.impl.kv`) names the three shapes a settle asks the
;; argument-root family for: a scoped leaf, the predicate-agnostic union at a
;; `(pos, term)` node, and that node's cardinality.  The in-memory backend overrides it
;; with a counted `::arg` trie and answers all three as node reads; every other backend
;; takes the `Object` default, which spells the keys and folds the generic set ops.
;;
;; This backend takes the default, and the two halves of that are worth separating.
;;
;; **The scoped reads are packed reads.**  `arg-scoped-members` is one packed-long lookup
;; and `arg-scoped-intersect` one `kv-intersect` over packed keys — no consed vector, no
;; `doEquiv`, and the narrowing runs in the postings' own representation, a mapped run
;; included.  These are the reads `sentexes-with-args` makes for a named functor, which is
;; the overwhelmingly common query shape.
;;
;; **The agnostic reads cost one extra lookup.**  The default reaches them over the
;; slot roster — `[:argument-slot pos term]` → the predicates present there — and then
;; unions the scoped postings.  That roster is *one predicate* in the common case (a
;; term occupies a given position under one predicate; `kv.clj`, `sentexes-with-arg`),
;; so the union is a single set handed straight back and the cost over a maintained node
;; union is the roster read itself.  A handful of predicates is a handful of packed
;; lookups.
;;
;; Maintaining an agnostic union here instead would mean a second posting per
;; `(pos, term)` holding what the scoped postings already hold — the family's whole
;; fact-scaled mass, stored twice — to save one lookup on a read that is usually a union
;; of one.  The roster is already maintained and already vocabulary-scaled.  So the
;; default is the right reading of this representation rather than a gap in it, and the
;; trie's advantage stays where it is paid for: in RAM, on the memory backend.

(defn dense-roots
  "A key-interning `KvBackend` sharing `dict` (the columnar trie's token dictionary) so a
  term interned by the trie and by a root get the same id."
  [dict]
  (->DenseRoots dict (tok/token-dict) (Long2ObjectOpenHashMap.)
                (mem/->MemoryKvBackend (atom {}))
                nil nil nil 0))

(defn fallback-entries
  "The entries the routed families do **not** claim: the term roster and the slot roster,
  whose members are *names* rather than handles.  Both are **vocabulary-scaled**, which
  is what lets a snapshot write them as one nippy blob and load them resident without
  the blob tracking the fact count (`disk/index_snapshot.clj`, \"The residency split\")."
  [^DenseRoots b] (kv/kv-entries (.-fallback b)))

(defn load-fallback! [^DenseRoots b entries] (kv/kv-load (.-fallback b) entries) nil)

;; ---- the scope dictionary, as a snapshot section ------------------------
;; The packed argument keys cite scope ids, so an image that carries the keys has to
;; carry the table that decodes them.  It rides `roots.csr` — the file whose key column
;; is its only reader — rather than a log beside `tokens.log`, and the reason is the
;; failure each shape can have.  `tokens.log` is durable ground truth: appended as facts
;; arrive, cited by the mapped trie edges, and able to disagree with an image written at
;; some other time — which is what `:duplicate-tokens` exists to repair.  This table is
;; written in the same pass as the column that cites it and discarded with it, so the two
;; cannot drift apart at all.  A second log would buy nothing and inherit that repair.

(defn argfam-table
  "The scope dictionary as `{:preds int[] :positions int[]}`, indexed by scope id, with
  each predicate taken through `remap` into the durable dictionary's id space — the same
  `int[]` the packed keys' term halves are remapped by.

  A pair's predicate is interned into the term dictionary when the pair is
  (`argfam-id`), so every id here has a term id to be written as."
  [^DenseRoots b ^ints remap]
  (let [af (.-argfam b)
        n  (long (tok/token-count af))
        ps (int-array n)
        qs (int-array n)]
    (dotimes [i n]
      (let [[pred pos] (tok/id-token af i)]
        (aset ps i (int (aget remap (int (tok/token-id (.-dict b) pred)))))
        (aset qs i (int pos))))
    {:preds ps :positions qs}))

(defn load-argfam!
  "Rebuild the scope dictionary from a snapshot's table, ids implied by position — the
  same first-writer-wins order `vaelii.impl.tokens` allocates in, so an id read out of a
  packed key names the pair it named when the image was written."
  [^DenseRoots b ^ints preds ^ints positions n]
  (let [af   (.-argfam b)
        dict (.-dict b)]
    (tok/clear-tokens! af)
    (dotimes [i (long n)]
      (tok/intern-token! af [(tok/id-token dict (aget preds i)) (aget positions i)]))
    (let [loaded (long (tok/token-count af))]
      (when (not= loaded (long n))
        (throw (ex-info (str "the argument-root scope dictionary reloaded as " loaded
                             " entries where the image holds " n
                             " — the ids the packed keys cite have shifted")
                        {:type :torn-snapshot :loaded loaded :entries n})))))
  nil)


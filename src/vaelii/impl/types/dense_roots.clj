;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns ^{:clojure.tools.namespace.repl/load false :clojure.tools.namespace.repl/unload false}
 vaelii.impl.types.dense-roots
  "The columnar index's key-interning root backend, as a held namespace
  (`vaelii.impl.types.prover` states what that means).  `DenseRoots` mutates its own
  fields, which only its inline methods can do, so the type and the code it calls live
  here together; it calls only held namespaces.  Building one, and the snapshot sections
  it is written into, are `vaelii.impl.dense-roots`."
  (:require [clojure.set :as set]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.tokens :as tok]
            [vaelii.impl.types.postings :as postings]
            [vaelii.impl.types.snapshot :as snapshot-types])
  (:import [it.unimi.dsi.fastutil.longs Long2ObjectOpenHashMap]
           [java.nio IntBuffer LongBuffer]))

;; family tags (bits 56-63); pos in bits 32-55; term-id in bits 0-31 (≫ 100M)
(def ^:private ^:const F-CTX     0)
;; The leaves of the count tries ending in the context.  `[:argument-root :handles [pred
;; pos term ctx]]` carries three names beside the term, and the packed long has one term
;; field — so the `(pred, pos, ctx)` scope is interned to an id of its own and rides `pos`,
;; which the flat families do not use (they pass 0).  Every other count trie's leaf
;; `[key ctx]` rides the context's scope `(ctx, 0, ctx)` the same way, its term field
;; holding `key`; no argument position is 0, so the two scope shapes cannot meet.  See
;; `argfam-id`.
(def ^:private ^:const F-PEXT    1)
(def ^:private ^:const F-ARG     2)
(def ^:private ^:const F-TERM    3)
(def ^:private ^:const F-RULE-A  4)
(def ^:private ^:const F-RULE-C  5)
(def ^:private ^:const F-EXC-P   6)
(def ^:private ^:const F-ROSTER  7)
;; The count tries' nodes, from 8 up: their members are contexts, held as their ids in the
;; shared dictionary (`ctx-family?`).  `[:argument-root :children [pred pos term]]` rides
;; the `(pred, pos)` scope; the other three nodes `[key]` hold `key` in the term field and
;; 0 in `pos`.  An argument node's count is not stored: it is the sum of its leaves' sizes
;; (`node-count`).  The other three counts are vocabulary-scaled, one per predicate or rule
;; key, and are ordinary counters in the fallback.
(def ^:private ^:const F-ARG-CTX    8)
(def ^:private ^:const F-PEXT-CTX   9)
(def ^:private ^:const F-RULE-A-CTX 10)
(def ^:private ^:const F-RULE-C-CTX 11)
;; The rule extent, `[:rule-extent :handles [kind ctx]]` and its node's children, numbered
;; after the others so no family above changes its number.
(def ^:private ^:const F-RULE-X     12)
(def ^:private ^:const F-RULE-X-CTX 13)
;; The opposed family: a body's leaf `[:opposed :handles [body ctx]]` and its node's
;; children, then the members by context `[:opposed-in ctx]`, a flat family like the
;; context root.
(def ^:private ^:const F-OPP        14)
(def ^:private ^:const F-OPP-CTX    15)
(def ^:private ^:const F-OPP-IN     16)
;; The mint family: the `:mint` trie's leaf `[term ctx]` and its node's children, and the
;; `:mint-in` leaf `[ctx]`, a flat posting under the context alone.  The `:mint-in` node's
;; children and every mint count stay in the fallback, one entry each per context or term.
(def ^:private ^:const F-MINT       17)
(def ^:private ^:const F-MINT-CTX   18)
(def ^:private ^:const F-MINT-IN    19)
;; The self-tuple trie: a functor's leaf `[:self-tuple :handles [pred ctx]]` and its node's
;; children.
(def ^:private ^:const F-SELF       20)
(def ^:private ^:const F-SELF-CTX   21)

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

;; ---- the scoped families ------------------------------------------------
;; The argument trie's keys carry two or three names beside the term — a node
;; `[pred pos term]`, a leaf `[pred pos term ctx]` — and `packed` has one term field.  The
;; room is in `pos`: 24 bits reserved for an argument position, which never exceeds an
;; arity, and which every flat family passes 0.  So the *scope* — `[pred pos]` for a
;; node, `[pred pos ctx]` for a leaf — is interned, in one dictionary of its own, and
;; rides those 24 bits.  Every other count trie's leaf `[key ctx]` takes its context's
;; scope `[ctx 0 ctx]`, whatever the key: a mint's term and an opposed body are content,
;; and a scope per key would grow with them.
;;
;; The scope space is bounded by (distinct predicates × their arities × the contexts each
;; is stated in, plus one per context), never by facts, so a 24-bit field is the right
;; size rather than a lucky one: tens of thousands of predicates of small arity, each
;; stated in a handful of contexts, sit well under 16.7M scopes.  `argfam-ceiling` asserts
;; that instead of assuming it.

(def ^:private ^:const argfam-bits 24)
;; a var rather than a `^:const`, so the refusal can be driven in a test by lowering it
;; instead of by minting 16.7M scopes.  It is read once per scope intern, against the
;; dictionary's size.
(def ^:private argfam-ceiling (bit-shift-left 1 argfam-bits))

(defn- argfam-id
  "The dense id for an argument-trie key's scope (`[pred pos]` or `[pred pos ctx]`): `-1`
  when a *read* names a scope nothing has interned (so the posting cannot exist), else the
  id.

  `intern?` allocates, and allocating also interns the scope's `pred` and `ctx` into the
  **term** dictionary.  That is not incidental — a snapshot writes this table as durable
  token ids, so a scope whose names the term dictionary never saw would have no id to
  write.  Every predicate carrying an argument root already has a predicate extent, and
  every context a context root, so the intern is almost always a lookup; doing it here is what
  makes \"almost\" unnecessary to reason about.

  **The ceiling is consulted before the scope is minted, and that ordering is the whole
  of the refusal.**  An id allocated and *then* refused stays in the dictionary, where
  the read path — which does not intern and so never reaches the ceiling — finds it and
  packs a scope past 24 bits into a 24-bit field; `argfam-table` would write it into a
  snapshot too, and `load-argfam!`'s count check restores it happily.  So a caller that
  swallows the throw turns a refusal into a routed read answering another family's
  posting.  `token-count` is the id the dictionary hands out next (`vaelii.impl.tokens`:
  ids count up from 0, first-writer-wins), so asking it first costs one array-size read
  and mints nothing."
  [dict argfam scope intern?]
  (letfn [(names! [] (doseq [n (cons (nth scope 0) (drop 2 scope))] (tok/intern-token! dict n)))]
    (if-not intern?
      (long (tok/token-id argfam scope))
      (if (< (long (tok/token-count argfam)) (long argfam-ceiling))
        (let [id (long (tok/intern-token! argfam scope))]
          (names!)
          id)
        ;; full, which refuses a *new* scope and not a held one: every id already handed
        ;; out is inside the field, so a scope the dictionary holds still answers.
        (let [id (long (tok/token-id argfam scope))]
          (when (neg? id)
            (throw (ex-info (str "the argument-root scope dictionary is full: "
                                 (inc (long (tok/token-count argfam)))
                                 " distinct (predicate, position[, context]) scopes against a"
                                 " ceiling of " argfam-ceiling ". The scope rides 24 bits of the"
                                 " packed root key, so a KB past this cannot int-route its"
                                 " argument roots — take the reference index (`:index"
                                 " :memory`), whose keys are boxed vectors and have no such"
                                 " ceiling.")
                            {:type :argument-family-ceiling :pred (nth scope 0)
                             :position (nth scope 1) :scope scope
                             :pairs (inc (long (tok/token-count argfam)))
                             :ceiling argfam-ceiling
                             :remedy {:index :memory}})))
          (names!)
          id)))))

(defn- arg-key
  "The packed long for an argument-trie key — a leaf `[pred pos term ctx]` under `F-ARG`,
  a node's children `[pred pos term]` under `F-ARG-CTX` — or `:absent`.  The scope
  first: it is the half that can be absent without the term being, and a read of an
  unscoped key has no posting to find."
  [dict argfam family path intern?]
  (let [[pred pos term] path
        af (argfam-id dict argfam (if (= family F-ARG) [pred pos (nth path 3)] [pred pos]) intern?)]
    (if (neg? af) :absent (fam-key dict family af term intern?))))

(defn- ctx-leaf-key
  "The packed long for a count trie's leaf `[key ctx]` under `family`, its scope the
  context's `[ctx 0 ctx]`, or `:absent`."
  [dict argfam family [k ctx] intern?]
  (let [af (argfam-id dict argfam [ctx 0 ctx] intern?)]
    (if (neg? af) :absent (fam-key dict family af k intern?))))

(defn- ctx-trie-key
  "`route`'s answer for a key of a count trie whose node is `[key]`: the leaf under
  `leaf-family`, the node's children under `node-family`, and the count in the fallback."
  [dict argfam leaf-family node-family k intern?]
  (case (nth k 1)
    :handles  (ctx-leaf-key dict argfam leaf-family (nth k 2) intern?)
    :children (fam-key dict node-family 0 (nth (nth k 2) 0) intern?)
    :fallback))

(defn- route
  "Map a structured index key to its packed long (a `Long`), `:absent` (a read of an
  unknown term), `:count` (an argument node's count, which is answered from its leaves),
  or `:fallback` (not an int-routed family — a scalar / counter / unknown)."
  [dict argfam k intern?]
  (if-not (vector? k)
    :fallback
    (case (nth k 0)
      :context-root (fam-key dict F-CTX  0 (nth k 1) intern?)
      :predicate-extent (ctx-trie-key dict argfam F-PEXT F-PEXT-CTX k intern?)
      :rule-antecedent  (ctx-trie-key dict argfam F-RULE-A F-RULE-A-CTX k intern?)
      :rule-consequent  (ctx-trie-key dict argfam F-RULE-C F-RULE-C-CTX k intern?)
      :rule-extent      (ctx-trie-key dict argfam F-RULE-X F-RULE-X-CTX k intern?)
      :opposed          (ctx-trie-key dict argfam F-OPP F-OPP-CTX k intern?)
      :opposed-in       (fam-key dict F-OPP-IN 0 (nth k 1) intern?)
      :mint             (ctx-trie-key dict argfam F-MINT F-MINT-CTX k intern?)
      :mint-in          (if (= :handles (nth k 1))
                          (fam-key dict F-MINT-IN 0 (nth (nth k 2) 0) intern?)
                          :fallback)
      :self-tuple       (ctx-trie-key dict argfam F-SELF F-SELF-CTX k intern?)
      ;; The `[:argument-slot pos term]` roster stays in the fallback — its members are
      ;; predicates, not handles.
      :argument-root (case (nth k 1)
                       :handles  (arg-key dict argfam F-ARG (nth k 2) intern?)
                       :children (arg-key dict argfam F-ARG-CTX (nth k 2) intern?)
                       :count    :count
                       :fallback)
      :term-index (fam-key dict F-TERM 0 (nth k 1) intern?)
      :exception-index (if (= :rules (nth k 1))
                         roster-key                                         ; already a boxed Long
                         (fam-key dict F-EXC-P 0 (nth k 1) intern?))
      :fallback)))

(defn- ctx-family?
  "Does packed key `pk` hold a node's contexts (token ids) rather than handles?"
  [^long pk]
  (let [f (bit-shift-right pk 56)]
    (or (<= (long F-ARG-CTX) f (long F-RULE-C-CTX)) (== f (long F-RULE-X-CTX))
        (== f (long F-OPP-CTX)) (== f (long F-MINT-CTX)) (== f (long F-SELF-CTX)))))

(defn- unpack
  "The inverse of `route`'s packing: a packed long back to the structured key it stands
  for.  It covers every family `packed` can construct, so the two are each other's
  inverse whatever `route` chooses to send to the fallback — a family routed there
  instead comes back from the fallback's own enumeration, verbatim, and neither path can
  drop an entry."
  [dict argfam ^long pk]
  (let [family (bit-shift-right pk 56)
        term   (tok/id-token dict (int (bit-and pk 0xffffffff)))
        ;; the scope dictionary is consulted on the way back out, which is what makes this
        ;; the inverse of `route` rather than a partial one: the scope id in `pos` decodes
        ;; to the names the key spells around the term.
        scope  #(tok/id-token argfam (int (bit-and (bit-shift-right pk 32) 0xffffff)))
        leaf   (fn [tag] [tag :handles [term (nth (scope) 2)]])]
    (case (int family)
      0  [:context-root term]
      1  (leaf :predicate-extent)
      2  (let [[pred pos ctx] (scope)] [:argument-root :handles [pred pos term ctx]])
      3  [:term-index term]
      4  (leaf :rule-antecedent)
      5  (leaf :rule-consequent)
      6  [:exception-index term]
      7  [:exception-index :rules]
      8  (let [[pred pos] (scope)] [:argument-root :children [pred pos term]])
      9  [:predicate-extent :children [term]]
      10 [:rule-antecedent :children [term]]
      11 [:rule-consequent :children [term]]
      12 (leaf :rule-extent)
      13 [:rule-extent :children [term]]
      14 (leaf :opposed)
      15 [:opposed :children [term]]
      16 [:opposed-in term]
      17 (leaf :mint)
      18 [:mint :children [term]]
      19 [:mint-in :handles [term]]
      20 (leaf :self-tuple)
      21 [:self-tuple :children [term]])))

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
  (^:private -find-key [b pk] "Index of packed key `pk` in the mapped column, or -1.")
  (^:private -slice    [b i]  "The i'th mapped posting as `[lo hi)` into the handle run.")
  (^:private mapped-members [b i] "The i'th mapped posting as a Clojure set of Longs.")
  (^:private mapped-ints [b i]
    "The i'th mapped posting copied out of the buffer as an ascending `int[]` — the
    boxing-free read beside `mapped-members`, for the intersection, which discards most of
    what it reads and would otherwise box every handle on the way past.")
  (^:private -thaw-roots! [b] "Materialize every mapped posting into `m` and drop the map.")
  (sections [b]
    "What this backend **holds**, by section — `{:routed :keys :offsets :handles :argfam
    :fallback}` — for a residency measurement (`vaelii.bench.budget`).  The objects
    themselves, never a copy: `snapshot-read` builds fresh heap arrays to write, and
    sizing those would size a temporary rather than what a running KB holds.

    Which section carries the mass is the whole reading, so each says what it scales
    with:

    - `:routed` — the mutable map the routed families use before a snapshot is installed
      and after a write thaws one.  **Fact-scaled**: every handle family is in here.
    - `:keys` / `:offsets` / `:handles` — the installed columns.  The first two are
      vocabulary-scaled, `:handles` is the fact-scaled mass, and all three are buffers
      over the image, so they belong in a caller's *mapped* total rather than its heap
      one.
    - `:argfam` — the scope dictionary the packed argument and leaf keys cite
      (`argfam-id`).  **Vocabulary-scaled**, bounded by distinct predicates × their
      arities × their contexts, plus one per context.
    - `:fallback` — the backend under everything the routed families do not claim: the
      term roster and the slot roster, whose members are names rather than handles
      (`fallback-entries`).  **Vocabulary-scaled**, which is what lets a snapshot write
      it as one nippy blob.

    The heap/mapped split is the caller's to make from the objects — a buffer says
    whether it is direct — so this reports the shape and judges nothing."))

(defn- packed-members
  "The set at a packed key, mapped or heap."
  [this ^Long2ObjectOpenHashMap m pk]
  (if (snapshot-types/snapshot-mapped? this)
    (let [i (-find-key this (long pk))]
      (if (neg? i) #{} (mapped-members this i)))
    (let [p (.get m (long pk))] (if p (postings/pmembers p) #{}))))

(defn- packed-posting
  "The posting at a packed key in the representation it is stored in, or nil — the
  boxing-free twin of `packed-members`, for the narrowing."
  [this ^Long2ObjectOpenHashMap m pk]
  (if (snapshot-types/snapshot-mapped? this)
    (let [i (-find-key this (long pk))]
      (when-not (neg? i) (mapped-ints this i)))
    (.get m (long pk))))

(defn- packed-count
  "The cardinality at a packed key — a slice width while mapped, a posting's own count
  on the heap."
  [this ^Long2ObjectOpenHashMap m pk]
  (if (snapshot-types/snapshot-mapped? this)
    (let [i (-find-key this (long pk))]
      (if (neg? i) 0 (let [[lo hi] (-slice this i)] (- (long hi) (long lo)))))
    (let [p (.get m (long pk))] (if p (postings/pcard p) 0))))

(defn- ctx-ids
  "The context ids a node's children posting at packed key `pk` holds, as an `int[]`, or
  nil when it holds none."
  ^ints [this ^Long2ObjectOpenHashMap m pk]
  (if (snapshot-types/snapshot-mapped? this)
    (let [i (-find-key this (long pk))]
      (when-not (neg? i) (mapped-ints this i)))
    (some-> (.get m (long pk)) postings/pints)))

(defn- ctx-members
  "A node's children as the context tokens its ids name."
  [dict ids]
  (into #{} (map #(tok/id-token dict (int %))) ids))

(defn- count-key?
  "Is `k` an argument node's count, which this backend answers from the node's leaves?"
  [k]
  (and (vector? k) (= :argument-root (nth k 0)) (= :count (nth k 1))))

(defn- node-count
  "The count at argument node `[pred pos term]`: the sum of its leaves' sizes, one leaf
  per context its children posting names.  It is computed rather than stored, so a count
  cannot disagree with the leaves, and a snapshot carries no column for it."
  [this dict argfam m [pred pos term]]
  (let [pair (long (argfam-id dict argfam [pred pos] false))
        tid  (long (tok/token-id dict term))]
    (if (or (neg? pair) (neg? tid))
      0
      (let [ids (ctx-ids this m (packed F-ARG-CTX pair tid))]
        (if (nil? ids)
          0
          (reduce (fn [n id]
                    (let [sc (long (argfam-id dict argfam [pred pos (tok/id-token dict (int id))] false))]
                      (if (neg? sc) n (+ (long n) (long (packed-count this m (packed F-ARG sc tid)))))))
                  0 ids))))))

(defn- members
  "The set at `k`, from whichever place the routed families live in."
  [this dict argfam ^Long2ObjectOpenHashMap m fallback k]
  (let [r (route dict argfam k false)]
    (cond
      (instance? Long r) (if (ctx-family? r)
                           (ctx-members dict (ctx-ids this m r))
                           (packed-members this m r))
      (= :fallback r)    (p/kv-members fallback k)
      :else              #{})))                                  ; :absent, :count

(defn- posting
  "The set at `k` in the representation it is *stored* in — an `IntPostings` (heap), an
  ascending `int[]` (a mapped run), a Clojure set (a fallback family, or a node's
  contexts decoded from their ids), or `nil` when the key holds nothing at all.
  `kv-intersect` reads this rather than `members`, so a routed family never boxes a handle
  the narrowing is about to throw away."
  [this dict argfam ^Long2ObjectOpenHashMap m fallback k]
  (let [r (route dict argfam k false)]
    (cond
      (instance? Long r) (if (ctx-family? r)
                           (some->> (ctx-ids this m r) (ctx-members dict))
                           (packed-posting this m r))
      (= :fallback r)    (p/kv-members fallback k)
      :else              nil)))                                  ; :absent, :count

(deftype DenseRoots [dict argfam ^Long2ObjectOpenHashMap m fallback
                     ^:unsynchronized-mutable mkeys      ; LongBuffer | nil
                     ^:unsynchronized-mutable moff       ; IntBuffer  | nil
                     ^:unsynchronized-mutable mhandles   ; IntBuffer  | nil
                     ^:unsynchronized-mutable ^int mn]   ; mapped key count
  PMappedRoots
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
                p       (postings/int-postings)]
            (loop [e (long lo)] (when (< e (long hi)) (postings/padd! p (.get hs (int e))) (recur (inc e))))
            (.put m (.get ks (int i)) p))))
      (set! mkeys nil) (set! moff nil) (set! mhandles nil) (set! mn (int 0)))
    nil)

  (sections [_]
    {:routed m :keys mkeys :offsets moff :handles mhandles
     :argfam argfam :fallback fallback})

  snapshot-types/SnapshotSections
  (snapshot-mapped? [_] (some? mkeys))

  ;; The routed families as heap arrays, keys sorted and their term ids taken through
  ;; `:remap` (an `int[]` from this dictionary's ids to the durable ones).  The roster key
  ;; holds no term, so it is passed through unmapped.  The columns are read off the live
  ;; representation, so a mapped backend thaws first.
  (snapshot-read [this {remap :remap}]
    (-thaw-roots! this)
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
            (vswap! total + (long (postings/pcard (.get back (aget order i)))))
            (aset offs (inc i) (int @total)))
          (let [^ints hs (int-array (aget offs n))]
            (dotimes [i n]
              (let [pk       (aget order i)
                    ^ints ph (postings/pints (.get back pk))
                    base     (aget offs i)]
                (if (ctx-family? pk)
                  ;; a node's members are context ids, taken through the same remap as
                  ;; the keys' term halves and re-sorted, since a mapped probe
                  ;; binary-searches the run
                  (let [^ints rs (int-array (alength ph))]
                    (dotimes [e (alength ph)] (aset rs e (aget rm (aget ph e))))
                    (java.util.Arrays/sort rs)
                    (System/arraycopy rs 0 hs base (alength rs)))
                  (System/arraycopy ph 0 hs base (alength ph)))))
            {:keys order :offsets offs :handles hs})))))

  ;; A `LongBuffer` and two `IntBuffer`s over the image, plus the key count they are
  ;; sized by.  The routed map is emptied: the columns answer every routed read until a
  ;; write thaws them back into it.
  (snapshot-install! [_ {ks :keys, offsets :offsets, handles :handles, n :n}]
    (.clear m)
    (set! mkeys ks) (set! moff offsets) (set! mhandles handles) (set! mn (int n))
    nil)

  p/KvBackend
  ;; `kv-get` reads the fallback alone, and that is the contract rather than an omission:
  ;; a routed family holds a posting, never a scalar, so `kv-get` on one is nil — which is
  ;; what `dense_routing_test` reads to tell a routed key from a fallback key.  Counters
  ;; are scalars and route nowhere, so the two increments follow it down.  An argument
  ;; node's count is the exception: it is `node-count`, read off the leaves, so an
  ;; increment or decrement stores nothing and replies with the count the leaf write
  ;; before it in the batch left (`kv/node-adds` orders them so).
  (kv-get  [this k]
    (if (count-key? k) (node-count this dict argfam m (nth k 2)) (p/kv-get fallback k)))
  (kv-increment [this k]
    (if (count-key? k) (node-count this dict argfam m (nth k 2)) (p/kv-increment fallback k)))
  (kv-decrement [this k]
    (if (count-key? k) (node-count this dict argfam m (nth k 2)) (p/kv-decrement fallback k)))

  ;; A whole-posting put and a delete are the two ops the index's own writes never issue
  ;; on a root family — `index-sentex` adds and removes members — so only `kv_backend_test`
  ;; exercises them, and only there does a routed key that took the fallback's answer show
  ;; up: it would write a boxed entry the routed reads cannot see, and leave the packed
  ;; posting standing under a key a dump reports as deleted.
  (kv-put [this k v]
    (let [r (route dict argfam k true)]                          ; intern ⇒ never :absent
      (cond
        (instance? Long r)
        (do (-thaw-roots! this)
            (.put m (long r) (reduce postings/padd! (postings/int-postings)
                                     (if (ctx-family? r) (map #(tok/intern-token! dict %) v) v))))
        (= :count r) nil                                         ; read off the leaves
        :else (p/kv-put fallback k v)))
    nil)
  (kv-delete [this k]
    (let [r (route dict argfam k false)]
      (cond
        (instance? Long r) (do (-thaw-roots! this) (.remove m (long r)))
        (= :fallback r)    (p/kv-delete fallback k)))           ; :absent, :count ⇒ nothing to drop
    nil)

  ;; A node's children posting holds each context as its id in the shared dictionary,
  ;; interned on the add and looked up on the remove and the probe.
  (kv-add-to-set [this k mem]
    (let [r (route dict argfam k true)]                                 ; intern ⇒ never :absent
      (if (instance? Long r)
        (let [_  (-thaw-roots! this)                             ; a write leaves the mapped tail
              pk (long r)
              p  (or (.get m pk) (let [p (postings/int-postings)] (.put m pk p) p))]
          (postings/padd! p (if (ctx-family? pk) (tok/intern-token! dict mem) mem)))
        (p/kv-add-to-set fallback k mem)))
    nil)
  (kv-remove-from-set [this k mem]
    (let [r (route dict argfam k false)]
      (cond
        (instance? Long r) (let [mem (if (ctx-family? r) (tok/token-id dict mem) mem)]
                             (-thaw-roots! this)
                             (when-let [p (when-not (neg? (long mem)) (.get m (long r)))]
                               (postings/prem! p mem)
                               (when (zero? (postings/pcard p)) (.remove m (long r)))))
        (= :fallback r)    (p/kv-remove-from-set fallback k mem)))          ; :absent ⇒ nothing to remove
    nil)
  (kv-members [this k] (members this dict argfam m fallback k))
  ;; the probe routes exactly as `kv-count` does — a term the dictionary never interned
  ;; has no posting, so `:absent` is a false rather than a lookup
  (kv-member? [this k mem]
    (let [r   (route dict argfam k false)
          mem (if (and (instance? Long r) (ctx-family? r)) (tok/token-id dict mem) mem)]
      (cond
        (and (instance? Long r) (neg? (long mem))) false            ; a context never interned
        (instance? Long r) (if (snapshot-types/snapshot-mapped? this)
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
                               (boolean (and p (postings/pcontains? p mem)))))
        (= :fallback r)    (p/kv-member? fallback k mem)
        :else              false)))
  (kv-count [this k]
    (let [r (route dict argfam k false)]
      (cond
        (instance? Long r) (packed-count this m r)
        (= :fallback r)    (p/kv-count fallback k)
        :else              0)))
  ;; The narrowing runs in the postings' own representation (`postings/intersect-postings`),
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
                                          (map #(if (set? %) % (postings/postings-set %)) ps)))
          :else          (postings/intersect-postings ps)))))
  (kv-batch [this ops]
    (mapv (fn [[op k a]]
            (case op
              :put  (do (p/kv-put  this k a) nil)
              :delete  (do (p/kv-delete  this k) nil)
              :increment (p/kv-increment this k)
              :decrement (p/kv-decrement this k)
              :add-to-set (do (p/kv-add-to-set this k a) nil)
              :remove-from-set (do (p/kv-remove-from-set this k a) nil)
              ;; the one refusal every adapter spells — see `vaelii.impl.dense-kv`
              (p/unknown-op! op)))
          ops))
  ;; The portable projection has to undo *both* of this backend's compressions: the
  ;; interned key (through `unpack`, against the shared dictionary) and the `IntPostings`
  ;; value.  The two sides are enumerated together because a key routed to the fallback
  ;; is as much an index entry as a packed one.
  ;; A node's children decode from ids to contexts, and each argument node's count, which
  ;; is not stored, is emitted beside its children so the projection is the flat map's.
  (kv-entries [this]
    (concat (mapcat (fn [pk]
                      (let [pk  (long pk)
                            k   (unpack dict argfam pk)]
                        (cond
                          (= (long F-ARG-CTX) (bit-shift-right pk 56))
                          [[k (ctx-members dict (ctx-ids this m pk))]
                           [[:argument-root :count (nth k 2)] (node-count this dict argfam m (nth k 2))]]
                          (ctx-family? pk) [[k (ctx-members dict (ctx-ids this m pk))]]
                          :else            [[k (packed-members this m pk)]])))
                    (if (snapshot-types/snapshot-mapped? this)
                      (map (fn [i] (.get ^LongBuffer mkeys (int i))) (range mn))
                      (iterator-seq (.iterator (.keySet m)))))
            (p/kv-entries fallback)))
  ;; a node's count entry is dropped: the count is read off the leaves the load installs
  (kv-load [this entries]
    (-thaw-roots! this)
    (doseq [[k v] entries]
      (let [r (route dict argfam k true)]                                ; intern ⇒ never :absent
        (cond
          (instance? Long r)
          (.put m (long r) (reduce postings/padd! (postings/int-postings)
                                   (if (ctx-family? r) (map #(tok/intern-token! dict %) v) v)))
          (= :count r) nil
          :else (p/kv-put fallback k v))))
    nil)

  (kv-clear! [_]
    (.clear m)
    (set! mkeys nil) (set! moff nil) (set! mhandles nil) (set! mn (int 0))
    ;; the scope ids are only meaningful against the keys citing them, and every one of
    ;; those has just gone — a surviving dictionary would hand the next load ids nothing
    ;; decodes.
    (tok/clear-tokens! argfam)
    (p/kv-clear! fallback)
    nil))

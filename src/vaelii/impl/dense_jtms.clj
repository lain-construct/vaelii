;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.dense-jtms
  "The dense truth-maintenance network — the `:tms :dense` option, the default since
  0.9.0 (it holds the network in ~3.8× less RAM at corpus scale; docs/density.md).

  The JTMS is **always resident**, so its footprint is a wall in its own right
  (measured: ~467 B/node, which is ~43 GB at 100M nodes), and the decomposition
  (`lein bench-jtms`) says exactly where the bytes are:

  ```
    nodes  71%   <- 310 B/node of it is the per-node MAP OBJECT and its HAMT slot
    in     13%   <- 100% dense; RoaringBitmap measured 384x here
    groundable 13%
  ```

  Two findings shape everything below.  **The per-node scalars are already free** —
  stripping `:depth`, `:premise?` or `:datum` from the reference releases *nothing*,
  because they are shared cached objects (small `Long`s, keywords, booleans).  So the
  lever is not \"shrink the fields\", it is \"stop having a map per node\": a node here
  is a bit in a bitmap and, where it has one, an entry in a primitive-keyed map.  And
  **belief sets are the opposite regime from the index's postings** — `bench-postings`
  found RoaringBitmap a *loss* (1.07-1.45x) on the index's millions of tiny postings,
  while `:in` holds nearly every node and compresses 384x.  Both measurements are
  right; density is the variable.

  ```
    nodes / premises / in / groundable / defeated / blocked
    touched / touched-in / touched-new                         RoaringBitmap
    depths                                    Int2IntOpenHashMap  (absent => 0)
    supports / consequences   Int2ObjectOpenHashMap<IntPostings>  (absent => empty)
    a justification            columns keyed by id, never an object  (see below)
    superseded                             atom of a persistent map  (sparse)
  ```

  Two of those deserve their reasons.  **The defeat-classes are one bitmap** because
  the lattice has exactly two elements (`vaelii.impl.strength` — monotonic > default,
  and the reference already stores only the entries *above* the bottom), so \"the
  class map\" is precisely \"the set of monotonic datums\".  **Adjacency reuses Phase
  1's `IntPostings`** (a sorted `int[]` promoted to a bitmap past 128) rather than a
  bare `int[]`: a node's supports are usually one or two, but the *consequences* of a
  much-used premise — a rule handle is an antecedent of every justification it
  licensed — grow without bound, and an array-copy insert would make loading such a
  rule quadratic.

  ## Why this is a second implementation and not a swap

  `RoaringBitmap` is mutable, and the reference is an atom over one persistent map
  whose all-or-nothing mutation `jtms_atomicity_test` pins.  A mutable bitmap inside
  that value would break `swap!`'s retry semantics and let a reader observe a
  half-applied relabel — so the dense structures cannot be dropped into the reference,
  and the two ship side by side behind `vaelii.impl.jtms/Tms`.  That is the same shape
  the index took (`:memory-columnar` is a whole second trie beside `KvIndexStore`),
  and it carries the same obligation: the algorithms are duplicated here against the
  dense structures, so `jtms_dense_oracle_test` proves the two answer identically
  under randomized operation streams before either is trusted.

  **Concurrency.** A `StampedLock` gives the incidental reader the consistent view the
  single-writer contract owes one — \"a reader thread beside a writer thread (the web
  browser over a REPL's KB) is the supported shape\" (docs/storage.md), and the atom-
  over-persistent-map reference gives that reader a consistent view for free.  The dense
  network mutates its bitmaps in place, so it earns the same guarantee with a lock, and
  the lock is chosen so the engine's own single writer never pays for it.  Writers take
  the exclusive stamp — serializing exactly as the reference's `swap!` retry does.  Point
  reads (`in?`, the hottest call in the engine, one per candidate on the match path) run
  **optimistically**: no lock in the steady state, since writes are bursty and reads are
  the hot path, validated after the fact and redone under a shared read stamp only if a
  write intervened or the lock-free read saw torn state.  Iterating reads take the shared
  stamp directly — they already allocate O(nodes), so the acquisition disappears into the
  materialization, and an unlocked walk over a bitmap a writer is rewriting in place could
  tear.  A reader never observes a partially-applied relabel; it sees the state either
  fully before or fully after, exactly as it would on the reference.  The lock is
  **non-reentrant**: every protocol method below takes a stamp once and calls only
  raw-field helpers (no method re-enters), and every read body is side-effect-free (so the
  optimistic retry is safe).

  **Precondition.** `ensure-node` precedes `add-justification`, and a justification's
  antecedents already have nodes — which every engine path does.  (The reference
  tolerates the violation by growing a malformed phantom node; neither implementation
  is specified there.)

  **Limit.** The bitmaps and the fastutil maps are `int`-keyed, so a handle or
  justification id must fit a 32-bit int: the ceiling is 2^31-1 = 2,147,483,647.
  Handles are allocated in assertion order and never reused, so this bounds a KB's
  *cumulative* allocations (~2.1B), not its live node count — 21x the engine's 100M
  target, but reachable by a long-lived writer that churns assert/retract for long
  enough.  Crossing it throws an actionable error naming the ceiling and the `{:tms
  :reference}` remedy (`check-handle!`, at the two entry points a new id enters), rather
  than the bare \"integer overflow\" the cast would raise — and never a silent truncation
  that would collide two handles, so belief is never corrupted.  A KB that expects to
  churn past 2^31 pins `{:tms :reference}`, whose `Long`-keyed persistent maps have no
  such ceiling.  This is measured in density.md."
  (:require [vaelii.impl.dense-kv :as dense]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.strength :as strength])
  (:import [it.unimi.dsi.fastutil.ints Int2IntOpenHashMap Int2ObjectOpenHashMap]
           [java.util.concurrent.locks StampedLock]
           [org.roaringbitmap RoaringBitmap]))

;; ---- bitmap helpers -----------------------------------------------------

(defn- rb ^RoaringBitmap [] (RoaringBitmap.))
(defn- rb-add! ^RoaringBitmap [^RoaringBitmap r d] (.add r (int d)) r)
(defn- rb-del! ^RoaringBitmap [^RoaringBitmap r d] (.remove r (int d)) r)

(defn- rb-has?
  "Is `d` a member?  **False for anything that cannot name a node**, nil included.
  Every read here is total, because the reference's are: a persistent map answers an
  unknown key as absent, and callers rely on it — `handle-of` yields nil for a sentence
  that is not stored, and `defeat-class` / `in?` are called with that nil.  The guard
  costs a perfectly-predicted branch on the engine's hottest call."
  [^RoaringBitmap r d]
  (and (integer? d) (.contains r (int d))))

(defn- rb-longs
  "The members as a vector of Longs — the engine's handle type, so what leaves this
  namespace is indistinguishable from what the reference returns."
  [^RoaringBitmap r]
  (let [it (.getIntIterator r)]
    (loop [acc (transient [])]
      (if (.hasNext it) (recur (conj! acc (long (.next it)))) (persistent! acc)))))

(defn- rb-set [^RoaringBitmap r]
  (let [it (.getIntIterator r)]
    (loop [acc (transient #{})]
      (if (.hasNext it) (recur (conj! acc (long (.next it)))) (persistent! acc)))))

;; ---- the justification columns ------------------------------------------
;;
;; A justification is not stored as an object.  Its belief-relevant fields are held in
;; primitive columns keyed by justification id — `jtms/graph-just` projects on the way
;; in, `just-record` rebuilds one only when a caller asks, which no relabel does.  The
;; decomposition
;; (`lein bench-jtms`, a rules-heavy corpus at 3.6 justifications per node) is what
;; picks the columns:
;;
;; ```
;;   structure     118 B   the record object + its map slot   -> gone
;;   bindings       80 B   never read by belief               -> the record store's
;;   antecedents    73 B   a vector of boxed handles          -> one int[]
;;   consequence     6 B                                      -> an int column
;;   id/informant/strength/out   0 B   shared objects already
;; ```
;;
;; `informant` splits in two because it is either a rule handle or a symbol
;; (`:premise`, a special-predicate name).  Both columns' values are compared with `=`
;; and never arithmetic, so an int column and an object column answer alike; the int
;; one exists so the common case cannot depend on a caller happening to share its
;; boxed handle.  `strength` is one bitmap for the same reason the class map is: the
;; lattice has two elements.

(def ^:private ^:const no-informant
  "The `informant` column's absent marker — a justification whose informant is not a
  handle is in the object column instead."
  Integer/MIN_VALUE)

;; ---- adjacency: datum -> the justification ids touching it --------------

(defn- adj-ints
  "The justification ids at `d` as an `int[]` — empty when the node has none.  Fresh,
  so a caller may walk it while mutating the posting."
  ^ints [^Int2ObjectOpenHashMap m d]
  (if-let [p (.get m (int d))] (dense/pints p) (int-array 0)))

(defn- adj-set
  "The justification ids at `d` as a Clojure set — empty for an unknown or unusable
  datum, so the read is as total as the reference's `get-in … #{}`."
  [^Int2ObjectOpenHashMap m d]
  (if-let [p (when (integer? d) (.get m (int d)))] (dense/pmembers p) #{}))

(defn- adj-add! [^Int2ObjectOpenHashMap m d jid]
  (let [k (int d)
        p (or (.get m k) (let [fresh (dense/int-postings)] (.put m k fresh) fresh))]
    (dense/padd! p jid)
    nil))

(defn- adj-rem! [^Int2ObjectOpenHashMap m d jid]
  (when-let [p (.get m (int d))]
    (dense/prem! p jid)
    ;; empty == absent, so a torn-down node leaves no husk behind
    (when (zero? (long (dense/pcard p))) (.remove m (int d))))
  nil)

;; ---- reader/writer coordination -----------------------------------------
;;
;; A `StampedLock` restores the consistent view an incidental reader is owed
;; (docs/storage.md, the single-writer contract) without taxing the engine's own single
;; writer.  See the namespace docstring's *Concurrency* note for the shape; the three
;; macros are how every method below takes its stamp.

(defmacro ^:private with-write
  "Run `body` holding the exclusive write stamp — writers serialize here, and a reader
  under a read stamp is excluded for the duration."
  [lock & body]
  `(let [^StampedLock l# ~lock, s# (.writeLock l#)]
     (try ~@body (finally (.unlockWrite l# s#)))))

(defmacro ^:private with-read
  "Run `body` holding a shared read stamp — for the iterating reads, which materialize
  O(nodes) and would tear if they walked a bitmap a writer is rewriting in place."
  [lock & body]
  `(let [^StampedLock l# ~lock, s# (.readLock l#)]
     (try ~@body (finally (.unlockRead l# s#)))))

(defmacro ^:private opt-read
  "Optimistic read of `body` — no lock in the steady state.  Redone under a shared read
  stamp if a writer intervened (`validate` fails) or the lock-free body saw torn state
  (threw).  `body` must be pure: it can run twice, and the first run may see a
  half-applied write.  An interned-keyword sentinel (never a value a read returns) marks
  the torn/aborted case rather than a wrapper object, so the steady-state path allocates
  nothing the body itself did not — measured at 0 extra bytes against the unlocked read."
  [lock & body]
  `(let [^StampedLock l# ~lock
         st# (.tryOptimisticRead l#)]
     (if (zero? st#)
       (with-read l# ~@body)                 ; a writer holds it now — wait, don't spin
       (let [r# (try (do ~@body) (catch Throwable _# ::torn))]
         (if (and (not (identical? ::torn r#)) (.validate l# st#))
           r#
           (with-read l# ~@body))))))

;; The deftype's methods call the operations below, and those need the type itself for
;; their hints — a genuine in-file cycle, so the entry points are declared ahead of it.
(declare ensure! premise! suspend-premise! add-just! restrength-informant! defeat!
         clear-defeats! relabel-all! set-blocked! retract-datum! sweep-from! snapshot
         just-record)

(deftype DenseTms [^StampedLock lock
                   ^RoaringBitmap nodes
                   ^RoaringBitmap premises
                   ^RoaringBitmap mono-premises
                   ^Int2IntOpenHashMap depths
                   ^Int2ObjectOpenHashMap supports
                   ^Int2ObjectOpenHashMap conseqs
                   ;; the justification columns — see the block above
                   ^RoaringBitmap jids
                   ^Int2IntOpenHashMap j-conseq
                   ^Int2IntOpenHashMap j-inf
                   ^Int2ObjectOpenHashMap j-inf-sym
                   ^Int2ObjectOpenHashMap j-antes
                   ^Int2ObjectOpenHashMap j-outs
                   ^RoaringBitmap j-mono
                   ^RoaringBitmap in
                   ^RoaringBitmap groundable
                   ^RoaringBitmap defeated
                   ^RoaringBitmap blocked
                   ^RoaringBitmap touched
                   ^RoaringBitmap touched-in
                   ^RoaringBitmap touched-new
                   ^RoaringBitmap mono
                   ^clojure.lang.Atom superseded]

  ;; `@tms` yields the canonical map the reference stores natively — materialized, so
  ;; this is a testing and debugging read, never an engine path.
  clojure.lang.IDeref
  (deref [this] (with-read lock (snapshot this)))

  jtms/Tms
  (-believed? [_ datum]
    (opt-read lock (and (rb-has? in datum) (not (contains? @superseded datum)))))
  (-believed [_] (with-read lock (seq (remove @superseded (rb-longs in)))))
  (-node? [_ datum] (opt-read lock (rb-has? nodes datum)))
  (-datums [_] (with-read lock (seq (rb-longs nodes))))
  ;; O(1)/early-terminating boolean checks — a poll on the render path must neither
  ;; drain the bitmap into boxed Longs (as `(first (-datums …))` would) nor walk it
  ;; while a writer rewrites it in place.
  (-any-node? [_] (opt-read lock (not (.isEmpty ^RoaringBitmap nodes))))
  (-any-belief? [_]
    (with-read lock
      (and (not (.isEmpty ^RoaringBitmap in))
           (let [sup @superseded]
             (or (empty? sup)
                 (let [it (.getIntIterator ^RoaringBitmap in)]
                   (loop []
                     (cond
                       (not (.hasNext it))               false
                       (contains? sup (long (.next it))) (recur)
                       :else                             true))))))))
  (-depth [_ datum] (opt-read lock (if (integer? datum) (long (.get depths (int datum))) 0)))
  (-premise? [_ datum] (opt-read lock (rb-has? premises datum)))
  (-premise-strength [_ datum]
    (opt-read lock
              (when (rb-has? premises datum)
                (if (rb-has? mono-premises datum) :monotonic :default))))
  (-defeat-class [_ datum]
    (opt-read lock
              (when (rb-has? in datum) (if (rb-has? mono datum) :monotonic :default))))
  (-defeated [_] (with-read lock (rb-set defeated)))
  (-blocked [_] (with-read lock (rb-set blocked)))
  ;; the supersession map is an immutable value in an atom, always consistent on its
  ;; own — no stamp needed, and it is mutated only under the write stamp anyway
  (-superseded [_] @superseded)
  (-touched [_] (with-read lock (rb-set touched)))
  (-touched-in [_] (with-read lock (rb-set touched-in)))
  (-touched-new [_] (with-read lock (rb-set touched-new)))
  (-reset-touched [_]
    (with-write lock (.clear touched) (.clear touched-in) (.clear touched-new)) nil)
  (-supports [_ datum] (with-read lock (adj-set supports datum)))
  (-dependents [_ datum] (with-read lock (adj-set conseqs datum)))
  (-justification [this jid] (with-read lock (when (rb-has? jids jid) (just-record this jid))))
  (-justifications [this] (with-read lock (seq (mapv #(just-record this %) (rb-longs jids)))))
  (-ensure-node [this datum depth] (with-write lock (ensure! this datum depth)) nil)
  (-add-premise [this datum strength] (with-write lock (premise! this datum strength)) nil)
  (-suspend-premise [this datum] (with-write lock (suspend-premise! this datum)) nil)
  (-add-justification [this just] (with-write lock (add-just! this just)) nil)
  (-restrength-informant [this informant strength]
    (with-write lock (restrength-informant! this informant strength)) nil)
  (-relabel [this] (with-write lock (relabel-all! this)) nil)
  (-defeat [this datums] (with-write lock (defeat! this datums)) nil)
  (-clear-defeats [this] (with-write lock (clear-defeats! this)) nil)
  (-set-blocked [this jids] (with-write lock (set-blocked! this jids)) nil)
  (-update-blocked [this f] (with-write lock (set-blocked! this (f (rb-set blocked)))) nil)
  (-supersede [_ m] (with-write lock (reset! superseded (into {} m))) nil)
  (-retract [this datum] (with-write lock (retract-datum! this datum)))
  (-sweep [this seeds] (with-write lock (sweep-from! this seeds)))
  (-snapshot [this] (with-read lock (snapshot this))))

;; ---- reading a justification out of the columns --------------------------

(def ^:private ^ints no-ids (int-array 0))

(defn- j-antecedents ^ints [^DenseTms this jid]
  (or (.get ^Int2ObjectOpenHashMap (.-j-antes this) (int jid)) no-ids))

(defn- j-out ^ints [^DenseTms this jid]
  (or (.get ^Int2ObjectOpenHashMap (.-j-outs this) (int jid)) no-ids))

(defn- j-consequence
  "The consequence handle, or -1 for a justification that is not stored — the callers
  are walks over adjacency, which can name an id whose justification has been swept."
  ^long [^DenseTms this jid]
  (let [m ^Int2IntOpenHashMap (.-j-conseq this)
        k (int jid)]
    (if (.containsKey m k) (long (.get m k)) -1)))

(defn- j-informant-int
  "The informant as an int when it is a handle, else the absent marker — what
  `conferred-class` compares antecedents against, so a symbolic informant simply
  matches nothing."
  ^long [^DenseTms this jid]
  (long (.get ^Int2IntOpenHashMap (.-j-inf this) (int jid))))

(defn- j-informant [^DenseTms this jid]
  (let [i (j-informant-int this jid)]
    (if (== i no-informant)
      (.get ^Int2ObjectOpenHashMap (.-j-inf-sym this) (int jid))
      i)))

(defn- just-record
  "Rebuild the `Justification` a caller asked for.  `:bindings` is nil: the network
  keeps the graph and the record store keeps the record (`jtms/graph-just`).  Nothing
  on a relabel path calls this — the fixpoints read the columns directly."
  [^DenseTms this jid]
  (let [antes (j-antecedents this jid)
        out   (j-out this jid)]
    (jtms/->Justification
     (long jid)
     (j-informant this jid)
     (into [] (map long) antes)
     (j-consequence this jid)
     nil
     (if (rb-has? ^RoaringBitmap (.-j-mono this) jid) :monotonic :default)
     (into #{} (map long) out))))

;; ---- validity and class, against the dense structures -------------------
;;
;; These mirror `vaelii.impl.jtms`'s private `valid?` / `conferred-class` /
;; `node-class`.  The semantics are the specification (docs/nmtms.md); the
;; differential oracle is what holds the two readings of it together.

(defn- all-in?
  "Are all of `ids` believed?  A hand-rolled loop rather than `every?` over a boxed
  seq: this is the innermost test of every fixpoint iteration."
  [^ints ids ^RoaringBitmap in]
  (let [n (alength ids)]
    (loop [i 0]
      (cond (== i n) true
            (.contains in (aget ids i)) (recur (unchecked-inc i))
            :else false))))

(defn- none-in? [^ints ids ^RoaringBitmap in]
  (let [n (alength ids)]
    (loop [i 0]
      (cond (== i n) true
            (.contains in (aget ids i)) false
            :else (recur (unchecked-inc i))))))

(defn- valid?
  "Is justification `jid` satisfied — every antecedent believed, no negation-as-failure
  antecedent believed, and not blocked by its rule's exception?"
  [^DenseTms this jid ^RoaringBitmap in ^RoaringBitmap blocked]
  (and (not (.contains blocked (int jid)))
       (all-in? (j-antecedents this jid) in)
       (none-in? (j-out this jid) in)))

(defn- conferred-class
  "The class a valid justification confers: its own strength, capped by the weakest of
  its antecedents' classes — the informant excluded, since a rule is an antecedent for
  *validity*, not as a ground."
  [^DenseTms this jid ^RoaringBitmap classes]
  (let [informant (j-informant-int this jid)
        antes     (j-antecedents this jid)]
    (areduce antes i acc (if (rb-has? ^RoaringBitmap (.-j-mono this) jid) :monotonic :default)
             (let [a (aget antes i)]
               (if (== a informant)
                 acc
                 (strength/min acc (if (.contains classes a) :monotonic :default)))))))

(defn- node-class
  "The strongest support an IN datum has: its premise strength, and what each currently
  valid justification confers.  A blocked justification is not valid, so it confers
  nothing — exactly as if it were missing an antecedent."
  [^DenseTms this d ^RoaringBitmap in ^RoaringBitmap classes]
  (let [blocked ^RoaringBitmap (.-blocked this)
        live    ^RoaringBitmap (.-jids this)
        prem    (when (and (rb-has? ^RoaringBitmap (.-premises this) d)
                           (not (rb-has? ^RoaringBitmap (.-defeated this) d)))
                  (if (rb-has? ^RoaringBitmap (.-mono-premises this) d) :monotonic :default))
        ids     (adj-ints (.-supports this) d)]
    (areduce ids i acc (or prem :default)
             (let [jid (aget ids i)]
               (if (and (.contains live jid) (valid? this jid in blocked))
                 (strength/max acc (conferred-class this jid classes))
                 acc)))))

;; ---- region-local relabelling -------------------------------------------

(defn- affected-region
  "Every node whose label could move when `seeds` do: the forward closure over
  consequence justifications, seeds included."
  ^RoaringBitmap [^DenseTms this seeds]
  (let [seen (rb)
        cons ^Int2ObjectOpenHashMap (.-conseqs this)]
    (loop [stack (vec seeds)]
      (when (seq stack)
        (let [d (peek stack), stack (pop stack)]
          (if (rb-has? seen d)
            (recur stack)
            (do (rb-add! seen d)
                (let [ids (adj-ints cons d)]
                  (recur (areduce ids i acc stack
                                  (let [c (j-consequence this (aget ids i))]
                                    (if (neg? c) acc (conj acc c)))))))))))
    seen))

(defn- region-fixpoint!
  "Least fixpoint of IN over `region`, accumulated **into** `acc` — the live bitmap, with
  the region already cleared out of it, so what it holds on entry is the boundary and the
  fixpoint only ever adds region members back.  `forced-out` is forced OUT whatever its
  support (the defeated set when labelling, empty when computing groundability).

  Starting from nothing believed inside the region and only ever adding is what keeps
  support well-founded, and a least fixpoint is unique — so going local costs no order
  independence.  Semi-naive: `valid?` is monotone in `in`, so a justification is
  retried only when one of its antecedents newly enters, reached through the stored
  inverse edge.

  **It accumulates into the live bitmap rather than into a clone of it, and that is what
  makes a relabel proportional to the region rather than to the graph.**  A clone is
  proportional to the *believed set*, so adding one premise to a KB with ten million
  believed datums copied ten million bits — and a rebuild, which adds a premise per
  stored premise, was quadratic.  Measured: per-premise cost rose 14.9× across three
  million premises where the reference representation stayed flat."
  [^DenseTms this ^RoaringBitmap region cands ^RoaringBitmap acc
   ^RoaringBitmap forced-out]
  (let [blocked ^RoaringBitmap (.-blocked this)
        cons    ^Int2ObjectOpenHashMap (.-conseqs this)]
    ;; seed: the region's own premises, unless forced OUT
    (let [it (.getIntIterator (RoaringBitmap/and region ^RoaringBitmap (.-premises this)))]
      (while (.hasNext it)
        (let [d (.next it)]
          (when-not (.contains forced-out d) (.add acc d)))))
    (loop [stack (vec cands)]
      (if (empty? stack)
        nil
        (let [jid   (peek stack)
              stack (pop stack)
              c     (j-consequence this jid)]
          (if (and (not (neg? c))
                   (rb-has? region c)
                   (not (rb-has? acc c))
                   (not (rb-has? forced-out c))
                   (valid? this jid acc blocked))
            (do (rb-add! acc c)
                (let [ids (adj-ints cons c)]
                  (recur (areduce ids i a stack (conj a (aget ids i))))))
            (recur stack)))))))

(defn- region-classes!
  "Defeat-classes for `region` under `in`, as a least fixpoint — every in-region IN
  node starts at the lattice's bottom and the recursive equation is iterated to
  stability, so the answer is unique and cannot depend on visit order.

  `classes` is the live monotonic bitmap with the region already cleared out of it, and
  is mutated in place for the same reason `region-fixpoint!` is: an OUT datum has no
  class and an IN one restarts at `:default` (absent from the bitmap), so what is left
  outside the region is boundary that does not move.

  The bitmap *is* the whole class map: the lattice has two elements.  A boundary node
  whose class could move would have an antecedent in the region and so would be in it."
  [^DenseTms this ^RoaringBitmap region ^RoaringBitmap in ^RoaringBitmap classes]
  (let [cons    ^Int2ObjectOpenHashMap (.-conseqs this)
        members (RoaringBitmap/and region in)]
    ;; The lattice has height one, so a member rises at most once and the worklist only
    ;; ever ADDS — which is exactly what makes this the least fixpoint rather than some
    ;; fixpoint.
    (loop [stack (rb-longs members)]
      (if (empty? stack)
        nil
        (let [d     (peek stack)
              stack (pop stack)]
          (if (or (rb-has? classes d)
                  (not= :monotonic (node-class this d in classes)))
            (recur stack)
            (do (rb-add! classes d)
                (let [ids (adj-ints cons d)]
                  (recur (areduce ids i acc stack
                                  (let [c (j-consequence this (aget ids i))]
                                    (if (and (not (neg? c)) (rb-has? in c))
                                      (conj acc c)
                                      acc))))))))))))

(defn- relabel-region!
  "Recompute belief, groundability and the classes for `region`, holding everything
  outside it fixed — equivalent to a global relabel whenever the region is the
  affected closure of what changed, and proportional to the region rather than to the
  graph."
  [^DenseTms this ^RoaringBitmap region]
  (let [live    ^RoaringBitmap (.-jids this)
        sup     ^Int2ObjectOpenHashMap (.-supports this)
        ;; only the justifications that can conclude something in the region matter
        cands   (let [it (.getIntIterator region)]
                  (loop [acc (transient [])]
                    (if-not (.hasNext it)
                      (persistent! acc)
                      (let [ids (adj-ints sup (.next it))]
                        (recur (areduce ids i a acc
                                        (if (.contains live (aget ids i))
                                          (conj! a (aget ids i))
                                          a)))))))
        in      ^RoaringBitmap (.-in this)
        ground  ^RoaringBitmap (.-groundable this)
        mono    ^RoaringBitmap (.-mono this)
        ;; Which of the region this window has not relabelled yet, and of those which are
        ;; believed *now* — read FIRST, because the fixpoint below overwrites the region's
        ;; labels in place and the prior ones are then gone.  See `jtms/touched-in`.
        fresh    (RoaringBitmap/andNot region ^RoaringBitmap (.-touched this))
        fresh-in (RoaringBitmap/and fresh in)]
    ;; Clearing the region out of each live bitmap leaves exactly the boundary, which is
    ;; what each fixpoint starts from and holds fixed.  In place: the static `andNot`
    ;; copies every container of a bitmap the size of the believed set, where the mutating
    ;; one is a merge over the container lists and touches only the region's own.
    (.andNot in region)
    (.andNot ground region)
    ;; the two are independent — each reads and writes only its own accumulator — so the
    ;; groundability pass cannot see a half-written in-set even though the in-set is now
    ;; written in place
    (region-fixpoint! this region cands in ^RoaringBitmap (.-defeated this))
    (region-fixpoint! this region cands ground (rb))
    ;; the classes are a function of the NEW in-set, and of the current `mono` outside the
    ;; region for their boundary — so the region is cleared out of `mono` and no further
    (.andNot mono region)
    (region-classes! this region in mono)
    (.or ^RoaringBitmap (.-touched-in this) fresh-in)
    ;; A supporter's belief can flip only inside a relabelled region, so the accumulated
    ;; touched set is a superset of every handle whose belief moved this settle — what
    ;; `tax/refresh-beliefs` reads to skip a cache no moved supporter touches.
    (.or ^RoaringBitmap (.-touched this) region)
    nil))

(defn- resettle! [^DenseTms this seeds]
  (relabel-region! this (affected-region this seeds)))

;; ---- mutation -----------------------------------------------------------

(def ^:private ^:const max-handle
  "The dense network's ceiling: bitmaps and fastutil maps are `int`-keyed, so a handle or
  justification id must fit a 32-bit int.  See the namespace docstring's *Limit*."
  Integer/MAX_VALUE)

(defn- check-handle!
  "Return `x` as a `long` after checking it fits the int ceiling, throwing an actionable
  error in place of the bare `integer overflow` the cast would otherwise raise.  Called
  where a new id first enters — `ensure!` for a node handle, `add-just!` for a
  justification id; antecedents and consequences reach `add-just!` already having nodes,
  so they were checked when those nodes were made.  `kind` names what overran."
  ^long [x kind]
  (let [v (long x)]
    (when (> v max-handle)
      (throw (ex-info (str "dense TMS: " kind " " v " exceeds the 2^31-1 handle ceiling ("
                           max-handle ").  Open the KB with {:tms :reference} — its "
                           "Long-keyed network has no ceiling (docs/density.md, Phase 3).")
                      {:kind kind :value v :ceiling max-handle :remedy {:tms :reference}})))
    v))

(defn- ensure! [^DenseTms this datum depth]
  (let [d      (int (check-handle! datum "node handle"))
        depths ^Int2IntOpenHashMap (.-depths this)]
    (if (rb-has? ^RoaringBitmap (.-nodes this) d)
      (.put depths d (int (min (.get depths d) (int depth))))
      ;; the window's record of what it created, taken here because this is the only
      ;; line that knows — see `jtms/touched-new`
      (do (rb-add! ^RoaringBitmap (.-nodes this) d)
          (rb-add! ^RoaringBitmap (.-touched-new this) d)
          (.put depths d (int depth))))
    nil))

(defn- premise! [^DenseTms this datum strength-kw]
  (ensure! this datum 0)
  (rb-add! ^RoaringBitmap (.-premises this) datum)
  (if (= :monotonic strength-kw)
    (rb-add! ^RoaringBitmap (.-mono-premises this) datum)
    (rb-del! ^RoaringBitmap (.-mono-premises this) datum))
  (resettle! this [datum]))

(defn- suspend-premise!
  "Drop the premise mark and relabel the affected closure — `retract-datum!` without
  the sweep, so nothing is deleted and `premise!` puts it back exactly."
  [^DenseTms this datum]
  (when (rb-has? ^RoaringBitmap (.-nodes this) datum)
    (rb-del! ^RoaringBitmap (.-premises this) datum)
    (rb-del! ^RoaringBitmap (.-mono-premises this) datum)
    (relabel-region! this (affected-region this [datum])))
  nil)

(defn- add-just!
  "Record `just` and relabel only what it actually moves.

  The fast path is what keeps a recursive forward load linear.  A *redundant*
  justification — one whose consequence is already believed and which confers no
  stronger a class than it already holds (or is not even valid) — moves nothing: an
  already-IN node feeds its consequences identically on one witness or two.  So the
  forward closure is walked once, when a fact is *first* derived (a brand-new node has
  no consequences yet, so its region is a singleton), and every later re-derivation by
  another path is a no-op.  Any real change still takes the full resettle."
  [^DenseTms this just]
  (let [{:keys [id informant antecedents consequence out strength]} (jtms/graph-just just)
        jid   (int (check-handle! id "justification id"))
        in    ^RoaringBitmap (.-in this)
        mono  ^RoaringBitmap (.-mono this)]
    ;; The columns, in place of a stored object.  Every one is **set**, never merged:
    ;; where a map entry would have been replaced wholesale, seven columns each have to
    ;; be told, and a column left alone on a re-add would answer for the justification
    ;; the id used to name.
    (rb-add! ^RoaringBitmap (.-jids this) jid)
    (.put ^Int2IntOpenHashMap (.-j-conseq this) jid (int consequence))
    (if (integer? informant)
      (do (.put ^Int2IntOpenHashMap (.-j-inf this) jid (int informant))
          (.remove ^Int2ObjectOpenHashMap (.-j-inf-sym this) jid))
      (do (.put ^Int2IntOpenHashMap (.-j-inf this) jid (int no-informant))
          (.put ^Int2ObjectOpenHashMap (.-j-inf-sym this) jid informant)))
    (.put ^Int2ObjectOpenHashMap (.-j-antes this) jid (int-array antecedents))
    (if (seq out)
      (.put ^Int2ObjectOpenHashMap (.-j-outs this) jid (int-array out))
      (.remove ^Int2ObjectOpenHashMap (.-j-outs this) jid))
    (if (= :monotonic strength)
      (rb-add! ^RoaringBitmap (.-j-mono this) jid)
      (rb-del! ^RoaringBitmap (.-j-mono this) jid))
    (adj-add! (.-supports this) consequence id)
    (doseq [a (concat antecedents out)]
      (adj-add! (.-conseqs this) a id))
    (if (and (rb-has? in consequence)
             (or (not (valid? this jid in ^RoaringBitmap (.-blocked this)))
                 (let [cls (if (rb-has? mono consequence) :monotonic :default)]
                   (= cls (strength/max cls (conferred-class this jid mono))))))
      ;; the fast path still notes the consequence as touched, for the reason
      ;; `jtms/add-just*` records: a second witness moves what a caller *published* about
      ;; the datum while moving no label, and `touched-in` takes it unless this window has
      ;; relabelled it already
      (let [t ^RoaringBitmap (.-touched this)]
        (when-not (rb-has? t consequence)
          (rb-add! ^RoaringBitmap (.-touched-in this) consequence))
        (rb-add! t consequence))
      (resettle! this [consequence]))))

(defn- restrength-informant!
  "The dense half of `jtms/restrength-informant`: the rule-contribution slot is the
  `j-mono` bitmap, the candidate justifications are the informant's own `conseqs`
  adjacency (a firing conjoins the rule handle as an antecedent), and the informant
  column filters out a justification that merely uses the handle as an ordinary
  antecedent.  Only a bit that actually moves seeds the relabel."
  [^DenseTms this informant strength]
  (when (integer? informant)
    (let [inf   (int informant)
          jinf  ^Int2IntOpenHashMap (.-j-inf this)
          jmono ^RoaringBitmap (.-j-mono this)
          mono? (= :monotonic strength)
          ids   (adj-ints (.-conseqs this) inf)
          n     (alength ids)]
      (loop [i 0, seeds (transient [])]
        (if (< i n)
          (let [jid (aget ids i)]
            (if (and (.containsKey jinf jid) (== (.get jinf jid) inf)
                     (not= mono? (rb-has? jmono jid)))
              (do (if mono? (rb-add! jmono jid) (rb-del! jmono jid))
                  (let [c (j-consequence this jid)]
                    (recur (inc i) (if (neg? c) seeds (conj! seeds c)))))
              (recur (inc i) seeds)))
          (let [s (persistent! seeds)]
            (when (seq s) (resettle! this s))))))))

(defn- defeat! [^DenseTms this datums]
  (let [d ^RoaringBitmap (.-defeated this)]
    (doseq [x datums] (rb-add! d x))
    (resettle! this datums)))

(defn- clear-defeats!
  "Empty the derived defeated set and relabel — the basis for revival.  The region is
  the *previously* defeated nodes, so a settle that defeated nothing does no work."
  [^DenseTms this]
  (let [d   ^RoaringBitmap (.-defeated this)
        was (rb-longs d)]
    (.clear d)
    (resettle! this was)))

(defn- set-blocked!
  "Replace the blocked set and relabel what moved.  Only the justifications whose
  blocked status actually changed can move a label, so they alone seed the region —
  a call that changes nothing does no work at all."
  [^DenseTms this jids]
  (let [want    (reduce rb-add! (rb) jids)
        blocked ^RoaringBitmap (.-blocked this)
        changed (RoaringBitmap/xor want blocked)]
    (when-not (.isEmpty changed)
      (let [seeds (into [] (keep #(let [c (j-consequence this %)] (when-not (neg? c) c)))
                        (rb-longs changed))]
        (doto blocked (.clear) (.or want))
        (resettle! this seeds)))))

(defn- relabel-all!
  "Whole-graph relabel — for `recover`, which rebuilds the network from the durable
  store and so has no smaller region to work from.

  Blocking and supersession are **cleared first**: nothing about an exception or an
  equality merge is stored, so a rebuild cannot read either back, and one that merged
  into whatever was there could only ever *add* — leaving a block standing for a
  justification whose exception no longer holds.  Recovery lands unblocked and the
  caller re-evaluates."
  [^DenseTms this]
  (.clear ^RoaringBitmap (.-blocked this))
  (reset! ^clojure.lang.Atom (.-superseded this) {})
  (relabel-region! this (.clone ^RoaringBitmap (.-nodes this))))

;; ---- retraction ---------------------------------------------------------

(defn- sweep!
  "Collect the datums in `suspects` that are no longer *structurally* derivable and are
  not premises, tear them and every justification touching them out of the graph, and
  return the removals for the caller to apply to its own stores.

  Groundability ignores defeats, so a defeated node with a surviving derivation is kept
  for revival, while one whose only support was just torn down is swept.  Blocking, by
  contrast, does suppress groundability, which is what makes this the garbage collector
  for an excepted conclusion as well as for a retracted one.

  Region-local: the justifications to tear down are read off the dead nodes' own
  adjacency, never by scanning `jids` — `exceptWhen` blocks on ordinary fact arrival,
  so sweeping is routine, and a sweep that scanned the graph would make a run of them
  quadratic."
  [^DenseTms this ^RoaringBitmap suspects]
  (let [ground ^RoaringBitmap (.-groundable this)
        prem   ^RoaringBitmap (.-premises this)
        live   ^RoaringBitmap (.-jids this)
        sup    ^Int2ObjectOpenHashMap (.-supports this)
        cons   ^Int2ObjectOpenHashMap (.-conseqs this)
        dead   (into [] (remove #(or (rb-has? prem %) (rb-has? ground %)))
                     (rb-longs suspects))
        dead-jids (into #{}
                        (comp (mapcat (fn [d] (concat (adj-set sup d) (adj-set cons d))))
                              (filter #(.contains live (int %))))
                        dead)
        ;; read the informants BEFORE the columns are unlinked — a premise
        ;; justification is the caller's own and is not ours to report as removed
        removed-justs (into [] (remove #(= :premise (j-informant this %))) dead-jids)]
    (doseq [jid dead-jids]
      (let [antes (j-antecedents this jid)
            outs  (j-out this jid)
            c     (j-consequence this jid)
            k     (int jid)]
        (rb-del! live k)
        (.remove ^Int2IntOpenHashMap (.-j-conseq this) k)
        (.remove ^Int2IntOpenHashMap (.-j-inf this) k)
        (.remove ^Int2ObjectOpenHashMap (.-j-inf-sym this) k)
        (.remove ^Int2ObjectOpenHashMap (.-j-antes this) k)
        (.remove ^Int2ObjectOpenHashMap (.-j-outs this) k)
        (rb-del! ^RoaringBitmap (.-j-mono this) k)
        (adj-rem! sup c jid)
        (dotimes [i (alength antes)] (adj-rem! cons (aget antes i) jid))
        (dotimes [i (alength outs)] (adj-rem! cons (aget outs i) jid))))
    (doseq [d dead]
      (rb-del! ^RoaringBitmap (.-nodes this) d)
      (rb-del! ^RoaringBitmap (.-premises this) d)
      (rb-del! ^RoaringBitmap (.-mono-premises this) d)
      (rb-del! ^RoaringBitmap (.-mono this) d)
      ;; the swept nodes were OUT and ungroundable, so dropping them cannot move any
      ;; survivor's label — only the bookkeeping needs the removal
      (rb-del! ^RoaringBitmap (.-in this) d)
      (rb-del! ^RoaringBitmap (.-groundable this) d)
      (.remove ^Int2IntOpenHashMap (.-depths this) (int d))
      (.remove sup (int d))
      (.remove cons (int d)))
    ;; a block names a justification and a supersession names a datum, so a swept one
    ;; must lose both — an entry left behind would be reapplied to whatever reuses the id
    (doseq [jid dead-jids] (rb-del! ^RoaringBitmap (.-blocked this) jid))
    (swap! ^clojure.lang.Atom (.-superseded this) #(apply dissoc % dead))
    {:removed-sentexes dead :removed-justifications removed-justs}))

(defn- retract-datum!
  "Dependency-directed retraction: drop the premise, relabel the affected closure (a
  suspect re-derivable by another witness stays IN), then sweep what the retraction
  solely supported.  An unknown datum is a no-op — retraction is idempotent, and
  materializing the node would let the sweep collect a phantom and claim a removal that
  never happened."
  [^DenseTms this datum]
  (if-not (rb-has? ^RoaringBitmap (.-nodes this) datum)
    {:removed-sentexes [] :removed-justifications []}
    (do (rb-del! ^RoaringBitmap (.-premises this) datum)
        (rb-del! ^RoaringBitmap (.-mono-premises this) datum)
        ;; marking and relabelling walk the graph once between them: the affected
        ;; closure is both the suspect set and the region to relabel
        (let [suspects (affected-region this [datum])]
          (relabel-region! this suspects)
          (sweep! this suspects)))))

(defn- sweep-from! [^DenseTms this seeds]
  (sweep! this (affected-region this seeds)))

;; ---- the canonical snapshot ---------------------------------------------

(defn- snapshot
  "The whole network as the reference's persistent-map shape — what the differential
  oracle compares, and what `@tms` yields.  Materializes everything, so it is a testing
  and debugging surface and no engine path calls it."
  [^DenseTms this]
  (let [prem   ^RoaringBitmap (.-premises this)
        mprem  ^RoaringBitmap (.-mono-premises this)
        depths ^Int2IntOpenHashMap (.-depths this)]
    {:nodes (into {}
                  (map (fn [d]
                         [d (cond-> {:datum d
                                     :premise? (rb-has? prem d)
                                     :depth (long (.get depths (int d)))
                                     :supports (adj-set (.-supports this) d)
                                     :consequences (adj-set (.-conseqs this) d)}
                              (rb-has? prem d)
                              (assoc :premise-strength
                                     (if (rb-has? mprem d) :monotonic :default)))]))
                  (rb-longs ^RoaringBitmap (.-nodes this)))
     :justs (into {} (map (fn [jid] [jid (just-record this jid)]))
                  (rb-longs ^RoaringBitmap (.-jids this)))
     :defeated   (rb-set ^RoaringBitmap (.-defeated this))
     :blocked    (rb-set ^RoaringBitmap (.-blocked this))
     :superseded @^clojure.lang.Atom (.-superseded this)
     :classes    (into {} (map (fn [d] [d :monotonic]))
                       (rb-longs ^RoaringBitmap (.-mono this)))
     :in         (rb-set ^RoaringBitmap (.-in this))
     :groundable (rb-set ^RoaringBitmap (.-groundable this))
     :touched     (rb-set ^RoaringBitmap (.-touched this))
     :touched-in  (rb-set ^RoaringBitmap (.-touched-in this))
     :touched-new (rb-set ^RoaringBitmap (.-touched-new this))}))

;; ---- construction -------------------------------------------------------

(defn create-dense-tms
  "A fresh, empty dense truth-maintenance network — `vaelii.impl.jtms/create-tms`'s
  counterpart, selected by `open-kb`'s `{:tms :dense}`."
  []
  (->DenseTms (StampedLock.)
              (rb) (rb) (rb)                                   ; nodes premises mono-premises
              (Int2IntOpenHashMap.)                            ; depths
              (Int2ObjectOpenHashMap.) (Int2ObjectOpenHashMap.) ; supports conseqs
              (rb)                                             ; jids
              (Int2IntOpenHashMap.)                            ; j-conseq
              ;; an absent informant reads as the marker, never as handle 0
              (doto (Int2IntOpenHashMap.) (.defaultReturnValue no-informant))
              (Int2ObjectOpenHashMap.) (Int2ObjectOpenHashMap.) (Int2ObjectOpenHashMap.)
              (rb)                                             ; j-mono
              (rb) (rb) (rb) (rb) (rb) (rb) (rb) (rb)          ; in groundable defeated blocked
                                                               ; touched touched-in touched-new
                                                               ; mono
              (atom {})))

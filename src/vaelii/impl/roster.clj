;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.roster
  "A **live-handle roster**: what `sentex-ids` / `justification-ids` / `premise-ids` hand
  back, for a store big enough that the shape matters.

  The three enumerations answer a `java.util.Set` of handles, and every store the engine
  ships answers a `PersistentHashSet<Long>` because that is what its own state already
  is.  At the scale a server-backed store exists for, that shape *is* the cost: measured
  over contiguous handles, a `PersistentHashSet<Long>` retains **48–75 bytes per handle**
  (the hash trie's fill varies with cardinality), so **4.5–7.0 GB at 100M** — and
  `rebuild-tms` holds the sentex roster while it walks the premises and the
  justifications.

  Handles are minted in assertion order (`next-id`), so a roster is a near-contiguous run
  of longs with holes where records were deleted — the one shape a compressed bitmap is
  built for.  Over the same handles with a tenth of them punched out, a `Roaring64Bitmap`
  retains **0.13–0.26 bytes per handle**, and less than that on an unbroken run, where
  the whole roster is a few run containers.  It answers `contains?` in *less* time than
  the hash set, not more (`vaelii.impl.protocols`, the enumeration contract).

  ## What this is not

  Not an `IPersistentSet`.  `conj`, `disj` and `clojure.set` need one, so a caller wanting
  those converts with `(set roster)` — which is the 4.5 GB, paid at the call site that
  asked for it rather than by every store on every enumeration.  What the seam promises is
  membership, iteration, cardinality and ordering, which is what every caller in the
  engine uses.

  Immutable once built, so concurrent readers need no coordination — the one property the
  bitmap has to have here, since a store's readers enumerate while its writer writes."
  (:import [java.util Collection Iterator Set]
           [org.roaringbitmap.longlong LongIterator Roaring64Bitmap]))

(defn- long-of
  "`o` as a boxed long when it is an integer handle a `long` can hold, else nil.

  A roster is keyed by the *number*, so a handle boxed as an `Integer` and the same handle
  boxed as a `Long` are one member — the same normalization the SQL stores' fetch caches
  need one layer down.  An integer **too large for a long** answers nil rather than
  throwing: `contains?` on the Clojure set this replaces answers `false` for it, and a
  membership test that throws where the set said no is exactly the kind of difference this
  namespace exists not to have."
  ^Long [o]
  (cond
    (instance? Long o)    o
    (instance? Integer o) (Long/valueOf (.longValue ^Integer o))
    (integer? o)          (try (Long/valueOf (long o))
                               (catch IllegalArgumentException _ nil))
    :else                 nil))

(defn- long-iterator
  "The bitmap's handles as a `java.util.Iterator<Long>` — Roaring's own `LongIterator` is
  not one, and `iterator-seq`, `for` and the `Set` contract all want one."
  ^Iterator [^Roaring64Bitmap bits]
  (let [^LongIterator it (.getLongIterator bits)]
    (reify Iterator
      (hasNext [_] (.hasNext it))
      (next [_] (Long/valueOf (.next it))))))

(deftype HandleRoster [^Roaring64Bitmap bits ^long n]
  Set
  (size [_] (int n))
  (isEmpty [_] (zero? n))
  (contains [_ o] (boolean (when-let [v (long-of o)] (.contains bits (long v)))))
  (containsAll [_ c]
    (every? (fn [o] (boolean (when-let [v (long-of o)] (.contains bits (long v))))) c))
  (iterator [_] (long-iterator bits))
  (toArray [_] (.toArray ^Collection (vec (iterator-seq (long-iterator bits)))))
  (^objects toArray [_ ^objects a]
    ;; the `Collection` contract: fill `a` when it is long enough, else a fresh array,
    ;; and null-terminate a longer one.  Nothing in the engine calls this — it is here
    ;; because a `java.util.Set` that lies about `toArray` breaks the java-side callers
    ;; that make it worth being a `Set` at all.
    (let [xs           (vec (iterator-seq (long-iterator bits)))
          m            (count xs)
          ^objects out (if (>= (alength a) m) a (object-array m))]
      (dotimes [i m] (aset out i (nth xs i)))
      (when (> (alength out) m) (aset out m nil))
      out))
  (add [_ _] (throw (UnsupportedOperationException. "a handle roster is immutable")))
  (remove [_ _] (throw (UnsupportedOperationException. "a handle roster is immutable")))
  (addAll [_ _] (throw (UnsupportedOperationException. "a handle roster is immutable")))
  (removeAll [_ _] (throw (UnsupportedOperationException. "a handle roster is immutable")))
  (retainAll [_ _] (throw (UnsupportedOperationException. "a handle roster is immutable")))
  (clear [_] (throw (UnsupportedOperationException. "a handle roster is immutable")))

  ;; `seq`, `first` and `reduce` reach a roster through `Iterable` alone; `Seqable` and
  ;; `Counted` are here so they take the bitmap's own iteration and cardinality rather
  ;; than a wrapper and an int round trip.
  clojure.lang.Seqable
  (seq [_] (iterator-seq (long-iterator bits)))

  clojure.lang.Counted
  (count [_] (int n))

  ;; the `java.util.Set` contract: equal to any Set with the same members, hashing to the
  ;; sum of its members' hashes.  Clojure's `=` reaches these only from the java side —
  ;; with a Clojure set on either side it goes through `APersistentSet.equiv`, which tests
  ;; `size` and `contains` and so reads a roster without materializing one.
  Object
  (equals [_ o]
    (boolean (and (instance? Set o)
                  (= (int n) (.size ^Set o))
                  (every? (fn [x] (boolean (when-let [v (long-of x)]
                                             (.contains bits (long v)))))
                          ^Collection o))))
  (hashCode [_]
    (let [^LongIterator it (.getLongIterator bits)]
      (loop [h (int 0)]
        (if (.hasNext it) (recur (unchecked-add-int h (Long/hashCode (.next it)))) h))))
  (toString [_] (str "#vaelii/roster{" n " handles}")))

(defn roster
  "The handles in `ids` as a `HandleRoster`.  `ids` is anything reducible — a seq, a
  vector, an array — and need not arrive sorted."
  [ids]
  (let [b ^Roaring64Bitmap (Roaring64Bitmap.)]
    (reduce (fn [^Roaring64Bitmap acc id] (.addLong acc (long id)) acc) b ids)
    (.runOptimize b)
    (HandleRoster. b (.getLongCardinality b))))

(defn collector
  "A mutable `[add! finish]` pair, for a caller with a row loop rather than a reducible —
  a SQL store's cursor walk.  `add!` takes one handle; `finish` returns the immutable
  roster and is called once."
  []
  (let [b ^Roaring64Bitmap (Roaring64Bitmap.)]
    [(fn add! [id] (.addLong b (long id)) nil)
     (fn finish [] (.runOptimize b) (HandleRoster. b (.getLongCardinality b)))]))

(defn roster?
  "Is `x` one of these?  For a caller deciding whether `(set x)` would cost anything."
  [x]
  (instance? HandleRoster x))

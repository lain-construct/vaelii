;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.roster-test
  "`vaelii.impl.roster` — the compressed live-handle roster a record store may answer its
  three enumerations with instead of a `PersistentHashSet<Long>`.

  What is under test is not the bitmap, which is a dependency: it is that a caller reading
  an enumeration **cannot tell**.  Every operation the engine performs on a roster is
  exercised here against the Clojure set it replaces — membership, iteration, cardinality,
  ordering, equality in both directions — because that equivalence is the whole licence
  for a store to return one, and a store returning a shape that reads differently is a KB
  answering differently on that backend.

  The two properties beyond equivalence: it is **immutable**, so the concurrent readers a
  networked store exists to have need no coordination; and `(set roster)` is the door back
  to an `IPersistentSet`, which is what a caller wanting `conj` / `disj` / `clojure.set`
  goes through."
  (:require [clojure.set :as set]
            [clojure.test :refer [deftest is testing]]
            [vaelii.impl.capabilities :as cap]
            [vaelii.impl.roster :as roster]))

(def ^:private ids
  ;; a near-contiguous run with holes, which is what assertion-order minting plus
  ;; retraction leaves behind — and the shape the representation is chosen for
  (into [] (remove #(zero? (mod % 7))) (range 1 2001)))

(defn- fresh [] (roster/roster ids))

;; ---- a roster reads as the set it replaces -------------------------------

(deftest every-read-the-engine-makes-agrees-with-the-set
  (let [r (fresh)
        s (set ids)]
    (testing "membership"
      (is (every? #(contains? r %) ids) "every stored handle is in it")
      (is (not (contains? r 7)) "and a hole is not")
      (is (not (contains? r 999999)) "nor a handle past the end")
      (is (not (contains? r nil)) "nor a non-handle")
      (is (not (contains? r :informant)) "nor a keyword — the shape `get-sentex` refuses")
      (is (contains? r (int 3)) "a handle boxed as an Integer is the same member")
      (is (= (contains? s 10000000000000000000N) (contains? r 10000000000000000000N))
          "an integer no long can hold answers false, as the set does, rather than throwing")
      (is (contains? r (bigint 3)) "and one that fits is still the same member"))
    (testing "cardinality and emptiness"
      (is (= (count s) (count r)))
      (is (not (empty? r)))                                   ; the `seq` path
      (is (zero? (count (roster/roster []))) "an empty roster is empty")
      (is (nil? (seq (roster/roster []))) "and seqs to nil"))
    (testing "iteration"
      (is (= s (set (seq r))) "seq yields every handle and no other")
      (is (= s (into #{} r)) "and reduces the same way")
      (is (= (sort s) (sort r)) "sorted, they are one sequence")
      (is (= (first (sort s)) (first r))
          "a roster iterates ascending, so `first` is the least handle")
      (is (every? #(instance? Long %) (take 10 r))
          "the handles arrive boxed as Longs, which is what `get-sentex` is given"))
    (testing "the array conversions, which nothing here calls and a java caller does"
      ;; a `java.util.Set` that lies about `toArray` breaks exactly the callers being a
      ;; `Set` was for, so the contract is asserted rather than assumed
      (is (= s (set (.toArray ^java.util.Set r))) "the no-arg copy holds every handle")
      (is (= s (set (.toArray ^java.util.Set r (object-array 0))))
          "and a too-short array is answered with a fresh one")
      (let [a (object-array (+ 2 (count s)))]
        (.toArray ^java.util.Set r a)
        (is (= s (set (take (count s) a))) "a long-enough array is filled in place")
        (is (nil? (aget a (count s))) "and null-terminated, as the Collection contract says"))
      (is (.containsAll ^java.util.Set r ids) "containsAll reads every member")
      (is (not (.containsAll ^java.util.Set r (conj ids 7))) "and answers for a hole"))
    (testing "equality, whichever side it is on"
      (is (= s r) "a Clojure set equals a roster over the same handles")
      (is (= r s) "and the comparison reads the same the other way round")
      (is (not= (set (rest ids)) r) "one handle short is not equal")
      (is (= (.hashCode ^Object (java.util.HashSet. ^java.util.Collection s))
             (.hashCode ^Object r))
          "and it hashes as a java.util.Set, so it is usable as one"))))

(deftest the-door-back-to-a-persistent-set-is-open
  (let [r (fresh)]
    (is (set? (set r)) "`set` converts, which is what a caller needing conj/disj does")
    (is (= (set ids) (set r)))
    (is (= (disj (set ids) 3) (disj (set r) 3)))
    (is (= #{} (set/difference (set r) (set ids)))
        "and clojure.set reads the conversion, never the roster")))

(deftest a-roster-refuses-to-be-written
  (let [r (fresh)]
    (doseq [[label f] [["add" #(.add ^java.util.Set % (long 5))]
                       ["remove" #(.remove ^java.util.Set % (long 5))]
                       ["clear" #(.clear ^java.util.Set %)]]]
      (is (thrown? UnsupportedOperationException (f r))
          (str label " is refused — a roster is a read of the store, not a handle on it")))))

;; ---- immutable, so readers need no coordination --------------------------

(deftest concurrent-readers-see-one-answer
  ;; The reason a roster may be handed to a caller at all: a networked store's readers
  ;; enumerate while its writer writes, and a structure that mutated on read (some
  ;; bitmaps cache a cumulative cardinality lazily) would answer differently under
  ;; contention and pass every single-threaded test.
  (let [r      (fresh)
        expect (set ids)
        probes (into [] (concat ids [7 14 999999]))
        tasks  (repeatedly 8 (fn [] (future (into [] (map #(contains? r %)) probes))))
        answer (into [] (map #(contains? expect %)) probes)]
    (doseq [t tasks]
      (is (= answer @t) "every reader sees the same membership as the set does"))
    (is (= (count expect) (count r)) "and the cardinality is unchanged by reading it")))

;; ---- it composes with what the recovery walks do to an enumeration -------

(deftest the-recovery-hint-chunks-a-roster-like-any-other-seq
  ;; `cap/hinting` wraps the enumerations on the recovery walks, so whatever they return has
  ;; to survive `take` / `drop` / `concat` — the one place a store's own shape meets the
  ;; engine's laziness.
  (let [r       (fresh)
        hinted  (atom [])
        chunked (cap/hinting (fn [c] (swap! hinted conj (count c))) 100 r)]
    (is (= (sort ids) (vec chunked)) "the walk yields every handle, in order")
    (is (= (repeat (dec (count @hinted)) 100) (drop-last @hinted))
        "hinted a full chunk at a time")
    (is (= (count ids) (reduce + @hinted)) "and hinted every handle exactly once")))

(deftest the-hint-runs-one-chunk-ahead-of-what-is-consumed
  ;; The claim `cap/hinting` is written for, and the reason it is not a `mapcat`: a store
  ;; sizes its batch against its own cache, so four chunks in flight against a cache
  ;; smaller than four of them evict each other and the walk pays the batch queries AND
  ;; every point read it meant to avoid.  The per-element readings are collected into a
  ;; vector and asserted once, so the assertion count is a property of the contract and
  ;; not of the chunk size.
  (let [n    10
        seen (atom 0)
        s    (cap/hinting (fn [_] (swap! seen inc)) n (vec (range 100)))]
    (is (zero? @seen) "nothing is hinted until something is asked for")
    ;; how far the hints have run past the chunk holding the element being read
    (let [ahead (into [] (map-indexed (fn [i _] (- (long @seen) (inc (quot (long i) n)))))
                      (take 40 s))]
      (is (every? #(<= 0 (long %) 1) ahead)
          (str "the hints ran " (apply max ahead) " chunk(s) past the one being read"
               " — a `mapcat` spelling runs four")))
    (is (= (range 100) (vec s)) "the walk yields every element, in order")
    (is (= 10 @seen) "and hinted each chunk exactly once"))
  (testing "a chunk size below one is floored rather than yielding empty chunks forever"
    ;; `partition-all` with 0 is an infinite seq of empty chunks, and 0 is truthy, so a
    ;; caller's `(or setting 1)` does not catch it
    (let [seen (atom [])]
      (is (= [0 1 2] (vec (cap/hinting (fn [c] (swap! seen conj (count c))) 0 [0 1 2]))))
      (is (= [1 1 1] @seen))))
  (testing "no hint at all is the enumeration itself, unwrapped"
    (let [r (fresh)]
      (is (identical? r (cap/hinting nil 100 r))
          "so a store that does not prefetch keeps the set operations its caller may want"))))

;; ---- the java half, which `=` and `empty?` never reach --------------------

(deftest the-java-side-set-contract-answers-too
  ;; `=` between a roster and a Clojure set does not reach these: it goes through
  ;; `APersistentSet.equiv`, which tests `size` and `contains`.  A java caller — the whole
  ;; reason a roster is a `java.util.Set` rather than something narrower — calls them
  ;; directly, and a Set that answered `equals` or `isEmpty` wrongly is one those callers
  ;; cannot use.
  (let [r         (fresh)
        same-set  (java.util.HashSet. ^java.util.Collection (set ids))
        one-short (java.util.HashSet. ^java.util.Collection (set (rest ids)))]
    (testing "equality, called the way java calls it"
      (is (.equals ^Object r same-set) "a roster equals a java Set over the same handles")
      (is (.equals ^Object same-set r) "and the java Set agrees, reading size and contains")
      (is (not (.equals ^Object r one-short)) "one handle short is not equal")
      (is (not (.equals ^Object r (Object.))) "and something that is not a Set never is"))
    (testing "emptiness, which `empty?` answers off `seq` instead"
      (is (not (.isEmpty ^java.util.Set r)))
      (is (.isEmpty ^java.util.Set (roster/roster []))))
    (testing "and it prints as what it is rather than as its bitmap"
      (is (= (str "#vaelii/roster{" (count ids) " handles}") (.toString ^Object r))))))

(deftest the-bulk-writes-are-refused-too
  ;; `add` / `remove` / `clear` are not the whole write half of `java.util.Set`.  The three
  ;; bulk ops are what a java caller and `java.util.Collections` reach for, and one of them
  ;; quietly succeeding would mutate a roster every concurrent reader is holding.
  (let [r (fresh)]
    (doseq [[label f] [["addAll"    #(.addAll ^java.util.Set % [(long 5)])]
                       ["removeAll" #(.removeAll ^java.util.Set % [(long 5)])]
                       ["retainAll" #(.retainAll ^java.util.Set % [(long 5)])]]]
      (is (thrown? UnsupportedOperationException (f r))
          (str label " is refused — a roster is a read of the store, not a handle on it")))
    (is (= (count ids) (count r)) "and the roster is unchanged by having been asked")))

;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.dense-roots-oracle-test
  "Differential oracle for the key-interning roots backend (`vaelii.impl.dense-roots`):
  the same random op sequence hits `MemoryKvBackend` and `DenseRoots`, and every read must
  agree.

  What is exercised, in the **key shapes `vaelii.impl.kv` actually writes**:

    * the int-routed families — `:context-root`, `:functor-root`, `:term-index`,
      `:rule-index` (both arms), `:exception-index` — with symbol *and* ground-compound
      terms, plus the `:exception-index :rules` roster, which is the one key packed
      whole rather than through the dictionary;
    * the **argument roots**, `[:argument-root pred pos term]` — four parts, the
      predicate included (index layout 2, `kv/arg-key`).  They are the interesting case
      precisely because they are *not* packed: family | pos | term-id is already full,
      so `route` sends them to the generic map, and this is the oracle that says the
      generic path answers what the memory backend answers.  `dense_routing_test` is
      what pins the routing decision itself, which no behavioural test can see;
    * the `[:argument-slot pos term]` roster beside them, whose members are
      **predicates rather than handles** and which takes the same generic path;
    * multi-family `kv-intersect`, and the fallback for unrecognized keys (counters /
      scalars — where the contract-test keyspace lives)."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.impl.dense-roots :as dr]
            [vaelii.impl.kv :as kv]
            [vaelii.impl.memory :as mem]
            [vaelii.impl.tokens :as tok]))

(defn- pick [^java.util.Random rng v] (nth v (.nextInt rng (count v))))

;; a keyspace spanning every routed family plus fallback keys (counters / plain sets)
(def ^:private index-keys
  (vec (concat (for [c '[C0 C1]]            [:context-root c])
               (for [p '[p0 p1 p2]]         [:functor-root p])
               ;; four parts, the predicate first — `kv/arg-key`'s own shape.  Written
               ;; as three (`[:argument-root pos term]`) this whole family would still
               ;; agree, because both sides answer such a key from the generic map;
               ;; what it would stop testing is the family the index writes.
               (for [p '[p0 p1] pos [1 2] t '[A0 A1 (fatherOf A0)]]
                 [:argument-root p pos t])
               (for [t '[A0 A1 dog (fatherOf A0)]]         [:term-index t])
               (for [p '[p0 p1]]            [:rule-index :antecedent p])
               (for [p '[p0 p2]]            [:rule-index :consequent p])
               (for [p '[flies penguin]]    [:exception-index p])
               [[:exception-index :rules]])))
(def ^:private fallback-keys (vec (for [n [:n0 :n1]] [:ctr n])))   ; not a routed family

(deftest dense-roots-set-equal
  (let [rng (java.util.Random. 7)
        m   (mem/->MemoryKvBackend (atom {}))
        d   (dr/dense-roots (tok/token-dict))]
    (dotimes [_ 9000]
      (let [r (.nextInt rng 100)]
        (cond
          (< r 55) (let [k (pick rng index-keys) h (.nextInt rng 400)]
                     (kv/kv-add-to-set m k h) (kv/kv-add-to-set d k h))
          (< r 75) (let [k (pick rng index-keys) h (.nextInt rng 400)]
                     (kv/kv-remove-from-set m k h) (kv/kv-remove-from-set d k h))
          (< r 85) (let [k (pick rng fallback-keys)]           ; fallback counter
                     (is (= (kv/kv-increment m k) (kv/kv-increment d k)) "incr reply"))
          (< r 92) (let [k (pick rng fallback-keys)]
                     (is (= (kv/kv-decrement m k) (kv/kv-decrement d k)) "decr reply"))
          :else    (let [ks (vec (take (inc (.nextInt rng 3)) (shuffle index-keys)))]
                     (is (= (kv/kv-intersect m ks) (kv/kv-intersect d ks)) (str "sinter " ks))))))
    ;; members + cardinality agree for every key
    (doseq [k index-keys]
      (is (= (kv/kv-members m k) (kv/kv-members d k)) (str "smembers " k))
      (is (= (kv/kv-count    m k) (kv/kv-count    d k)) (str "scard "    k)))
    (doseq [k fallback-keys]
      (is (= (kv/kv-get m k) (kv/kv-get d k)) (str "counter " k)))
    ;; a read of a never-interned term is empty, not an error, and doesn't grow the dict
    (is (= #{} (kv/kv-members d [:term-index 'NeverSeen])))
    (is (= 0   (kv/kv-count    d [:term-index 'NeverSeen])))
    ;; the argument roots are keyed by predicate, so two predicates at one (pos, term)
    ;; are two postings — a key that dropped the predicate would merge them, and the
    ;; merged answer is what both sides would then agree on
    (testing "an argument root is per predicate, not per (position, term)"
      (doseq [b [m d]]
        (kv/kv-add-to-set b [:argument-root 'q0 1 'B0] 11)
        (kv/kv-add-to-set b [:argument-root 'q1 1 'B0] 22))
      (is (= #{11} (kv/kv-members d [:argument-root 'q0 1 'B0])))
      (is (= (kv/kv-members m [:argument-root 'q0 1 'B0])
             (kv/kv-members d [:argument-root 'q0 1 'B0])))
      (is (= (kv/kv-members m [:argument-root 'q1 1 'B0])
             (kv/kv-members d [:argument-root 'q1 1 'B0]))))
    ;; the slot roster beside them: same generic path, but its members are predicate
    ;; *names* rather than handles, so a backend that assumed int postings everywhere
    ;; would fail here and nowhere else
    (testing "the argument-slot roster holds predicates, not handles"
      (doseq [b [m d]]
        (kv/kv-add-to-set b [:argument-slot 1 'B0] 'q0)
        (kv/kv-add-to-set b [:argument-slot 1 'B0] 'q1)
        (kv/kv-add-to-set b [:argument-slot 2 '(fatherOf A0)] 'q0)
        (kv/kv-remove-from-set b [:argument-slot 1 'B0] 'q1))
      (doseq [k '[[:argument-slot 1 B0] [:argument-slot 2 (fatherOf A0)]]]
        (is (= (kv/kv-members m k) (kv/kv-members d k)) (str "smembers " k))
        (is (= (kv/kv-count   m k) (kv/kv-count   d k)) (str "scard "    k)))
      (is (= #{'q0} (kv/kv-members d [:argument-slot 1 'B0]))))))

(deftest dense-roots-batch-and-clear
  (let [m (mem/->MemoryKvBackend (atom {}))
        d (dr/dense-roots (tok/token-dict))
        ops [[:add-to-set [:functor-root 'p0] 1] [:add-to-set [:functor-root 'p0] 2]
             [:add-to-set [:argument-root 'p0 2 'A0] 9]
             [:add-to-set [:argument-slot 2 'A0] 'p0]
             [:add-to-set [:term-index '(fatherOf A0)] 5] [:add-to-set [:exception-index :rules] 7]
             [:increment [:ctr :n]] [:remove-from-set [:functor-root 'p0] 1] [:decrement [:ctr :n]]]]
    (is (= (kv/kv-batch m ops) (kv/kv-batch d ops)) "batch replies aligned")
    (doseq [k '[[:functor-root p0] [:argument-root p0 2 A0] [:argument-slot 2 A0]
                [:term-index (fatherOf A0)] [:exception-index :rules]]]
      (is (= (kv/kv-members m k) (kv/kv-members d k)) (str "post-batch " k)))
    (is (= (kv/kv-get m [:ctr :n]) (kv/kv-get d [:ctr :n])) "fallback counter after batch")
    (kv/kv-clear! m) (kv/kv-clear! d)
    (doseq [k '[[:functor-root p0] [:exception-index :rules] [:ctr :n]]]
      (is (= (kv/kv-members m k) (kv/kv-members d k)) (str "cleared " k)))))

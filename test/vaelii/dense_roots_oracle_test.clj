(ns vaelii.dense-roots-oracle-test
  "Differential oracle for the key-interning roots backend (`vaelii.impl.dense-roots`):
  the same random op sequence hits `MemoryKvBackend` and `DenseRoots`, and every read must
  agree.  Exercised on purpose: each int-routed family (`:context-root` `:functor-root` `:argument-root` `:term-index`
  `:rule-index` `:exception-index`) with **symbol and ground-compound** terms, the packed `(pos, term-id)`
  arg keys, the `:exception-index :rules` roster, multi-family `kv-intersect`, and the **fallback** for
  unrecognized keys (counters / scalars — where the contract-test keyspace lives)."
  (:require [clojure.test :refer [deftest is]]
            [vaelii.impl.dense-roots :as dr]
            [vaelii.impl.kv :as kv]
            [vaelii.impl.memory :as mem]
            [vaelii.impl.tokens :as tok]))

(defn- pick [^java.util.Random rng v] (nth v (.nextInt rng (count v))))

;; a keyspace spanning every routed family plus fallback keys (counters / plain sets)
(def ^:private index-keys
  (vec (concat (for [c '[C0 C1]]            [:context-root c])
               (for [p '[p0 p1 p2]]         [:functor-root p])
               (for [pos [1 2 3] t '[A0 A1 (fatherOf A0)]] [:argument-root pos t])
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
    (is (= 0   (kv/kv-count    d [:term-index 'NeverSeen])))))

(deftest dense-roots-batch-and-clear
  (let [m (mem/->MemoryKvBackend (atom {}))
        d (dr/dense-roots (tok/token-dict))
        ops [[:add-to-set [:functor-root 'p0] 1] [:add-to-set [:functor-root 'p0] 2] [:add-to-set [:argument-root 2 'A0] 9]
             [:add-to-set [:term-index '(fatherOf A0)] 5] [:add-to-set [:exception-index :rules] 7]
             [:increment [:ctr :n]] [:remove-from-set [:functor-root 'p0] 1] [:decrement [:ctr :n]]]]
    (is (= (kv/kv-batch m ops) (kv/kv-batch d ops)) "batch replies aligned")
    (doseq [k '[[:functor-root p0] [:argument-root 2 A0] [:term-index (fatherOf A0)] [:exception-index :rules]]]
      (is (= (kv/kv-members m k) (kv/kv-members d k)) (str "post-batch " k)))
    (is (= (kv/kv-get m [:ctr :n]) (kv/kv-get d [:ctr :n])) "fallback counter after batch")
    (kv/kv-clear! m) (kv/kv-clear! d)
    (doseq [k '[[:functor-root p0] [:exception-index :rules] [:ctr :n]]]
      (is (= (kv/kv-members m k) (kv/kv-members d k)) (str "cleared " k)))))

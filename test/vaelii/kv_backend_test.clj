(ns vaelii.kv-backend-test
  "The `KvBackend` contract: one behavioral spec every adapter must satisfy, so a
  new backend (disk, SQL, overlay) is a drop-in the moment it passes this.

  `KvIndexStore` (`vaelii.impl.kv`) is written once over this protocol, so its
  behavior is exactly as portable as the ops below are.  Two arms run the same
  `check-backend` spec: the in-memory adapter directly, and whatever backend the
  suite is configured for (memory by default, the on-disk WAL under
  `VAELII_TEST_BACKEND=disk`), reached through a real KB so the clear teardown is
  handled for us.  Green on both is the proof both satisfy the contract."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.impl.kv :as kv]
            [vaelii.impl.memory :as mem]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.resolution :as res]
            [vaelii.test-util :as tu]))

(defn check-backend
  "The full spec, run against one `KvBackend`.  Uses its own keyspace and clears it
  at both ends, so it is safe on a shared store.

  Public because it is *the* adapter contract: `overlay_test` runs it against the
  overlay decorator over an empty base, which is the claim that a fork of nothing
  behaves exactly like the thing it forked."
  [b]
  (kv/kv-clear! b)
  (testing "scalar upsert — set, overwrite, read, delete"
    (is (nil? (kv/kv-get b [:s :a])) "absent scalar reads nil")
    (kv/kv-put b [:s :a] {:x 1})
    (is (= {:x 1} (kv/kv-get b [:s :a])) "a Clojure value round-trips")
    (kv/kv-put b [:s :a] {:x 2})
    (is (= {:x 2} (kv/kv-get b [:s :a])) "a second set overwrites")
    (kv/kv-delete b [:s :a])
    (is (nil? (kv/kv-get b [:s :a])) "delete removes it"))

  (testing "counters — incr/decr return the post-op value"
    (is (= 1 (kv/kv-increment b [:c :n])) "first incr from absent is 1")
    (is (= 2 (kv/kv-increment b [:c :n])))
    (is (= 1 (kv/kv-decrement b [:c :n])) "decr returns the new value")
    (is (= 0 (kv/kv-decrement b [:c :n]))))

  (testing "sets — add/remove/members/card, every member type intact"
    (kv/kv-add-to-set b [:put 1] 1970)          ; a number, not "1970"
    (kv/kv-add-to-set b [:put 1] :rule)         ; a keyword, not "rule"
    (kv/kv-add-to-set b [:put 1] 'foo)          ; a symbol
    (is (= #{1970 :rule 'foo} (kv/kv-members b [:put 1])) "types survive the round trip")
    (is (= 3 (kv/kv-count b [:put 1])))
    (kv/kv-add-to-set b [:put 1] 1970)          ; re-add is idempotent (set semantics)
    (is (= 3 (kv/kv-count b [:put 1])))
    (kv/kv-remove-from-set b [:put 1] :rule)
    (is (= #{1970 'foo} (kv/kv-members b [:put 1])))
    (testing "membership — the same answer as the set, one probe instead of a set"
      ;; nothing above compares the two ops, and on a backend that packs a posting they
      ;; are different code paths entirely; `kv_membership_test` is the differential
      (is (kv/kv-member? b [:put 1] 1970))
      (is (kv/kv-member? b [:put 1] 'foo))
      (is (not (kv/kv-member? b [:put 1] :rule))  "a member that was removed")
      (is (not (kv/kv-member? b [:put 1] 'bar))   "one that was never there")
      (is (not (kv/kv-member? b [:never] 1970))   "and a key that was never written"))
    (testing "an emptied set is indistinguishable from an absent one"
      (kv/kv-remove-from-set b [:put 1] 1970)
      (kv/kv-remove-from-set b [:put 1] 'foo)
      (is (= #{} (kv/kv-members b [:put 1])))
      (is (zero? (kv/kv-count b [:put 1])))
      (is (not (kv/kv-member? b [:put 1] 1970)))))

  (testing "N-key intersection"
    (doseq [m '[a b c]] (kv/kv-add-to-set b [:i 1] m))
    (doseq [m '[b c d]] (kv/kv-add-to-set b [:i 2] m))
    (doseq [m '[b c e]] (kv/kv-add-to-set b [:i 3] m))
    (is (= '#{b c} (kv/kv-intersect b [[:i 1] [:i 2]])) "two-key intersect")
    (is (= '#{b c} (kv/kv-intersect b [[:i 1] [:i 2] [:i 3]])) "three-key intersect")
    (is (= '#{a b c} (kv/kv-intersect b [[:i 1]])) "single-key intersect is the set itself")
    (is (= #{} (kv/kv-intersect b [])) "no keys intersect to empty"))

  (testing "batch — mixed writes as one unit, one reply per op in order"
    (let [replies (kv/kv-batch b [[:increment [:b :n]]          ; 0 -> 1
                                  [:increment [:b :n]]          ; 1 -> 2
                                  [:add-to-set [:b :s] 7]        ; (non-counter reply ignored)
                                  [:decrement [:b :n]]          ; 2 -> 1
                                  [:put  [:b :v] :hello]
                                  [:remove-from-set [:b :s] 7]])]     ; empties the set
      (is (= 6 (count replies)) "one reply per op")
      (is (= 1 (long (nth replies 0))) "first incr reply is the new value")
      (is (= 2 (long (nth replies 1))))
      (is (= 1 (long (nth replies 3))) "decr reply is the new value, positionally aligned"))
    (testing "every op in the batch actually took effect"
      (is (= :hello (kv/kv-get b [:b :v])) "the :put landed")
      (is (zero? (kv/kv-count b [:b :s])) "the :add-to-set then :remove-from-set cancelled to empty")
      (is (= 2 (long (kv/kv-increment b [:b :n]))) "the counter settled at 1 (incr,incr,decr)")))

  (testing "entries out, entries back in — the projection a dump is written from"
    ;; The one operation whose *shape* is shared rather than private: a backend may hold
    ;; a set as int postings or a key as an interned long, and `kv-entries` has to undo
    ;; both.  So the property is a round trip through a cleared store, not a peek at the
    ;; representation — and afterwards ordinary writes must still work, which is what a
    ;; `kv-put` of a raw set would break on a backend that packs them.
    (kv/kv-clear! b)
    (kv/kv-add-to-set b [:term-index 'foo] 11)
    (kv/kv-add-to-set b [:term-index 'foo] 12)
    (kv/kv-add-to-set b [:context-root 'AContext] 11)
    (kv/kv-put b [:trie :count []] 2)
    (let [snapshot (into #{} (kv/kv-entries b))]
      (is (= 3 (count snapshot)) "every key, once")
      (is (contains? snapshot [[:term-index 'foo] #{11 12}])
          (str "a handle set does not come back as a set: " (pr-str snapshot)))
      (kv/kv-clear! b)
      (is (empty? (kv/kv-entries b)))
      (kv/kv-load b snapshot)
      (is (= snapshot (into #{} (kv/kv-entries b))) "and back in unchanged")
      (is (= #{11 12} (kv/kv-members b [:term-index 'foo])) "readable through the ordinary reads")
      (is (= 2 (long (kv/kv-get b [:trie :count []]))))
      (testing "a loaded entry is in the backend's own representation, not a foreign value"
        (kv/kv-add-to-set b [:term-index 'foo] 13)
        (is (= #{11 12 13} (kv/kv-members b [:term-index 'foo]))))))

  (kv/kv-clear! b)
  (is (nil? (kv/kv-get b [:c :n])) "clear wipes everything"))

(deftest memory-backend-satisfies-the-contract
  ;; a dedicated db number, isolated from the KB registries the suite uses
  (check-backend (mem/memory-kv-backend {:space 991})))

(deftest suite-backend-satisfies-the-contract
  ;; whatever the suite runs on — the in-memory backend by default, the on-disk WAL
  ;; under VAELII_TEST_BACKEND=disk — reached through a real KB so the clear teardown
  ;; is handled.  Redundant with the arm above under the default memory run, which is
  ;; the point: it never demands infrastructure the run does not have.
  (tu/with-cleared-kb [kb tu/fresh]
    ;; a `KvIndexStore` exposes its backend as `:backend`; the columnar index keeps its
    ;; native trie and delegates the flat families to a key-interning backend under
    ;; `:roots` — either way the suite reaches a real `KvBackend` and runs the contract.
    (let [b (or (:backend (:index kb)) (:roots (:index kb)))]
      (is (satisfies? kv/KvBackend b) "the index rests on a KvBackend")
      (check-backend b))))

;; ---- pipelining: the index write is one batch, args is one sinter -------
;; A KvBackend decorator counting the two load-bearing ops.  The count is at the
;; protocol seam, so it is backend-independent: a backend is free to make `kv-batch`
;; one round trip and `kv-intersect` one server-side intersection, so one call = one
;; round trip.  Proving KvIndexStore issues exactly one of each is what keeps the hot
;; path off a round-trip-per-op regression.

(defrecord CountingBackend [inner counts]
  kv/KvBackend
  (kv-batch  [_ ops] (swap! counts update :batch inc)  (kv/kv-batch inner ops))
  (kv-intersect [_ ks]  (swap! counts update :sinter inc) (kv/kv-intersect inner ks))
  (kv-get      [_ k]   (kv/kv-get inner k))
  (kv-put      [_ k v] (kv/kv-put inner k v))
  (kv-delete      [_ k]   (kv/kv-delete inner k))
  (kv-increment     [_ k]   (kv/kv-increment inner k))
  (kv-decrement     [_ k]   (kv/kv-decrement inner k))
  (kv-add-to-set     [_ k m] (kv/kv-add-to-set inner k m))
  (kv-remove-from-set     [_ k m] (kv/kv-remove-from-set inner k m))
  (kv-members [_ k]   (kv/kv-members inner k))
  (kv-member? [_ k m] (kv/kv-member? inner k m))
  (kv-count    [_ k]   (kv/kv-count inner k))
  (kv-entries  [_]     (kv/kv-entries inner))
  (kv-load     [_ es]  (kv/kv-load inner es))
  (kv-clear!   [_]     (kv/kv-clear! inner)))

(deftest the-index-write-is-one-batch-and-args-is-one-sinter
  (tu/with-neutral-kb [kb tu/fresh]        ; only to build real sentexes; nothing stored
    (let [inner  (doto (mem/memory-kv-backend {:space 992}) (kv/kv-clear!))
          counts (atom {:batch 0 :sinter 0})
          store  (kv/->KvIndexStore (->CountingBackend inner counts))]
      (tu/with-terms [rel A B C Ctx]
        (let [sx (res/kb-sentex kb (list rel A B C) Ctx)]
          (testing "index-sentex — the whole path, roots, and term index in one batch"
            (p/index-sentex store sx 42)
            (is (= 1 (:batch @counts))))
          (testing "sentexes-with-args — one intersection of the functor and argument roots"
            (p/sentexes-with-args store rel [[1 A] [2 B]])
            (is (= 1 (:sinter @counts))))
          (testing "unindex-sentex — two batches (decrement pass, then the delete pass)"
            (p/unindex-sentex! store sx 42)
            (is (= 3 (:batch @counts)) "one index + two unindex batches")))))))

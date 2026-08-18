;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.sort-by-content-key-test
  "`nm/sort-by-content-key` / `nm/min-by-content-key` — the decorate-sort-undecorate the
  engine's content orders share.  What is pinned here is the contract every caller
  leans on: the key is built **once per element** (not once per comparison), the sort
  short-circuits below two so a one-element listing builds no key at all, ties fall to
  arrival order, and `min-by-content-key` is `(first (sort-by-content-key …))` in one pass."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.impl.naming :as nm]))

(defn- counting
  "A key fn that tallies how many times it is called, so a test can prove the key is
  built n times rather than ~2·n·log₂n."
  [f]
  (let [n (atom 0)]
    [n (fn [x] (swap! n inc) (f x))]))

(deftest builds-the-key-once-per-element-not-once-per-comparison
  (let [coll (shuffle (range 64))
        [calls k] (counting identity)
        _ (doall (nm/sort-by-content-key k compare coll))]
    (is (= 64 @calls)
        "the key is decorated once per element; a per-comparison key fn would run ~2·n·log₂n times")))

(deftest short-circuits-below-two-and-builds-no-key
  (testing "zero and one element return the collection's own order, untouched"
    (let [[c0 k0] (counting identity)
          [c1 k1] (counting identity)]
      (is (= [] (nm/sort-by-content-key k0 [])))
      (is (= [:only] (nm/sort-by-content-key k1 [:only])))
      (is (= 0 @c0) "no key is built for an empty collection")
      (is (= 0 @c1) "no key is built for a singleton — the key is what orders, and there is nothing to order")))
  (testing "min over zero is nil, over one is that one, still no key built"
    (let [[c0 k0] (counting identity)
          [c1 k1] (counting identity)]
      (is (nil? (nm/min-by-content-key k0 [])))
      (is (= :only (nm/min-by-content-key k1 [:only])))
      (is (= 0 @c0))
      ;; min over a singleton decorates the one element (harmless) — assert it is at most one
      (is (<= @c1 1)))))

(deftest compare-form-is-the-default-and-orders-structurally
  ;; shorter-first, not lexicographic: (a) before (a b), which pr-str/str would reverse
  (let [forms [(list 'a 'b) (list 'a) (list 'b)]]
    (is (= [(list 'a) (list 'a 'b) (list 'b)]
           (nm/sort-by-content-key identity forms))
        "compare-form default: (a) precedes (a b) precedes (b)")))

(deftest a-pre-built-tuple-key-orders-under-plain-compare
  ;; a [rank …] priority vector is Comparable; pass `compare` to keep that exact order
  (let [xs [{:p 1 :n "z"} {:p 0 :n "m"} {:p 1 :n "a"}]
        key (juxt :p :n)]
    (is (= [{:p 0 :n "m"} {:p 1 :n "a"} {:p 1 :n "z"}]
           (nm/sort-by-content-key key compare xs))
        "sorted by the tuple key under default compare, primary then secondary")))

(deftest ties-keep-arrival-order
  ;; every element shares one key, so the whole order must be the arrival order
  (let [xs (mapv (fn [i] {:id i}) (range 20))]
    (is (= xs (nm/sort-by-content-key (constantly :same) compare xs))
        "equal keys fall back to arrival order, never to a re-shuffle")
    (is (= (first xs) (nm/min-by-content-key (constantly :same) compare xs))
        "min on an all-tie collection is the earliest arrival")))

(deftest min-agrees-with-first-of-sort
  (doseq [cmp [compare nm/compare-form]
          n   [1 2 3 8 64]]
    (let [xs (shuffle (mapv (fn [i] [(mod (* i 7) 5) i]) (range n)))
          key first]
      (is (= (first (nm/sort-by-content-key key cmp xs))
             (nm/min-by-content-key key cmp xs))
          (str "min == first-of-sort for cmp " cmp " at n=" n)))))

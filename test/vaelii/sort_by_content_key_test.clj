;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.sort-by-content-key-test
  "`nm/sort-by-content-key` / `nm/min-by-content-key` / `nm/print-key` — the
  decorate-sort-undecorate the engine's content orders share, and the one guarded
  printer they use when a key is printed at all.  What is pinned here is the contract
  every caller leans on: the key is built **once per element** (not once per
  comparison), the sort short-circuits below two so a one-element listing builds no key
  at all, ties fall to arrival order, and `min-by-content-key` is
  `(first (sort-by-content-key …))` in one pass.

  The last test is a **scan of the sources**, not a unit assertion, and it is here
  because this is the one class of order-dependence that kept coming back one site at a
  time: a `pr-str` ordering key with the print vars left ambient.  A REPL binds
  `*print-length*`, two long sentences elide to one prefix, the key collapses, and the
  tie falls back to the enumeration order the content key existed to remove — silently,
  because every value involved is still legal."
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [vaelii.impl.naming :as nm])
  (:import [java.io File]))

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

;; ---- print-key: the guarded printer, and the scan that keeps it the only one ----

(deftest print-key-is-unmoved-by-an-ambient-print-bound
  (let [a (list 'likes 'Tom 'Jerry 'Spike 'Butch)
        b (list 'likes 'Tom 'Jerry 'Spike 'Nibbles)]
    (testing "a caller's print bounds elide two long sentences to one prefix"
      (binding [*print-length* 3]
        (is (= (pr-str a) (pr-str b))
            "the hazard itself: a bare pr-str key collapses, and the tie falls to arrival")))
    (testing "print-key ignores them, so the key stays total"
      (binding [*print-length* 3 *print-level* 2]
        (is (not= (nm/print-key a) (nm/print-key b)))
        (is (= [a b] (nm/sort-by-content-key nm/print-key compare [b a]))
            "and the order is the content one, under the bound that would have collapsed it")))
    (testing "metadata is no part of what a sentence says"
      (binding [*print-meta* true]
        (is (= (nm/print-key a) (nm/print-key (with-meta a {:tagged true}))))))))

(def ^:private ordering-call
  "The calls whose first argument is an ordering **key**.  `sort` is absent on purpose —
  it takes no key fn, so a printed value cannot reach it.  `group-by` is here because a
  key that collapses collapses two *buckets* into one, which is the same defect wearing a
  different hat."
  #"sort-by|min-by-content-key|max-key|min-key|group-by")

(def ^:private printed-key-allowed
  "The sources where a printed or `str`'d ordering key is not a hazard, each by a
  distinctive substring of its own line, and why.  Every entry keys a **keyword** — an
  option key, a mode name, a belief mode — and `*print-length*` / `*print-level*` elide
  collections, never a keyword, so those keys cannot collapse.  They order a rejection
  message's `:options` list rather than anything a belief or a report is read off.

  One allowlist for both scans below, because they are one rule seen from two sides: a
  key that may not print may not `str` either, and a value safe for one is safe for both."
  #{"(remove opt-keys (keys opts))"
    "(remove edit-batch-keys (keys batch))"
    "(keys belief-modes)"})

(def ^:private bare-str
  "`str` standing alone as a key fn — `(sort-by str …)`, `(comp str :sentence)`, `(str c)`
  inside a tuple key.  The lookarounds are what keep `pr-str`, `str/join` and a symbol that
  merely ends in those three letters out of it."
  #"(?<![\w-])str(?![\w/-])")

(defn- clj-sources []
  (->> (file-seq (io/file "src/vaelii"))
       (filter #(.isFile ^File %))
       (map #(.getPath ^File %))
       (filter #(str/ends-with? % ".clj"))
       sort))

(defn- key-argument
  "The part of `line` that can be an ordering key: everything after the ordering call,
  or nil when the line makes none.  Printing *before* the call is a different thing — a
  `(map pr-str (sort-by …))` renders what the sort answered and never keys on it."
  [line]
  (when-let [m (re-find ordering-call line)]
    (subs line (+ (str/index-of line m) (count m)))))

(defn- unguarded-printed-keys
  "Every `[path line-number line]` in `src/vaelii` that hands a bare `pr-str` to an
  ordering call, with the three ways of being guarded taken out: the printer is
  `nm/print-key`; a `*print-length*` binding frame is open within the twelve lines above
  (the shape `solve/content-key` and `settle/content-order` use, one binding around a
  whole sort rather than one per element); or the line is allowlisted above.

  `naming.clj` itself is skipped — it is where the guard is defined and where the hazard
  is described in prose."
  []
  (for [path  (clj-sources)
        :when (not (str/ends-with? path "/naming.clj"))
        :let  [lines (vec (str/split-lines (slurp path)))]
        i     (range (count lines))
        :let  [line (nth lines i)
               key  (key-argument line)
               above (str/join "\n" (subvec lines (max 0 (- i 12)) (inc i)))]
        :when (and key
                   (str/includes? key "pr-str")
                   (not (str/includes? key "print-key"))
                   (not (str/includes? above "*print-length*"))
                   (not-any? #(str/includes? line %) printed-key-allowed))]
    [path (inc i) (str/trim line)]))

(deftest no-ordering-key-prints-without-the-guard
  ;; The recurring bug this closes: `(sort-by pr-str …)` over an answer *set*, or over a
  ;; map's `keys`/`vals`.  Under a REPL's `*print-length*` the key collapses and the
  ;; choice — which hypothesis survives, which ASP atom gets which id, which declaration
  ;; a refusal names — falls back to handle order, which is assertion order.  Nothing
  ;; throws and no test of the answer notices, because both readings are legal.
  (let [bad (unguarded-printed-keys)]
    (is (empty? bad)
        (str "an ordering key is printed with the print vars left ambient — use "
             "`nm/print-key`, or bind `*print-length*`/`*print-level*` around the sort:\n"
             (str/join "\n" (map (fn [[p n l]] (str "  " p ":" n "  " l)) bad))))))

(defn- unguarded-str-keys
  "Every `[path line-number line]` in `src/vaelii` that hands a bare `str` to an ordering
  call.  The guarded answers are `nm/print-key` (a collection-capable value), `nm/name-key`
  (a scalar one) and `nm/compare-form` (no key at all), none of which contains a bare
  `str` — so a converted site simply stops matching, and no second roster has to be kept
  in step with this one.  The allowlist above is the one exception, and `naming.clj` is
  skipped for the reason the printed scan skips it.

  **Why `str` is the same hazard as `pr-str`.**  `str` on a collection is `pr-str` with
  the ambient print vars honoured — `(str '(a b c d))` under `*print-length*` 2 is
  `(a b ...)` — so a sentence, a NAT, a context NAT or a binding map keyed with it
  collapses under a REPL's bounds exactly as a printed key does.  On a symbol, keyword,
  string or number it cannot, which is what `nm/name-key` is for: the same `str`, with the
  scalar written down as a claim and a collection routed to the guarded printer."
  []
  (for [path  (clj-sources)
        :when (not (str/ends-with? path "/naming.clj"))
        :let  [lines (vec (str/split-lines (slurp path)))]
        i     (range (count lines))
        :let  [line (nth lines i)
               key  (key-argument line)]
        :when (and key
                   (re-find bare-str key)
                   (not-any? #(str/includes? line %) printed-key-allowed))]
    [path (inc i) (str/trim line)]))

(deftest no-ordering-key-is-a-bare-str
  ;; The wider half of the same class, and the one that had ~50 live sites: `str` honours
  ;; the print vars exactly as `pr-str` does, so `(sort-by str terms)` over a list that may
  ;; hold a NAT is the printed-key hazard with the printing hidden.  Nothing throws, both
  ;; readings are legal, and the order the page or the report is read in falls back to
  ;; whatever the index enumerated.
  (let [bad (unguarded-str-keys)]
    (is (empty? bad)
        (str "an ordering key is a bare `str` — use `nm/print-key` where the value may be "
             "a collection (a sentence, a NAT, a context NAT, a binding map), `nm/name-key` "
             "where it is a scalar, or `nm/compare-form` where no key is needed at all:\n"
             (str/join "\n" (map (fn [[p n l]] (str "  " p ":" n "  " l)) bad))))))

(deftest the-allowlist-still-names-live-code
  ;; An allowlist that has outlived its sites reads as a rule with exceptions when it is
  ;; really a rule with none — so each entry must still match a line that would otherwise
  ;; be flagged.
  (let [text (str/join "\n" (map slurp (clj-sources)))]
    (doseq [entry printed-key-allowed]
      (is (str/includes? text entry)
          (str "allowlisted printed key no longer in the sources: " entry)))))

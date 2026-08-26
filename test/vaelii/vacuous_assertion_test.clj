;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.vacuous-assertion-test
  "A **scan of the test sources** for assertions that cannot fail.

  This is the sibling of `sort-by-content-key-test`'s ordering scans and is here for
  the same reason: the shape keeps coming back one site at a time, and each one reads
  as a passing test forever.  An assertion that cannot fail is worse than a missing
  one — a missing test is a gap somebody can see in a coverage report, and a
  tautological test is a green tick over the thing it claims to check.

  Four shapes, one rule — **an assertion's two outcomes must both be reachable**:

    * `(is (= x x))` with the two operands written identically.  Whatever the fn under
      test does, it does the same thing twice, so the comparison holds.  The exception
      is a *determinism* claim, where the two sides are two independent builds and
      agreeing is the whole content of the test; those are allowlisted below by name.
    * `(is <literal>)` — `(is true)`, `(is :ok)`, `(is (do … true))`.  A throw inside
      still turns the run red, which is why the shape survives review, but it turns it
      red as an **error**: the assertion itself reports nothing, and the message
      attached to it is never printed on the path it was written for.  Say what the
      call returned instead.
    * `(is (or x (not x)))` — a disjunction over a value and its negation, which is
      the excluded middle rather than a property of the code.
    * `(is (<= 0 x))` / `(is (>= x 0))` on a count, a length or a wall-clock delta.
      The bound is a fact about the quantity's type, not about the run.

  **The scan is textual and the window is four lines**, which is what these shapes fit
  in; a form spread wider than that is missed rather than mis-read.  Nesting deeper
  than four parenthesis levels inside one operand is missed for the same reason.  It
  is a ratchet against the next one, not a proof about the ones already here.

  One `is` per shape, so a tree with fifty violations reports one failure carrying all
  fifty rather than fifty failures — and the count does not move with the findings."
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.test :refer [deftest is]])
  (:import (java.io File)))

(def ^:private this-file "vacuous_assertion_test.clj")

(defn- test-sources
  "Every test source but this one — the patterns below appear here as patterns, and a
  scan that reads its own roster reports itself."
  []
  (->> (file-seq (io/file "test/vaelii"))
       (filter #(.isFile ^File %))
       (map #(.getPath ^File %))
       (filter #(str/ends-with? % ".clj"))
       (remove #(str/ends-with? % this-file))
       sort))

;; ---- the shapes ----------------------------------------------------------

(def ^:private balanced
  "A parenthesised form nested at most four deep.  Java's regex engine has no
  recursion, and an assertion's operand does not need it: four levels is
  `(is (= (:a (f (g x))) …))` and everything shallower."
  (str "\\((?:[^()]|"
       "\\((?:[^()]|"
       "\\((?:[^()]|"
       "\\([^()]*\\)"
       ")*\\)"
       ")*\\)"
       ")*\\)"))

(def ^:private operand
  "One operand of a two-argument assertion: a parenthesised form, or a bare atom."
  (str "(?:" balanced "|[^\\s()]+)"))

(def ^:private self-comparison
  "`(is (= x x))` — the same text on both sides of the equality."
  (re-pattern (str "\\(is\\s+\\(=\\s+(" operand ")\\s+\\1\\s*\\)")))

(def ^:private literal-assertion
  "`(is true)`, `(is :ok)`, `(is 42)`, `(is \"…\")`, and `(is (do … true))` — an `is`
  whose form is a truthy constant however it is dressed."
  (re-pattern (str "\\(is\\s+(?:true|:[^\\s()]+|[0-9]+|\"[^\"]*\")[\\s)]"
                   "|\\(is\\s+\\(do\\b[^()]*(?:" balanced "[^()]*)*"
                   "(?:true|:[^\\s()]+|[0-9]+)\\s*\\)")))

(def ^:private excluded-middle
  "`(is (or x (not x)))` — a disjunction that holds for every value of `x`."
  (re-pattern (str "\\(is\\s+\\(or\\s+(" operand ")\\s+\\(not\\s+\\1\\s*\\)")))

(def ^:private vacuous-bound
  "`(is (<= 0 (count …)))` / `(is (>= (count …) 0))` — two arguments, one of them the
  literal zero, against a quantity that cannot be negative whatever the run did.

  **`count` and nothing else**, which is what keeps this a ratchet rather than a
  nuisance: `(>= (.indexOf …) 0)` is the same *shape* over a quantity whose −1 is the
  whole answer, and a scan that cannot tell them apart is one whose findings get
  allowlisted one by one until it means nothing.  The three-argument form
  (`(is (<= 0 n limit))`) carries a real upper bound and is not this shape either."
  (let [counted (str "\\(count\\s[^()]*(?:" balanced "[^()]*)*\\)")]
    (re-pattern (str "\\(is\\s+\\(<=\\s+0\\s+" counted "\\s*\\)"
                     "|\\(is\\s+\\(>=\\s+" counted "\\s+0\\s*\\)"))))

(def ^:private shapes
  [["an equality whose two operands are the same text" self-comparison]
   ["an `is` on a literal" literal-assertion]
   ["a disjunction over a value and its negation" excluded-middle]
   ["a bound that holds for every value of the quantity" vacuous-bound]])

(def ^:private allowed
  "Distinctive substrings of the lines this scan must let through, each a
  **determinism** claim rather than a tautology: the two sides are built
  independently and agreeing is the content of the test.

    * `(edge/translate (mk))` — `mk` is a thunk that builds a fresh program per call,
      and `translate` allocates atom ids while walking sets and maps.  Two independent
      builds producing the same ASPIF is exactly the claim; one build compared with
      itself would be the tautology this scan is for."
  #{"(edge/translate (mk))"})

(defn- opens-on-the-first-line?
  "Does `pattern` match `window` starting inside the line the window opens on?

  Without this the window is a second bug: four lines over a clean assertion reach the
  *next* one, and a finding three lines down is reported against the line above it —
  once per window that saw it, so four times over."
  [^java.util.regex.Pattern pattern ^String window ^long head-length]
  (let [m (.matcher pattern window)]
    (and (.find m) (<= (.start m) head-length))))

(defn- vacuous-assertions
  "`[path line text shape]` for every assertion in the test sources that cannot fail."
  []
  (for [path (test-sources)
        :let [lines (vec (str/split-lines (slurp path)))]
        i    (range (count lines))
        :when (str/includes? (nth lines i) "(is ")
        :let [head   (str/replace (nth lines i) #"\s+" " ")
              window (-> (str/join " " (subvec lines i (min (count lines) (+ i 4))))
                         (str/replace #"\s+" " "))]
        [what pattern] shapes
        :when (and (opens-on-the-first-line? pattern window (count head))
                   (not-any? #(str/includes? window %) allowed))]
    [path (inc i) (str/trim (nth lines i)) what]))

(deftest no-assertion-that-cannot-fail
  (let [bad (vacuous-assertions)]
    (is (empty? bad)
        (str "an assertion whose two outcomes are not both reachable — make it say what"
             " the call returned, or delete it:\n"
             (str/join "\n" (map (fn [[p n l what]] (str "  " p ":" n "  " what "\n      " l))
                                 bad))))))

(deftest the-allowlist-still-names-live-code
  ;; An allowlist entry outliving the line it was written for is how a scan quietly
  ;; stops covering something.  One assertion per entry, so the failure names which.
  (let [text (str/join "\n" (map slurp (test-sources)))]
    (doseq [entry allowed]
      (is (str/includes? text entry)
          (str "an allowlisted assertion is no longer in the test sources: " entry)))))

(deftest the-scan-reads-the-test-sources
  ;; The paths are relative, so a runner whose cwd is not the project root scans an
  ;; empty file list and reports a clean tree.  Nothing else here would say so.
  (is (< 100 (count (test-sources)))
      "the scan found almost no test sources — is the runner's cwd the project root?"))

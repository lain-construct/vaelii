;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.except-strength-test
  "An `exceptWhen` asserts **two** things — the rule, and the exception qualifying it —
  and `assert` takes one `opts`.  So the assertion's own `:strength` reaches both halves,
  and three of the four rule × exception pairings are all that can be said with it.  The
  fourth, a **known-true exception on a default rule**, is what a wrapper on the query
  says: `(exceptWhen (set/monotonic Q) R)`.

  Two claims, and they are one claim asked at two entry points.  `assert` reads the wrapper —
  and `check` reports the same refusal for a malformed one, since check and do may
  disagree on nothing but the delivery.  And the **text KB format** writes whichever
  spelling reproduces the pair, so all four round-trip: byte-identically, because a text
  KB is ordered by content and carries nothing about the run, and belief-identically,
  because the two halves come back at the classes they went out at.

  Built with `tu/with-cleared-kb` rather than a fixture, as `text_export_test` is: what
  these exercise is a KB written out and read back into a second one."
  (:require [clojure.java.io :as io]
            [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.rules :as vr]
            [vaelii.impl.sentex :as sx]
            [vaelii.test-util :as tu])
  (:import (java.io File)
           (java.nio.file Files)
           (java.nio.file.attribute FileAttribute)))

(defn- temp-dir ^File [nm]
  (.toFile (Files/createTempDirectory (str "vaelii-halves-" nm "-")
                                      (into-array FileAttribute []))))

(defn- rm-rf! [^File d]
  (doseq [^File f (reverse (file-seq d))] (.delete f)))

(defn- with-dirs*
  "Run `(f dir…)` on `n` temp directory paths, removed before the body and after it — an
  export destination is normally one that does not exist yet."
  [n nm f]
  (let [dirs (mapv #(temp-dir (str nm "-" %)) (range n))]
    (try (run! rm-rf! dirs)
         (apply f dirs)
         (finally (run! rm-rf! dirs)))))

(defn- half-classes
  "`[rule-class exception-class]` for the one excepted rule in `ctx` — read off the
  records, since a strength is a fact about the premise rather than about the sentence."
  [kb ctx]
  (let [sxs (v/sentexes-in-context kb ctx)]
    [(:strength (first (filter #(some? (:antecedent %)) sxs)))
     (:strength (first (filter #(sx/exceptWhen-meta? (:sentence %)) sxs)))]))

;;; ── the entry point ──────────────────────────────────────────────────────────

(deftest assert-reads-a-strength-stated-on-an-exceptWhen-query
  ;; The inline-rule form, which is also the one the text writer emits.
  (tu/with-cleared-kb [kb tu/fresh]
    (tu/with-terms [bird flies penguin CxHalf]
      (v/assert kb (list 'genlCx CxHalf 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'exceptWhen (list 'set/monotonic (list penguin '?b))
                         (vr/rule-sentence [(list bird '?b)] (list flies '?b)))
                CxHalf)
      (testing "the exception is known-true and the rule it qualifies is not"
        (is (= [:default :monotonic] (half-classes kb CxHalf))))
      (testing "and the wrapper never reaches the store"
        (let [meta-sx (first (filter #(sx/exceptWhen-meta? (:sentence %))
                                     (v/sentexes-in-context kb CxHalf)))]
          (is (not-any? #{'set/monotonic}
                        (tree-seq sequential? seq (:sentence meta-sx)))
              "a strength is how a sentence is asserted, not part of what it says"))))))

(deftest a-strength-on-the-query-of-a-by-handle-exceptWhen-is-read-too
  ;; The other branch of the split: the exceptWhen names its rule by handle, so there is
  ;; no rule to store and the `opts` has only ever been the exception's.  It reads the
  ;; wrapper all the same, so one spelling means one thing at both spellings of the entry point.
  (tu/with-cleared-kb [kb tu/fresh]
    (tu/with-terms [bird flies penguin CxHalf]
      (v/assert kb (list 'genlCx CxHalf 'CxUniverse) 'CxUniverse)
      (let [h (v/assert kb (vr/rule-sentence [(list bird '?b)] (list flies '?b)) CxHalf)]
        (v/assert kb (list 'exceptWhen (list 'set/monotonic (list penguin '?b))
                           (v/sentex-handle h))
                  CxHalf)
        (is (= [:default :monotonic] (half-classes kb CxHalf)))))))

(deftest an-outer-wrapper-still-reaches-both-halves
  ;; Unchanged, and the reason the query wrapper exists rather than replacing it: the
  ;; outer one is the assertion's own option, and an assertion is one thing.
  (tu/with-cleared-kb [kb tu/fresh]
    (tu/with-terms [bird flies penguin CxHalf]
      (v/assert kb (list 'genlCx CxHalf 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'exceptWhen (list penguin '?b)
                         (vr/rule-sentence [(list bird '?b)] (list flies '?b)))
                CxHalf {:strength :monotonic})
      (is (= [:monotonic :monotonic] (half-classes kb CxHalf))))))

(deftest a-malformed-query-wrapper-is-refused-the-same-way-at-check-and-assert
  ;; Refused rather than passed through: handed on, `(set/monotonic)` would reach the
  ;; naming checks as a literal whose functor is a namespace-qualified symbol and be
  ;; refused there for the wrong reason.
  (tu/with-cleared-kb [kb tu/fresh]
    (tu/with-terms [bird flies CxHalf]
      (v/assert kb (list 'genlCx CxHalf 'CxUniverse) 'CxUniverse)
      (doseq [[label q] [["a wrapper round nothing" (list 'set/monotonic)]
                         ["a wrapper round two queries"
                          (list 'set/monotonic (list bird '?b) (list flies '?b))]]]
        (testing label
          (let [bad (list 'exceptWhen q
                          (vr/rule-sentence [(list bird '?b)] (list flies '?b)))
                ps  (v/check kb bad CxHalf)]
            (is (= :shape (:type (first ps))))
            (let [e (is (thrown? clojure.lang.ExceptionInfo (v/assert kb bad CxHalf)))]
              (is (= :shape (:type (ex-data e))))
              (is (= (:message (first ps)) (ex-message e))
                  "check and assert refuse it in the same words"))))))))

;;; ── the round trip ────────────────────────────────────────────────────

(deftest all-four-strength-pairings-round-trip-through-text
  (doseq [[rule-s exc-s outer? query? own-line?]
          [[:default   :default   false false false]
           [:default   :monotonic false true  false]
           [:monotonic :default   false false true]
           [:monotonic :monotonic true  false true]]]
    (testing (str "a " (name rule-s) " rule under a " (name exc-s) " exception")
      (tu/with-terms [bird flies penguin CxHalf]
        (with-dirs* 2 "pairing"
          (fn [a b]
            (let [pa    (.getPath ^File a)
                  pb    (.getPath ^File b)
                  file  (str CxHalf ".txt")
                  text  (tu/with-cleared-kb [kb tu/fresh]
                          (v/assert kb (list 'genlCx CxHalf 'CxUniverse) 'CxUniverse)
                          (let [h (v/assert kb (vr/rule-sentence [(list bird '?b)]
                                                                 (list flies '?b))
                                            CxHalf {:strength rule-s})]
                            (v/assert kb (list 'exceptWhen (list penguin '?b)
                                               (v/sentex-handle h))
                                      CxHalf {:strength exc-s}))
                          (v/export-text! kb pa)
                          (slurp (io/file pa file)))]
              (testing "the file spells the pair"
                ;; the outer wrapper can only say a class both halves share, so it is
                ;; written only when they do; the query wrapper says the exception's own;
                ;; and a known-true rule is written again on a line of its own, since
                ;; there is no wrapper for *weakening* a half
                (is (= outer? (some? (re-find #"\(set/monotonic \(exceptWhen " text))))
                (is (= query? (some? (re-find #"\(exceptWhen \(set/monotonic " text))))
                (is (= own-line? (some? (re-find #"(?m)^\(set/monotonic \(implies " text)))))
              (testing "the reload stands the two halves back up at their own classes"
                (tu/with-cleared-kb [kb tu/fresh]
                  (v/load-text! kb pa)
                  (is (= [rule-s exc-s] (half-classes kb CxHalf)))
                  (testing "and writing it out again is byte-identical"
                    (v/export-text! kb pb)
                    (is (= text (slurp (io/file pb file))))))))))))))

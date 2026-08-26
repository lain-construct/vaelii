;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.encodable-test
  "A stored sentence's values must survive the durable log.  The in-memory backend
  serializes nothing, so a value nippy cannot freeze — a function, an atom, an open
  stream — stores there and then throws at write time on the first on-disk backend:
  the same assert succeeds or fails by backend, which breaks the promise that every
  backend reasons alike.  `checks/check-encodable` refuses it at the door instead, so a
  value stores in every backend or none.

  What *is* storable is everything a sentence is normally built from — the vocabulary
  (symbols, keywords), the literals (strings, numbers, chars), booleans and nil — plus
  any structure of them nippy round-trips: vectors, maps, sets.  A vector argument is
  accepted and, like every sequential, canonicalizes to its `=` list form (vaelii keeps
  vectors ≡ lists — a vector carries no distinct meaning yet, and Clojure `=` already
  treats `[a b]` and `(a b)` as one value), so it is found by the list spelling.

  Both write doors that persist — `assert` (hence `assert-rule`, `assert-many`) and
  `assert-inert` — carry the guard, and `check` predicts it under the same `:type`."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(defn- refusal
  "The `ex-data` of the refusal `f` throws, or `{:answered (f)}` when it answers."
  [f]
  (try {:answered (f)}
       (catch clojure.lang.ExceptionInfo e (ex-data e))))

(deftest a-non-serializable-arg-is-refused-at-the-door
  ;; The canonical "blows up" cases: a value with no nippy handler and no Serializable
  ;; fallback.  Refused as :not-encodable before anything is stored, so a good assert
  ;; right after still works — the door is closed to the value, not wedged.
  (tu/with-terms [holds Tom CxStory]
    (tu/with-cleared-kb [kb tu/fresh]
      (doseq [[label bad] {"a function" (fn [_] 1)
                           "an atom"    (atom 1)}]
        (is (= :not-encodable (:type (refusal #(v/assert kb (list holds Tom bad) CxStory))))
            label))
      (testing "and an ordinary fact still asserts and is found"
        (v/assert kb (list holds Tom 1) CxStory)
        (is (seq (v/sentexes-matching kb (list holds Tom 1) CxStory)))))))

(deftest a-non-serializable-value-is-caught-anywhere-in-the-sentence
  ;; The walk descends every collection, so the value is caught in argument position,
  ;; nested in a compound / vector / map argument, and inside a rule.
  (tu/with-terms [holds part Tom CxStory]
    (tu/with-cleared-kb [kb tu/fresh]
      (let [bad (fn [_] 1)]
        (testing "bare in argument position"
          (is (= :not-encodable
                 (:type (refusal #(v/assert kb (list holds Tom bad) CxStory))))))
        (testing "nested inside a compound argument"
          (is (= :not-encodable
                 (:type (refusal #(v/assert kb (list holds Tom (list part bad)) CxStory))))))
        (testing "inside a vector argument"
          (is (= :not-encodable
                 (:type (refusal #(v/assert kb (list holds Tom [bad]) CxStory))))))
        (testing "inside a map argument (as a value, and as a key)"
          (is (= :not-encodable
                 (:type (refusal #(v/assert kb (list holds Tom {:k bad}) CxStory)))))
          (is (= :not-encodable
                 (:type (refusal #(v/assert kb (list holds Tom {bad :k}) CxStory))))))
        (testing "inside a rule antecedent"
          (is (= :not-encodable
                 (:type (refusal #(v/assert-rule kb [(list holds '?x bad)]
                                                 (list holds '?x Tom) CxStory
                                                 {:direction :forward}))))))))))

(deftest assert-inert-refuses-a-non-serializable-value-too
  ;; The other door that persists and indexes, guarded the same way.
  (tu/with-terms [holds Tom CxStory]
    (tu/with-cleared-kb [kb tu/fresh]
      (is (= :not-encodable
             (:type (refusal #(v/assert-inert kb (list holds Tom (atom 1)) CxStory))))))))

(deftest check-predicts-the-encodable-refusal
  ;; check reports what assert would do, under the same :type — and passes a sentence
  ;; whose values all round-trip.
  (tu/with-terms [holds Tom CxStory]
    (tu/with-cleared-kb [kb tu/fresh]
      (let [bad (list holds Tom (fn [_] 1))]
        (is (= :not-encodable (:type (first (v/check kb bad CxStory)))))
        (is (= :not-encodable (:type (refusal #(v/assert kb bad CxStory))))))
      (is (empty? (v/check kb (list holds Tom 1) CxStory))
          "an encodable sentence is not refused"))))

(deftest the-refusal-names-the-value-it-refused
  (tu/with-terms [holds Tom CxStory]
    (tu/with-cleared-kb [kb tu/fresh]
      (let [e (try (v/assert kb (list holds Tom (atom 1)) CxStory)
                   (catch clojure.lang.ExceptionInfo ex ex))
            d (ex-data e)]
        (is (= :not-encodable (:type d)))
        (is (contains? d :value) "the offending value is carried for the caller")
        (is (.contains ^String (ex-message e) "cannot be stored"))
        (is (.contains ^String (ex-message e) "clojure.lang.Atom")
            "the message names the value's type")))))

(deftest encodable-scalar-args-are-accepted
  ;; Everything nippy round-trips AND `canon` can order is admissible in argument
  ;; position.  A map or a set is neither, and is refused under the same `:type`
  ;; (`check_test/a-map-or-set-anywhere-in-a-sentence-is-refused`).
  (tu/with-terms [holds Tom CxStory]
    (tu/with-cleared-kb [kb tu/fresh]
      (testing "scalars of every storable kind assert"
        (doseq [v [42 -7 3/4 2.5 "a string" :a-keyword \c true nil]]
          (is (some? (v/assert kb (list holds Tom v) CxStory))
              (str "arg " (pr-str v))))))))

(deftest a-vector-argument-is-accepted-and-canonicalizes-to-its-list-form
  ;; Kept vectors ≡ lists: a vector argument stores, and the same content spelled as a
  ;; list finds it — one value, two spellings, as Clojure `=` already has it.
  (tu/with-terms [holds Tom CxStory]
    (tu/with-cleared-kb [kb tu/fresh]
      (v/assert kb (list holds Tom [Tom Tom]) CxStory)
      (is (seq (v/sentexes-matching kb (list holds Tom (list Tom Tom)) CxStory))
          "the list spelling of the vector argument reaches the stored fact")
      (is (seq (v/sentexes-matching kb (list holds Tom [Tom Tom]) CxStory))
          "and so does the vector spelling")
      (testing "the stored sentence is the canonical list form, not a vector"
        (let [stored (:sentence (v/sentex kb (v/handle-of kb (list holds Tom [Tom Tom])
                                                          CxStory)))]
          (is (seq? stored))
          (is (not (vector? (nth stored 2))) "the argument is a list, not a vector"))))))

;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.test-util-test
  "The harness's own refusals — `vaelii.test-util` checked the way it checks the engine.

  A test utility that accepts a shape and quietly does something else with it is worse
  than one that throws, because what it breaks is the *evidence*: a test still runs, still
  passes, and no longer means what it says.  `with-kb` is the case that motivated this
  namespace — its binding vector reads like a `let`'s and takes a symbol only, so an init
  form written there is refused at macroexpansion rather than dropped.

  **No fixture here, deliberately.**  These tests are about the harness rather than about a
  KB, and one of them calls `fresh` in the middle of a test — which is precisely what the
  `:each` net-neutrality fixture exists to catch, since a clear removes the content that
  fixture recorded its baseline against.  Adding no KB is what leaves the space as it was
  found."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.test-util :as tu]))

(defn- refusal
  "The `ex-info` refusing `form`, or nil if it expanded.  `macroexpand-1` wraps a macro's
  own throw in a `CompilerException` (phase `:macro-syntax-check`), so the reading a test
  wants is one or more causes down — and discriminating on `:type` rather than on the
  message is the convention every `ex-info` in this project is written for."
  [form]
  (try (let [_ (macroexpand-1 form)] nil)
       (catch Throwable t
         (loop [e t]
           (cond (nil? e)                                   nil
                 (instance? clojure.lang.ExceptionInfo e)   e
                 :else                                      (recur (ex-cause e)))))))

(deftest with-kb-takes-a-symbol-and-refuses-an-init-form
  (testing "the one-symbol form is what expands"
    (is (seq? (macroexpand-1 '(vaelii.test-util/with-kb [k] :body))))
    (is (nil? (refusal '(vaelii.test-util/with-kb [k] :body)))))
  (testing "an init form is refused rather than silently dropped"
    ;; The shape this exists for.  `(with-kb [k (fresh)] …)` reads as though it binds a
    ;; cleared KB and binds the fixture's instead — so a helper called twice in one test
    ;; runs its second arm over everything the first left, and a test comparing two
    ;; arrangements compares them against different baselines while still passing.
    (let [e (refusal '(vaelii.test-util/with-kb [k (vaelii.test-util/fresh)] :body))]
      (is (some? e) "an init form must not expand")
      (is (= :bad-binding (:type (ex-data e))))
      (is (re-find #"one-symbol binding vector" (ex-message e))
          "and the message says what to write instead")))
  (testing "and every other binding shape is refused too"
    (doseq [form ['(vaelii.test-util/with-kb [a b c] :body)
                  '(vaelii.test-util/with-kb [] :body)
                  '(vaelii.test-util/with-kb k :body)]]
      (is (= :bad-binding (:type (ex-data (refusal form))))
          (str "expected a refusal for " (pr-str form))))))

(deftest fresh-hands-back-a-cleared-kb
  ;; The other half of the same story: `fresh` really does clear, which is why calling it
  ;; mid-test is a live hazard rather than a no-op.  Tests needing a genuinely separate KB
  ;; give each arm its own `with-terms` (`exposure_test`'s budgeted-sweep pair) or build
  ;; over a cleared store with `with-cleared-kb`.
  (let [kb (tu/fresh)]
    (is (some? kb))
    (is (= {:sentexes 0 :justifications 0} (tu/content-count kb))
        "fresh means empty, not merely bound")))

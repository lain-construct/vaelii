;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.argue-test
  "Tests for vaelii.core/argue — four-valued epistemic status queries."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(tu/deftest-kb argue-true-for-asserted-fact
  (tu/with-terms [dog Muffet]
    (v/assert kb (list dog Muffet) 'CxUniverse)
    (is (= :true (:verdict (v/argue kb (list dog Muffet) 'CxUniverse))))))

(tu/deftest-kb argue-unknown-for-unasserted-fact
  (tu/with-terms [hungry Muffet]
    (is (= :unknown (:verdict (v/argue kb (list hungry Muffet) 'CxUniverse))))))

(tu/deftest-kb argue-false-for-explicitly-negated-fact
  (tu/with-terms [hungry Muffet]
    (v/assert kb (list 'not (list hungry Muffet)) 'CxUniverse)
    (is (= :false (:verdict (v/argue kb (list hungry Muffet) 'CxUniverse))))))

(tu/deftest-kb argue-contradiction-for-both-sides-at-default
  (tu/with-terms [hungry Muffet]
    (v/assert kb (list hungry Muffet) 'CxUniverse)
    (v/assert kb (list 'not (list hungry Muffet)) 'CxUniverse)
    (is (= :contradiction (:verdict (v/argue kb (list hungry Muffet) 'CxUniverse))))))

(tu/deftest-kb argue-true-via-genl
  (tu/with-terms [dog animal Muffet]
    (v/assert kb (list dog Muffet) 'CxUniverse)
    (v/assert kb (list 'genl dog animal) 'CxUniverse)
    (is (= :true (:verdict (v/argue kb (list animal Muffet) 'CxUniverse))))))

(tu/deftest-kb argue-rule-expansion-with-max-depth
  (tu/with-terms [dog hasFur Muffet]
    (v/assert kb (list dog Muffet) 'CxUniverse)
    (v/assert-rule kb [(list dog '?x)] (list hasFur '?x) 'CxUniverse {:direction :backward})
    (testing "without opts: ask does not fire backward rules"
      (is (= :unknown (:verdict (v/argue kb (list hasFur Muffet) 'CxUniverse)))))
    (testing "with max-depth: rules fire"
      (is (= :true (:verdict (v/argue kb (list hasFur Muffet) 'CxUniverse {:max-depth 3})))))))

(tu/deftest-kb argue-monotonic-wins-over-default
  (tu/with-terms [hungry Muffet]
    (v/assert kb (list 'not (list hungry Muffet)) 'CxUniverse {:strength :default})
    (v/assert kb (list hungry Muffet) 'CxUniverse {:strength :monotonic})
    (is (= :true (:verdict (v/argue kb (list hungry Muffet) 'CxUniverse))))))

(tu/deftest-kb argue-refuses-an-option-it-does-not-read-at-its-own-door
  ;; `argue` reaches `query` only when `:max-depth` is there and takes the
  ;; no-rule-expansion `ask` arm otherwise, so a roster checked downstream is not checked
  ;; at all for exactly the misspelling that matters: `{:max-deph 3}` would answer
  ;; `:unknown` for a sentence a rule derives, which is the failure the docstring says
  ;; must not happen.  The check is `argue`'s own, and the roster is `query`'s.
  (tu/with-terms [dog hasFur Muffet]
    (v/assert kb (list dog Muffet) 'CxUniverse)
    (v/assert-rule kb [(list dog '?x)] (list hasFur '?x) 'CxUniverse {:direction :backward})
    (let [goal    (list hasFur Muffet)
          refusal (fn [opts]
                    (try (v/argue kb goal 'CxUniverse opts) nil
                         (catch clojure.lang.ExceptionInfo e (ex-data e))))]
      (testing "a misspelt depth is refused rather than taking the facts-only arm"
        (doseq [opts [{:max-deph 3} {:max-depth 3 :max-deph 4} {:nonsense 1}]]
          (let [d (refusal opts)]
            (is (= :unknown-option (:type d)) (pr-str opts))
            (is (= (vec (sort v/query-opt-keys)) (:options d)) "and the refusal names the roster")
            (is (seq (:unknown d))))))
      (testing "a non-map opts too"
        (is (= :unknown-option (:type (refusal :oops))))
        (is (= :unknown-option (:type (refusal [:max-depth 3])))))
      (testing "and every rostered key still answers"
        (is (= :true (:verdict (v/argue kb goal 'CxUniverse {:max-depth 3}))))
        (is (= :true (:verdict (v/argue kb goal 'CxUniverse
                                        {:max-depth 3 :strategy :depth-first}))))
        (is (= :unknown (:verdict (v/argue kb goal 'CxUniverse nil))))))))

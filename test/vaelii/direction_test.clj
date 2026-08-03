;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.direction-test
  "Directed rules via the set/forwardRule, set/backwardRule, set/inertRule virtual
  predicates."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.rules :as vr]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(tu/deftest-kb forward-rule-materializes
  (let [parentOf (tu/tmp-pred) ancestorOf (tu/tmp-pred)
        tom (tu/tmp-ind) bob (tu/tmp-ind)
        ancestor-rule (vr/rule-sentence [(list parentOf '?x '?y)] (list ancestorOf '?x '?y))]
    (v/assert kb (list 'set/forwardRule ancestor-rule) 'FamContext)
    (v/assert kb (list parentOf tom bob) 'FamContext)
    (testing "a forward rule forward-chains its consequent"
      (is (seq (v/sentexes-matching kb (list ancestorOf tom bob) 'FamContext))))))

(tu/deftest-kb backward-rule-does-not-materialize-but-proves
  (let [parentOf (tu/tmp-pred) ancestorOf (tu/tmp-pred)
        tom (tu/tmp-ind) bob (tu/tmp-ind)
        ancestor-rule (vr/rule-sentence [(list parentOf '?x '?y)] (list ancestorOf '?x '?y))]
    (v/assert kb (list 'set/backwardRule ancestor-rule) 'FamContext)
    (v/assert kb (list parentOf tom bob) 'FamContext)
    (testing "a backward rule is not forward-materialized"
      (is (empty? (v/sentexes-matching kb (list ancestorOf tom bob) 'FamContext))))
    (testing "but it answers backward queries"
      (is (v/provable? kb (list ancestorOf tom bob) 'FamContext)))))

(tu/deftest-kb inert-rule-is-documentation-only
  (let [parentOf (tu/tmp-pred) ancestorOf (tu/tmp-pred)
        tom (tu/tmp-ind) bob (tu/tmp-ind)
        ancestor-rule (vr/rule-sentence [(list parentOf '?x '?y)] (list ancestorOf '?x '?y))]
    (v/assert kb (list 'set/inertRule ancestor-rule) 'FamContext)
    (v/assert kb (list parentOf tom bob) 'FamContext)
    (testing "an inert rule drives no inference"
      (is (empty? (v/sentexes-matching kb (list ancestorOf tom bob) 'FamContext)))
      (is (not (v/provable? kb (list ancestorOf tom bob) 'FamContext))))
    (testing "but the rule sentex is stored and findable by its terms"
      (is (= 1 (count (v/find-sentexes kb ancestorOf)))))))

(tu/deftest-kb direction-via-opts
  (let [parentOf (tu/tmp-pred) ancestorOf (tu/tmp-pred)
        tom (tu/tmp-ind) bob (tu/tmp-ind)]
    (v/assert-rule kb [(list parentOf '?x '?y)] (list ancestorOf '?x '?y) 'FamContext {:direction :backward})
    (v/assert kb (list parentOf tom bob) 'FamContext)
    (testing ":direction opt matches the virtual-predicate behavior"
      (is (empty? (v/sentexes-matching kb (list ancestorOf tom bob) 'FamContext)))
      (is (v/provable? kb (list ancestorOf tom bob) 'FamContext)))))

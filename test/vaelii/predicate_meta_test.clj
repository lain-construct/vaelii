;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.predicate-meta-test
  "Predicate metadata: transitive / symmetric / inverse / reflexive generic
  provers, and the functional constraint."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(tu/deftest-kb transitive-predicate
  (let [partOf (tu/tmp-pred)
        wheel (tu/tmp-ind) car (tu/tmp-ind) vehicle (tu/tmp-ind) machine (tu/tmp-ind)]
    (v/assert kb (list 'transitive partOf) 'NaturalWorldContext)
    (v/assert kb (list partOf wheel car)     'NaturalWorldContext)
    (v/assert kb (list partOf car vehicle)   'NaturalWorldContext)
    (v/assert kb (list partOf vehicle machine) 'NaturalWorldContext)
    (testing "transitive closure over facts"
      (is (v/ask? kb (list partOf wheel machine) 'NaturalWorldContext))   ; 3 steps
      (is (= #{car vehicle machine}
             (set (map #(get % '?w) (v/ask kb (list partOf wheel '?w) 'NaturalWorldContext))))))
    (testing "non-parts are not derived"
      (is (not (v/ask? kb (list partOf machine wheel) 'NaturalWorldContext))))))

(tu/deftest-kb symmetric-predicate
  (let [siblingOf (tu/tmp-pred) bob (tu/tmp-ind) ann (tu/tmp-ind)]
    (v/assert kb (list 'symmetric siblingOf) 'NaturalWorldContext)
    (v/assert kb (list siblingOf bob ann) 'NaturalWorldContext)
    (testing "the relation holds both ways though asserted once"
      (is (v/ask? kb (list siblingOf bob ann) 'NaturalWorldContext))
      (is (v/ask? kb (list siblingOf ann bob) 'NaturalWorldContext))     ; via the symmetric prover
      (is (= #{ann} (set (map #(get % '?x) (v/ask kb (list siblingOf '?x bob) 'NaturalWorldContext))))))))

(tu/deftest-kb inverse-predicate
  (let [parentOf (tu/tmp-pred) childOf (tu/tmp-pred) tom (tu/tmp-ind) bob (tu/tmp-ind)]
    (v/assert kb (list 'inverse parentOf childOf) 'NaturalWorldContext)
    (v/assert kb (list parentOf tom bob) 'NaturalWorldContext)
    (testing "the inverse is answerable from the forward facts"
      (is (v/ask? kb (list childOf bob tom) 'NaturalWorldContext))
      (is (= #{tom} (set (map #(get % '?p) (v/ask kb (list childOf bob '?p) 'NaturalWorldContext))))))))

(tu/deftest-kb reflexive-predicate
  (let [sameRegionAs (tu/tmp-pred) paris (tu/tmp-ind) rome (tu/tmp-ind)]
    (v/assert kb (list 'reflexive sameRegionAs) 'NaturalWorldContext)
    (testing "everything is in the relation with itself"
      (is (v/ask? kb (list sameRegionAs paris paris) 'NaturalWorldContext))
      (is (not (v/ask? kb (list sameRegionAs paris rome) 'NaturalWorldContext))))))

(tu/deftest-kb functional-constraint
  (let [birthYearOf (tu/tmp-pred) tom (tu/tmp-ind)]
    (v/assert kb (list 'functional birthYearOf) 'NaturalWorldContext)
    (v/assert kb (list birthYearOf tom 1980) 'NaturalWorldContext)
    (testing "a second, different value is rejected"
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list birthYearOf tom 1990) 'NaturalWorldContext))))
    (testing "re-asserting the same value is fine"
      (is (v/assert kb (list birthYearOf tom 1980) 'NaturalWorldContext)))))

;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.term-index-test
  "The inverted term index (findable by any term) and ist reification."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(tu/deftest-kb findable-by-any-term
  (let [parentOf (tu/tmp-pred) likesPet (tu/tmp-pred)
        tom (tu/tmp-ind) bob (tu/tmp-ind) muffet (tu/tmp-ind)]
    (v/assert kb (list parentOf tom bob) 'CxNaturalWorld)
    (v/assert kb (list likesPet bob muffet) 'CxNaturalWorld)
    (testing "a sentex is findable by any term it contains — any position"
      (is (= 2 (count (v/find-sentexes kb bob))))        ; predicate arg in both
      (is (= 1 (count (v/find-sentexes kb tom))))
      (is (= 1 (count (v/find-sentexes kb muffet))))
      (is (= 1 (count (v/find-sentexes kb parentOf))))   ; by functor
      (is (= 2 (count (v/find-sentexes kb 'CxNaturalWorld)))))  ; by context
    (testing "intersection of several terms"
      (is (= 1 (count (v/find-sentexes-all kb [bob muffet]))))
      (is (= 0 (count (v/find-sentexes-all kb [tom muffet])))))))

(tu/deftest-kb ist-finds-or-creates
  (let [loves (tu/tmp-pred) mary (tu/tmp-ind) john (tu/tmp-ind)
        h (v/ist kb 'CxBelief (list loves mary john))]
    (testing "ist creates the sentence in the context (ist), not a wrapper"
      (is (= 1 (count (v/sentexes-matching kb (list loves mary john) 'CxBelief))))
      (is (empty? (v/find-sentexes kb 'ist))))        ; ist itself is never stored
    (testing "calling again finds the same sentex (idempotent)"
      (is (= h (v/ist kb 'CxBelief (list loves mary john)))))
    (testing "the (ist ..) form given to assert does the same"
      (is (= h (v/assert kb (list 'ist 'CxBelief (list loves mary john))))))
    (testing "the sentence is findable by any of its terms, and its contexts listed"
      (is (= 1 (count (v/find-sentexes kb (list loves mary john)))))
      (is (= 1 (count (v/find-sentexes kb mary))))
      (is (= '(CxBelief) (v/contexts-of kb (list loves mary john)))))))

(tu/deftest-kb oversized-ground-compound-capped-but-atoms-stay-findable   ; perf-review #8
  (let [holds (tu/tmp-pred) bagOf (tu/tmp-pred) pairOf (tu/tmp-pred) tag (tu/tmp-ind)
        inds  (vec (repeatedly 70 tu/tmp-ind))
        big   (apply list bagOf inds)              ; ~72-node ground compound (> cap)
        small (list pairOf (first inds) tag)       ; 4-node ground compound (< cap)
        h     (v/assert kb (list holds big small) 'CxNaturalWorld)]
    (testing "every atom of the oversized compound stays findable at any depth"
      (is (= 1 (count (v/find-sentexes kb (nth inds 40)))))   ; an individual deep inside
      (is (= 1 (count (v/find-sentexes kb bagOf))))            ; its functor symbol
      (is (= 1 (count (v/find-sentexes kb holds)))))
    (testing "the oversized whole compound is not itself an index key — and is found anyway"
      ;; the cap is a bound on what is *stored*, not on what is answerable: `find-sentexes`
      ;; narrows a compound on the atoms it contains and verifies the candidates against
      ;; their records, so a term outside either bound costs a read rather than a key.
      (is (= 1 (count (v/find-sentexes kb big))))
      (is (= #{(list holds big small)} (set (map :sentence (v/find-sentexes kb big)))))
      (is (empty? (v/find-sentexes kb (apply list bagOf (reverse inds))))
          "and a compound that was never stored is still empty"))
    (testing "a small compound in the same fact is still findable by the whole compound"
      (is (= 1 (count (v/find-sentexes kb small)))))
    (testing "indexable-terms drops the oversized compound, keeps its atoms and the small one"
      (let [terms (set (v/indexable-terms (v/sentex kb h)))]
        (is (contains? terms (nth inds 40)))
        (is (contains? terms small))
        (is (not (contains? terms big)))))))

(tu/deftest-kb term-index-cleaned-on-retract
  (let [parentOf (tu/tmp-pred) tom (tu/tmp-ind) bob (tu/tmp-ind)
        h (v/assert kb (list parentOf tom bob) 'CxNaturalWorld)]
    (is (= 1 (count (v/find-sentexes kb tom))))
    (v/retract! kb h)
    (is (empty? (v/find-sentexes kb tom)))))

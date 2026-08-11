;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.argue-test
  "Tests for vaelii.argue — four-valued epistemic status queries."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.argue :as argue]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(tu/deftest-kb argue-true-for-asserted-fact
  (v/assert kb '(dog Muffet) 'UniverseContext)
  (is (= :true (:verdict (argue/argue kb '(dog Muffet) 'UniverseContext)))))

(tu/deftest-kb argue-unknown-for-unasserted-fact
  (is (= :unknown (:verdict (argue/argue kb '(hungry Muffet) 'UniverseContext)))))

(tu/deftest-kb argue-false-for-explicitly-negated-fact
  (v/assert kb '(not (hungry Muffet)) 'UniverseContext)
  (is (= :false (:verdict (argue/argue kb '(hungry Muffet) 'UniverseContext)))))

(tu/deftest-kb argue-contradiction-for-both-sides-at-default
  (v/assert kb '(hungry Muffet) 'UniverseContext)
  (v/assert kb '(not (hungry Muffet)) 'UniverseContext)
  (is (= :contradiction (:verdict (argue/argue kb '(hungry Muffet) 'UniverseContext)))))

(tu/deftest-kb argue-true-via-genl
  (v/assert kb '(dog Muffet) 'UniverseContext)
  (v/assert kb '(genl dog animal) 'UniverseContext)
  (is (= :true (:verdict (argue/argue kb '(animal Muffet) 'UniverseContext)))))

(tu/deftest-kb argue-rule-expansion-with-max-depth
  (v/assert kb '(dog Muffet) 'UniverseContext)
  (v/assert-rule kb ['(dog ?x)] '(hasFur ?x) 'UniverseContext {:direction :backward})
  (testing "without opts: ask does not fire backward rules"
    (is (= :unknown (:verdict (argue/argue kb '(hasFur Muffet) 'UniverseContext)))))
  (testing "with max-depth: rules fire"
    (is (= :true (:verdict (argue/argue kb '(hasFur Muffet) 'UniverseContext {:max-depth 3}))))))

(tu/deftest-kb argue-monotonic-wins-over-default
  (let [kb2 (v/fork kb)]
    (v/assert kb2 '(not (hungry Muffet)) 'UniverseContext {:strength :default})
    (v/assert kb2 '(hungry Muffet) 'UniverseContext {:strength :monotonic})
    (is (= :true (:verdict (argue/argue kb2 '(hungry Muffet) 'UniverseContext))))))

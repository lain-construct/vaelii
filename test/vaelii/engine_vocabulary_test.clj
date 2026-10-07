;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.engine-vocabulary-test
  "The terms the engine reads by name are declared in CxCore, so a KB can query what the
  engine answers and the vocabulary audit classifies each one.  Each row pins one
  declaration against the engine behaviour it describes."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh #(doto (tu/fresh) (tu/load-core!))))

(def ^:private U 'CxUniverse)

;; ---- different -------------------------------------------------------------

(tu/deftest-kb different-is-declared-at-the-arity-its-prover-answers
  (testing "the declaration loads and the vocabulary audit classifies the term"
    (is (:enforced (v/interpreted 'different)))
    (is (true? (v/ask? kb '(variable_arity_predicate different) U)))
    (is (true? (v/ask? kb '(arityMin different 2) U)))
    (is (true? (v/ask? kb '(args different thing) U)))
    (is (true? (v/ask? kb '(commutative different) U))))
  (testing "two distinct names are different in either order"
    (tu/with-terms [Alpha Beta]
      (is (true? (v/ask? kb (list 'different Alpha Beta) U)))
      (is (true? (v/ask? kb (list 'different Beta Alpha) U)))
      (is (false? (v/ask? kb (list 'different Alpha Alpha) U))))))

;; ---- the equality relations and the rule and strength wrappers -------------

(tu/deftest-kb the-equality-relations-are-declared-binary-over-things
  (doseq [r '[sameAs equals]]
    (is (:enforced (v/interpreted r)) (str r " is classified enforced"))
    (is (true? (v/ask? kb (list 'binary_predicate r) U)) (str r " is a binary_predicate"))
    (is (true? (v/ask? kb (list 'arg r 1 'thing) U)))
    (is (true? (v/ask? kb (list 'arg r 2 'thing) U))))
  (testing "a merge under either relation still answers from the closure"
    (tu/with-terms [Alpha Beta Gamma Delta]
      (v/assert kb (list 'sameAs Alpha Beta) U)
      (v/assert kb (list 'equals Gamma Delta) U)
      (is (true? (v/ask? kb (list 'sameAs Beta Alpha) U)))
      (is (true? (v/ask? kb (list 'equals Delta Gamma) U)))
      (is (false? (v/ask? kb (list 'different Alpha Beta) U))))))

(tu/deftest-kb every-wrapper-the-engine-peels-is-commented-and-classified
  (doseq [w '[set/forwardRule set/backwardRule set/defaultRule set/inertRule
              set/forwardOnlyRule set/solveRule set/assumptionRule
              set/hardConstraint set/softConstraint set/monotonic]]
    (is (:enforced (v/interpreted w)) (str w " is classified enforced"))))

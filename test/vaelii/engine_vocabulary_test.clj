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

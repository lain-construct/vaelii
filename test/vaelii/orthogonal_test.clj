;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.orthogonal-test
  "`(orthogonal A B)`: the two types overlap — some thing is an instance of both — and
  neither is a subtype of the other.  Nothing is claimed about things that are instances of
  neither.  The declared spelling of the `:orthogonal` subsumption status."
  (:require [clojure.test :refer [is use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

;; `true?` around each read, so a failure prints the answer rather than the KB.

;; ---- the declaration ------------------------------------------------------

(tu/deftest-kb orthogonal-is-a-declared-term-of-the-grammar
  (is (some? (v/interpreted 'orthogonal))
      "CxCore declares orthogonal, and the vocabulary roster answers for it")
  (is (true? (v/ask? kb '(binary_predicate orthogonal))))
  (is (true? (v/ask? kb '(symmetric orthogonal))))
  (is (true? (v/ask? kb '(type_relation_predicate orthogonal)))))

(tu/deftest-kb orthogonal-is-symmetric
  (tu/with-terms [spatialKind temporalKind]
    (v/assert kb (list 'genl 'spatialKind 'thing) 'CxUniverse)
    (v/assert kb (list 'genl 'temporalKind 'thing) 'CxUniverse)
    (v/assert kb (list 'orthogonal 'temporalKind 'spatialKind) 'CxUniverse)
    (is (true? (v/ask? kb (list 'orthogonal 'spatialKind 'temporalKind) 'CxUniverse))
        "either spelling answers the one stored declaration")
    (is (true? (v/ask? kb (list 'orthogonal 'temporalKind 'spatialKind) 'CxUniverse)))))

;; ---- the subsumption status -------------------------------------------------

(tu/deftest-kb a-declared-pair-is-orthogonal-without-a-shared-instance
  (tu/with-terms [spatialKind temporalKind]
    (v/assert kb (list 'genl 'spatialKind 'thing) 'CxUniverse)
    (v/assert kb (list 'genl 'temporalKind 'thing) 'CxUniverse)
    (is (= :unknown (v/subsumption-status kb 'spatialKind 'temporalKind))
        "no relation and no shared instance yet")
    (v/assert kb (list 'orthogonal 'temporalKind 'spatialKind) 'CxUniverse)
    (is (= #{:orthogonal} (v/subsumption-statuses kb 'spatialKind 'temporalKind))
        "the declaration is the witness, whichever order it was written in")
    (is (= :orthogonal (v/subsumption-status kb 'temporalKind 'spatialKind)))))

(tu/deftest-kb a-declaration-a-narrower-context-holds-is-read-from-that-vantage
  (tu/with-terms [spatialKind temporalKind]
    (let [cx (tu/tmp-ctx)]
      (v/assert kb (list 'genlCx cx 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genl 'spatialKind 'thing) 'CxUniverse)
      (v/assert kb (list 'genl 'temporalKind 'thing) 'CxUniverse)
      (v/assert kb (list 'orthogonal 'spatialKind 'temporalKind) cx)
      (is (= :unknown (v/subsumption-status kb 'spatialKind 'temporalKind))
          "CxUniverse does not see a declaration stated below it")
      (is (= :orthogonal (v/subsumption-status kb 'spatialKind 'temporalKind cx))))))

(tu/deftest-kb a-declared-pair-that-is-also-genl-related-is-inconsistent
  (tu/with-terms [alphaKind betaKind]
    (v/assert kb (list 'genl 'alphaKind 'thing) 'CxUniverse)
    (v/assert kb (list 'genl 'betaKind 'alphaKind) 'CxUniverse)
    (v/assert kb (list 'orthogonal 'alphaKind 'betaKind) 'CxUniverse {:strength :monotonic})
    (is (= #{:spec :orthogonal} (v/subsumption-statuses kb 'alphaKind 'betaKind)))
    (is (= :inconsistent (v/subsumption-status kb 'alphaKind 'betaKind)))))

(tu/deftest-kb a-declared-pair-that-is-also-disjoint-is-inconsistent
  (tu/with-terms [alphaKind betaKind]
    (v/assert kb (list 'genl 'alphaKind 'thing) 'CxUniverse)
    (v/assert kb (list 'genl 'betaKind 'thing) 'CxUniverse)
    (v/assert kb (list 'disjoint 'alphaKind 'betaKind) 'CxUniverse)
    (v/assert kb (list 'orthogonal 'alphaKind 'betaKind) 'CxUniverse {:strength :monotonic})
    (is (= #{:disjoint :orthogonal} (v/subsumption-statuses kb 'alphaKind 'betaKind)))
    (is (= :inconsistent (v/subsumption-status kb 'betaKind 'alphaKind)))))

(tu/deftest-kb the-audit-counts-a-declared-pair-as-known
  (tu/with-terms [spatialKind temporalKind]
    (v/assert kb (list 'genl 'spatialKind 'thing) 'CxUniverse)
    (v/assert kb (list 'genl 'temporalKind 'thing) 'CxUniverse)
    (let [row (fn [] (first (filter #(= #{'spatialKind 'temporalKind} (hash-set (:a %) (:b %)))
                                    (:pairs-data (v/disjointness-audit kb)))))
          before (row)]
      (is (= :unknown (:status before)))
      (v/assert kb (list 'orthogonal 'spatialKind 'temporalKind) 'CxUniverse)
      (is (= :orthogonal (:status (row)))
          "a declared pair leaves the audit's unknown candidates"))))

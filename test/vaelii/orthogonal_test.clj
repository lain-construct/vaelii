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

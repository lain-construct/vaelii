;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.metatype-orthogonal-test
  "The higher-order type relations that state many pairs at once: `typeOrthogonal`
  makes every member of a classifier orthogonal to one type, `orthogonalMetatypes`
  makes every member of each named metatype orthogonal to every member of the others,
  and `partitionedByType` places every member of a classifier under a whole and
  separates the members.  Each is a CxCore rule generator, so the pairs it concludes
  are derived and the KB does not state them.  The upper types `logical` and
  `quantitative` and the documentation predicate `implementationNote` are pinned here
  too."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

;; ---- implementationNote ------------------------------------------------------

(tu/deftest-kb an-implementation-note-is-a-sibling-of-comment
  (is (true? (v/ask? kb '(binary_predicate implementationNote) 'CxCore)))
  (is (true? (v/ask? kb '(termsRelated comment implementationNote) 'CxCore)))
  (is (not (v/genl? kb 'implementationNote 'comment)))
  (is (not (v/genl? kb 'comment 'implementationNote)))
  (doseq [t '[formula sentence non_atomic_term unrepresented_term symbol logical_constant]]
    (is (seq (v/sentexes-matching kb (list 'implementationNote t '?note) 'CxCore))
        (str t " carries an implementation note"))))


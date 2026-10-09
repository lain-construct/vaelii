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

(defn- derived-not-stated?
  "Is `(pred a b)` believed in `ctx` with no premise stating it in any context?"
  [kb pred a b ctx]
  (and (true? (v/ask? kb (list pred a b) ctx))
       (not-any? #(v/premise? kb (:id %))
                 (concat (v/sentexes-matching kb (list pred a b) '?ctx)
                         (v/sentexes-matching kb (list pred b a) '?ctx)))))

;; ---- typeOrthogonal ---------------------------------------------------------

(tu/deftest-kb a-member-of-the-classifier-is-orthogonal-to-the-type
  (tu/with-terms [origin_kind crafted grown edible]
    (doseq [t [crafted grown edible]] (v/assert kb (list 'genl t 'tangible) 'CxUniverse))
    (v/assert kb (list 'metatype origin_kind) 'CxUniverse)
    (v/assert kb (list 'forced_monotonic_predicate origin_kind) 'CxUniverse)
    (v/assert kb (list origin_kind crafted) 'CxUniverse)
    (v/assert kb (list 'typeOrthogonal origin_kind edible) 'CxUniverse)
    (is (true? (v/ask? kb (list 'orthogonal crafted edible) 'CxUniverse)))
    (is (= :orthogonal (v/subsumption-status kb crafted edible)))
    (testing "a member that arrives later is concluded orthogonal too"
      (v/assert kb (list origin_kind grown) 'CxUniverse)
      (is (true? (v/ask? kb (list 'orthogonal grown edible) 'CxUniverse))))
    (is (not-any? #(= :forced-conclusion (:violation %)) (v/violations kb)))))

(def ^:private origin-crossers
  "The types every origin_type member (made, natural) is orthogonal to."
  '[organism biological body_part substance food animal])

(tu/deftest-kb what-cuts-across-made-and-natural-is-derived-from-origin-type
  (is (true? (v/ask? kb '(origin_type made) 'CxAbstract)))
  (is (true? (v/ask? kb '(origin_type natural) 'CxAbstract)))
  (doseq [t origin-crossers, o '[made natural]]
    (is (true? (v/ask? kb (list 'typeOrthogonal 'origin_type t) 'CxAbstract)))
    (is (derived-not-stated? kb 'orthogonal t o 'CxAbstract)
        (str "(orthogonal " t " " o ") is derived and not stated"))
    (is (= :orthogonal (v/subsumption-status kb t o)))))

(tu/deftest-kb abducibility-is-orthogonal-to-every-arity-type
  (doseq [a '[unary binary ternary fixed_arity variable_arity bounded_arity unbounded_arity
              at_least_binary at_least_ternary]]
    (is (true? (v/ask? kb (list 'arity_type a) 'CxCore)) (str a " is an arity_type"))
    (is (derived-not-stated? kb 'orthogonal a 'abducible_predicate 'CxCore)
        (str "(orthogonal " a " abducible_predicate) is derived"))
    (is (= :orthogonal (v/subsumption-status kb a 'abducible_predicate)))))

(tu/deftest-kb a-type-of-each-order-may-be-empty-or-nonempty
  (doseq [o '[type metatype meta_metatype], e '[empty nonempty]]
    (is (derived-not-stated? kb 'orthogonal o e 'CxCore)
        (str "(orthogonal " o " " e ") is derived from (typeOrthogonal type_type_by_order " e ")"))))

;; ---- logical and quantitative -------------------------------------------------

(tu/deftest-kb logical-linguistic-and-quantitative-are-separated-under-nowhere-never
  (doseq [t '[logical linguistic quantitative]]
    (is (true? (v/genl? kb t 'nowhere_never 'CxCore))))
  (doseq [[a b] '[[logical linguistic] [logical quantitative] [linguistic quantitative]]]
    (is (true? (v/disjoint? kb a b 'CxCore))))
  (doseq [t '[relation context]]
    (is (true? (v/genl? kb t 'logical 'CxCore))))
  (is (true? (v/genl? kb 'proposition 'logical 'CxReflection)))
  (is (true? (v/genl? kb 'measure 'quantitative 'CxCore)))
  (doseq [t '[unit_of_measure physical_dimension sign_value]]
    (is (true? (v/genl? kb t 'quantitative 'CxMeasure))))
  (is (not (v/genl? kb 'quantity 'quantitative)) "a quantity is temporal and not quantitative"))

;; ---- the orthogonal pairs the disjointness audit ruled -------------------------

(tu/deftest-kb the-audited-overlapping-pairs-read-orthogonal
  (doseq [[a b] '[[made vertebrate] [made invertebrate] [made solid]
                  [animal mortal] [animal dead] [animal alive] [animal food]
                  [biological container] [literal wff_expression]]]
    (is (= :orthogonal (v/subsumption-status kb a b)) (str a " and " b " read orthogonal"))))

;; ---- implementationNote ------------------------------------------------------

(tu/deftest-kb an-implementation-note-is-a-sibling-of-comment
  (is (true? (v/ask? kb '(binary_predicate implementationNote) 'CxCore)))
  (is (true? (v/ask? kb '(termsRelated comment implementationNote) 'CxCore)))
  (is (not (v/genl? kb 'implementationNote 'comment)))
  (is (not (v/genl? kb 'comment 'implementationNote)))
  (doseq [t '[formula sentence non_atomic_term unrepresented_term symbol logical_constant]]
    (is (seq (v/sentexes-matching kb (list 'implementationNote t '?note) 'CxCore))
        (str t " carries an implementation note"))))


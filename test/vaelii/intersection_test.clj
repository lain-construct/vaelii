;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.intersection-test
  "The `intersection` definitional collection relation: (intersection ?combined . ?types)
  declares ?combined as the intersection of ?types. Two defining directions, each proven
  to *fire* into materialized, justified facts:

    * intersection -> genl: the combined kind is a subtype of each type it intersects.
    * membership: a thing that is each type is concluded a member of the combined kind
      (a generator stamps a concrete-functor rule per intersection fact, since the
      membership consequent's predicate is a variable).

  Binary and ternary arities; general arity is future work. See CxCore."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(defn- believes?
  [kb sentence ctx]
  (boolean (seq (v/sentexes-matching kb sentence ctx))))

;; ---- binary: intersection -> genl ----------------------------------------

(tu/deftest-kb binary-intersection-derives-genl-of-each-type
  (tu/with-terms [combined_kind type_a type_b]
    (v/assert kb (list 'genl 'type_a 'thing) 'CxUniverse)
    (v/assert kb (list 'genl 'type_b 'thing) 'CxUniverse)
    (v/assert kb (list 'intersection 'combined_kind 'type_a 'type_b) 'CxUniverse)
    (is (v/ask? kb (list 'genl 'combined_kind 'type_a) 'CxUniverse)
        "combined kind is genl the first type it intersects")
    (is (v/ask? kb (list 'genl 'combined_kind 'type_b) 'CxUniverse)
        "combined kind is genl the second type it intersects")))

;; ---- binary: membership --------------------------------------------------

(tu/deftest-kb binary-intersection-concludes-membership-from-the-conjuncts
  (tu/with-terms [combined_kind type_a type_b]
    (v/assert kb (list 'genl 'type_a 'thing) 'CxUniverse)
    (v/assert kb (list 'genl 'type_b 'thing) 'CxUniverse)
    (v/assert kb (list 'intersection 'combined_kind 'type_a 'type_b) 'CxUniverse)
    (v/assert kb (list 'type_a 'Item) 'CxUniverse)
    (v/assert kb (list 'type_b 'Item) 'CxUniverse)
    (is (believes? kb (list 'combined_kind 'Item) 'CxUniverse)
        "a thing that is each type is a member of the combined kind")))

(tu/deftest-kb binary-intersection-membership-needs-every-conjunct
  (tu/with-terms [combined_kind type_a type_b]
    (v/assert kb (list 'genl 'type_a 'thing) 'CxUniverse)
    (v/assert kb (list 'genl 'type_b 'thing) 'CxUniverse)
    (v/assert kb (list 'intersection 'combined_kind 'type_a 'type_b) 'CxUniverse)
    (v/assert kb (list 'type_a 'Item) 'CxUniverse)
    (is (not (believes? kb (list 'combined_kind 'Item) 'CxUniverse))
        "being only one of the types does not make a member of the combined kind")))

;; ---- ternary -------------------------------------------------------------

(tu/deftest-kb ternary-intersection-derives-genl-and-membership
  (tu/with-terms [combined_kind type_a type_b type_c]
    (v/assert kb (list 'genl 'type_a 'thing) 'CxUniverse)
    (v/assert kb (list 'genl 'type_b 'thing) 'CxUniverse)
    (v/assert kb (list 'genl 'type_c 'thing) 'CxUniverse)
    (v/assert kb (list 'intersection 'combined_kind 'type_a 'type_b 'type_c) 'CxUniverse)
    (is (v/ask? kb (list 'genl 'combined_kind 'type_c) 'CxUniverse)
        "combined kind is genl the third type in a ternary intersection")
    (testing "membership requires all three"
      (v/assert kb (list 'type_a 'Item) 'CxUniverse)
      (v/assert kb (list 'type_b 'Item) 'CxUniverse)
      (is (not (believes? kb (list 'combined_kind 'Item) 'CxUniverse))
          "two of three is not enough")
      (v/assert kb (list 'type_c 'Item) 'CxUniverse)
      (is (believes? kb (list 'combined_kind 'Item) 'CxUniverse)
          "all three makes a member"))))

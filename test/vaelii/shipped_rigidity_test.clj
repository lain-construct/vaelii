;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.shipped-rigidity-test
  "The rigidity kinds the shipped ontology states for its own relations.

  Each family is read through one or more representative members, in the context that
  sees the family's definitions.  A relation of one kind is believed of no other, so each
  check reads all three kinds."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(def ^:private kinds
  '[time_invariant_relation time_agnostic_relation time_varying_relation])

(defn- kinds-of
  "The rigidity kinds `relation` is believed to have in `context`."
  [kb relation context]
  (set (filter #(v/ask? kb (list % relation) context) kinds)))

(defn- all-of-kind
  [kb kind relations context]
  (doseq [r relations]
    (is (= #{kind} (kinds-of kb r context)) (str r " is " kind " and of no other kind"))))

(tu/deftest-kb types-over-atemporal-things-and-every-metatype-are-time-invariant
  ;; A number, an expression, a relation or a type exists outside time, so nothing can
  ;; stop being one.  A metatype's members are types, so every metatype is invariant too.
  (testing "types over numbers, expressions and other atemporal things"
    (all-of-kind kb 'time_invariant_relation
                 '[number non_positive_integer atomic_expression open_expression
                   ill_formed_expression logical aspatial atemporal]
                 'CxUniverse))
  (testing "types over relations, functions and types"
    (all-of-kind kb 'time_invariant_relation
                 '[relation unary_function binary_predicate symmetric type
                   time_varying_relation]
                 'CxUniverse))
  (testing "every member of arity_type, through one genl edge"
    (is (v/ask? kb '(genl arity_type time_invariant_relation) 'CxUniverse))
    (all-of-kind kb 'time_invariant_relation '[unary binary at_least_binary variable_arity]
                 'CxUniverse))
  (testing "metatypes"
    (all-of-kind kb 'time_invariant_relation
                 '[stuff_type_by_state_of_matter folk_species vertebrate_class rigidity_kind
                   at_least_metatype arity_type]
                 'CxUniverse)))

(tu/deftest-kb folk-kinds-are-time-invariant
  ;; A mouse is a mouse for as long as it exists.  Two genl edges classify every folk
  ;; species and every member of folk_biological_class, flower included.
  (is (v/ask? kb '(genl folk_species time_invariant_relation) 'CxUniverse))
  (is (v/ask? kb '(genl folk_biological_class time_invariant_relation) 'CxUniverse))
  (all-of-kind kb 'time_invariant_relation
               '[mouse human dog rose oak flower mammal bird insect arachnid tree]
               'CxUniverse))

(tu/deftest-kb meta-and-logical-predicates-are-time-invariant
  ;; Their arguments are relations, expressions, numbers or terms, none of which can
  ;; change what holds between them.
  (all-of-kind kb 'time_invariant_relation
               '[arity admitsArgnum arityMin functionCorrespondingPredicate implies not and
                 forall thereExists equals different lessThan termsRelated
                 borderlineExample comment means]
               'CxUniverse))

(tu/deftest-kb kinship-and-biology-are-time-invariant
  ;; Whoever is a thing's mother is its mother for as long as both exist.
  (all-of-kind kb 'time_invariant_relation
               '[parentOf childOf motherOf fatherOf ancestorOf siblingOf birthYearOf mortal
                 warm_blooded MotherFn FatherFn]
               'CxUniverse))

(tu/deftest-kb social-relations-are-time-varying
  ;; Any employment, friendship or ownership can end with both parties still existing.
  (all-of-kind kb 'time_varying_relation
               '[worksFor friendOf likes owns memberOf marriedTo speaks]
               'CxUniverse)
  (testing "CxSocial's own relations, in the context that defines them"
    (all-of-kind kb 'time_varying_relation '[coworkerOf roommateOf romanticPartnerOf]
                 'CxSocial)))

(tu/deftest-kb a-quantitys-sign-trend-and-derivative-are-time-varying
  ;; A quantity changes: the tap is shut, and its flow rate's sign goes to zero.
  (all-of-kind kb 'time_varying_relation '[signOf trendOf derivativeOf] 'CxUniverse))

(tu/deftest-kb spatial-relations-are-time-agnostic
  ;; A ship very far from its home port can sail home, and two points of a mathematical
  ;; plane can never move, so some instances could lose the relation and some could not.
  (all-of-kind kb 'time_agnostic_relation
               '[veryFarFrom moderatelyFarFrom northwestOf behindRightOf eastOf
                 regionConnectedTo partOfRegion withinNearDistanceOf]
               'CxUniverse))

(tu/deftest-kb type-relation-and-argument-declaration-predicates-are-time-invariant
  ;; A sentence of one of these is shorthand for a rule over type membership, and it
  ;; relates types or relations, which exist outside time.
  (all-of-kind kb 'time_invariant_relation
               '[disjoint partition covering separating orthogonal intersection genl genlCx
                 typeGenl typeOrthogonal arg genlArg result defnIff transitiveInArg]
               'CxUniverse))

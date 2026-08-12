;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.generate-test
  "The synthetic KB generator: that a plan is a function of its parameters, that what it
  generates is well-formed by the naming invariants, and that loading it produces the
  shape the numbers asked for — with nothing dropped."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.io.generate :as gen]
            [vaelii.impl.naming :as nm]
            [vaelii.test-util :as tu]))

(def ^:private small
  "A KB small enough to assert about exhaustively, with every knob off its default so a
  parameter that is silently ignored shows up as a wrong count."
  {:types 12 :branching 3 :individuals 20 :predicates 9 :facts 40 :rules 8
   :forward 50 :defeasible 25 :antecedents 2 :layers 3 :contexts 2 :seed 5})

(deftest a-plan-with-fewer-predicates-than-layers-still-draws-every-rule
  ;; a band past the vocabulary is dropped rather than emitted empty: predicates 2
  ;; under layers 3 otherwise puts `(nth [] …)` inside the lazy rule draw, and the
  ;; throw lands mid-load, after the vocabulary has already been asserted
  (doseq [[preds layers] [[2 3] [4 6] [2 8]]]
    (let [p (gen/plan (assoc small :predicates preds :layers layers :rules 20))]
      (is (= 20 (count (doall (:rules p))))
          (str "every rule drawn at predicates " preds " layers " layers))
      (is (every? (comp some? first :consequent) (:rules p))
          "and every consequent names a predicate"))))

;; ---- the plan is a function of the parameters ---------------------------

(deftest plan-is-deterministic-in-its-seed
  (testing "the same parameters describe the same KB, every time"
    (let [a (gen/plan small)
          b (gen/plan small)]
      (is (= (vec (:facts a)) (vec (:facts b))))
      (is (= (vec (:rules a)) (vec (:rules b))))
      (is (= (vec (:memberships a)) (vec (:memberships b))))))
  (testing "a different seed describes a different one"
    (is (not= (vec (:facts (gen/plan small)))
              (vec (:facts (gen/plan (assoc small :seed 6))))))))

(deftest plan-counts-are-what-was-asked-for
  (let [{:keys [genls memberships facts rules units]} (gen/plan small)]
    (is (= (:types small) (count genls)))
    (is (= (:individuals small) (count memberships)))
    (is (= (:facts small) (count facts)))
    (is (= (:rules small) (count rules)))
    (testing "units is the assertion count a progress bar divides by"
      (is (= units (+ (:contexts small) (:types small) (:individuals small)
                      (:facts small) (:rules small)))))))

(deftest generated-names-satisfy-the-naming-invariants
  (let [{:keys [genls memberships facts rules context-edges]} (gen/plan small)]
    (testing "types are snake_case and used at arity 1"
      (doseq [[_ sub _] genls] (is (nm/type-symbol? sub)))
      (doseq [[s _] memberships]
        (is (nm/type-symbol? (nm/functor s)))
        (is (= 1 (nm/arity s)))))
    (testing "individuals are CapitalCamelCase, predicates camelCase"
      (doseq [[s _] (take 20 facts)]
        (is (nm/predicate? (nm/functor s)))
        (is (every? nm/individual? (nm/args s)))))
    (testing "contexts end in Context"
      (doseq [[_ sub super] context-edges]
        (is (nm/context? sub))
        (is (nm/context? super))))
    (testing "no literal of a rule breaks a naming invariant"
      (doseq [r rules]
        (is (empty? (nm/problems (list 'implies (cons 'and (:antecedents r))
                                       (:consequent r))
                                 'GeneratedContext)))))))

(deftest rules-are-range-restricted-and-stratified
  (let [{:keys [rules]} (gen/plan (assoc small :rules 200))]
    (testing "every consequent variable is bound by an antecedent"
      (doseq [{:keys [antecedents consequent]} rules]
        (let [bound (into #{} (mapcat #(filter symbol? (nm/args %))) antecedents)]
          (is (every? bound (filter #(re-find #"^\?" (name %)) (nm/args consequent)))))))
    (testing "a rule concludes strictly above the layer it reads from, so the rule set
              is acyclic and forward chaining terminates"
      (let [layer-of (fn [p] (some (fn [[k ps]] (when (ps p) k))
                                   (map-indexed vector
                                                (map set (#'gen/bands
                                                          (max 2 (:predicates small))
                                                          (:layers small))))))]
        (doseq [{:keys [antecedents consequent layer]} rules]
          (is (= layer (layer-of (nm/functor consequent))))
          (doseq [a antecedents]
            (is (< (layer-of (nm/functor a)) layer))))))))

;; ---- loading one ---------------------------------------------------------

(deftest loading-a-generated-kb-produces-the-shape-asked-for
  (tu/with-cleared-kb [kb tu/fresh]
    (let [phases (atom [])
          r (gen/load-into kb small {:on-progress #(swap! phases conj (:phase %))})]
      (testing "the summary reports what landed"
        (is (pos? (:stored r)))
        (is (= (merge gen/defaults small) (:params r))))
      (testing "progress runs through the phases in load order and ends at :done"
        (is (= [:vocabulary :contexts :types :individuals :rules :facts :done]
               (vec (distinct @phases)))))
      (testing "the type hierarchy is rooted at thing"
        (is (contains? (v/genls kb 'gen_type_11) 'thing))
        (is (contains? (v/specs kb 'thing) 'gen_type_0)))
      (testing "the fact contexts are a chain under the schema context, so any two facts
                a rule joins have a common descendant to put its conclusion in"
        (is (v/sees? kb 'GenBand1Context 'GenBand0Context))
        (is (v/sees? kb 'GenBand0Context 'GeneratedContext)))
      (testing "the rules are there, in the mix that was asked for"
        (let [rules (filter :antecedent (v/sentexes-in-context kb 'GeneratedContext))]
          (is (= (:rules small) (count rules)))
          (is (= 4 (count (filter #(= :forward (:direction %)) rules))))
          (is (= 2 (count (filter :defeasible rules)))))))))

(deftest ^:slow a-generated-kb-derives-cleanly
  (testing "chaining over a generated corpus drops nothing: every firing has a placement
            context, and no definitional check refuses a conclusion"
    (tu/with-cleared-kb [kb tu/fresh]
      ;; individuals ≈ facts keeps the joins sparse, which is what a real corpus looks
      ;; like; a handful of individuals shared by every fact is a cross product, and the
      ;; depth bound (not this test) is what keeps *that* case finite
      (let [r (gen/load-into kb (assoc small :individuals 200 :facts 200 :rules 20
                                       :forward 100 :chain? true))]
        (is (pos? (:derived r)))
        (is (empty? (v/violations kb)))
        (is (empty? (v/conflicts kb)))))))

(deftest the-progress-callback-can-cancel-a-load
  (testing "a callback that throws stops the load where it stands — the seam the catalog
            cancels on"
    (tu/with-cleared-kb [kb tu/fresh]
      (let [seen (atom 0)]
        (is (thrown-with-msg?
             clojure.lang.ExceptionInfo #"enough"
             (gen/load-into kb (assoc small :facts 100000)
                            {:on-progress (fn [_]
                                            (when (< 3 (swap! seen inc))
                                              (throw (ex-info "enough" {}))))})))
        (testing "and what had landed before the throw is still there — a load is not a
                  transaction, and the catalog's unload is what cleans it up"
          (is (pos? (count (v/types kb)))))))))

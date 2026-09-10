;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.asp-prover-test
  "The `(bravely S)` / `(cautiously S)` prover (`vaelii.impl.asp.prover`, opted in with
  `add-reasoner :brave-cautious`): a read-path brave/cautious classification of the current
  dilemmas that commits nothing.  Solver-dependent tests skip without a backend, where the
  classification degrades to everything `:supportable`; the not-assertible refusal does not,
  since it is backend-independent."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.asp.prover :as prover]
            [vaelii.impl.asp.solver :as solver]
            [vaelii.impl.rules :as vr]
            [vaelii.test-util :as tu]))

(def ^:private asp? (solver/available?))

(defn- default-rule [antes conseq]
  (list 'set/defaultRule (list 'set/forwardRule (vr/rule-sentence antes conseq))))

(defn- nixon-diamond
  "The canonical rebutting dilemma on gensym'd terms: two equally-specific defaults
  concluding `(pacifist N)` and `(not (pacifist N))`.  Returns the terms and both handles."
  [kb]
  (let [quaker (tu/tmp-pred) pacifist (tu/tmp-pred) republican (tu/tmp-pred)
        nixon  (tu/tmp-ind)]
    (v/assert kb (default-rule [(list quaker '?x)]     (list pacifist '?x))             'CxUniverse)
    (v/assert kb (default-rule [(list republican '?x)] (list 'not (list pacifist '?x))) 'CxUniverse)
    (v/assert kb (list quaker nixon)     'CxUniverse)
    (v/assert kb (list republican nixon) 'CxUniverse)
    {:quaker quaker :pacifist pacifist :nixon nixon
     :pos (v/handle-of kb (list pacifist nixon)             'CxUniverse)
     :neg (v/handle-of kb (list 'not (list pacifist nixon)) 'CxUniverse)}))

(deftest brave-cautious-separates-forced-from-arbitrary
  ;; In a Nixon diamond both sides are IN and neither is forced; an ordinary `ask` cannot
  ;; tell them apart, and the brave/cautious read can — each side holds in some optimum
  ;; (brave) but not in every one (cautious).
  (when asp?
    (tu/with-neutral-kb [kb tu/fresh]
      (v/add-reasoner kb :brave-cautious)
      (let [{:keys [pacifist nixon pos neg]} (nixon-diamond kb)
            P  (list pacifist nixon)
            nP (list 'not (list pacifist nixon))]
        (testing "the engine arbitrated nothing: both sides IN, no program"
          (is (true? (v/in? kb pos)))
          (is (true? (v/in? kb neg)))
          (is (nil? (v/last-program kb))))
        (testing "each side is bravely true (in some optimum)"
          (is (v/ask? kb (list 'bravely P)  'CxUniverse))
          (is (v/ask? kb (list 'bravely nP) 'CxUniverse)))
        (testing "neither side is cautiously true (in every optimum) — the arbitrariness"
          (is (not (v/ask? kb (list 'cautiously P)  'CxUniverse)))
          (is (not (v/ask? kb (list 'cautiously nP) 'CxUniverse))))
        (testing "the read committed nothing — belief and reports are unchanged"
          (is (true? (v/in? kb pos)))
          (is (true? (v/in? kb neg)))
          (is (= 1 (count (v/contradictions kb))))
          (is (nil? (v/last-program kb))))))))

(deftest an-uncontested-fact-is-both-brave-and-cautious
  ;; A datum in no dilemma is in every optimum, so brave and cautious both reduce to
  ;; ordinary belief — the prover answers there rather than reporting nothing.
  (when asp?
    (tu/with-neutral-kb [kb tu/fresh]
      (v/add-reasoner kb :brave-cautious)
      (let [{:keys [quaker nixon]} (nixon-diamond kb)
            fact (list quaker nixon)]
        (is (v/ask? kb (list 'cautiously fact) 'CxUniverse))
        (is (v/ask? kb (list 'bravely fact)    'CxUniverse))))))

(deftest bravely-and-cautiously-are-not-assertible
  ;; A read on the dilemmas is not a fact: storing one would be a computed value with no
  ;; way to keep it current, the reason the aggregates and `unknown` are refused too.
  (tu/with-neutral-kb [kb tu/fresh]
    (doseq [f '[bravely cautiously]]
      (testing (str f " is refused as an assertion")
        (let [e (try (v/assert kb (list f (list 'some_prop 'Thing)) 'CxUniverse) nil
                     (catch clojure.lang.ExceptionInfo e e))]
          (is (some? e) (str "asserting (" f " ...) should throw"))
          (is (= :not-well-formed (:type (ex-data e))))
          (is (str/includes? (ex-message e) (str f " is not assertible"))))))))

(deftest a-brave-cautious-antecedent-derives-nothing
  ;; The prover is not a SupportingProver, so a rule resting on its answer carries no
  ;; support and the forward join drops it: a read, not something belief is built on.
  (when asp?
    (tu/with-neutral-kb [kb tu/fresh]
      (v/add-reasoner kb :brave-cautious)
      (let [{:keys [pacifist nixon]} (nixon-diamond kb)]
        (v/assert kb (list 'set/forwardRule
                           (vr/rule-sentence [(list 'bravely (list pacifist nixon))]
                                             (list 'suspected_pacifist nixon)))
                  'CxUniverse)
        (is (not (v/ask? kb (list 'suspected_pacifist nixon) 'CxUniverse)))))))

(deftest the-reader-is-opt-in
  ;; Without the reasoner registered, no prover answers a brave/cautious goal — the ASP
  ;; stack stays off a KB's path until a caller asks.
  (when asp?
    (tu/with-neutral-kb [kb tu/fresh]
      (let [{:keys [pacifist nixon]} (nixon-diamond kb)]
        (is (not (v/ask? kb (list 'bravely (list pacifist nixon)) 'CxUniverse)))))))

(deftest add-prover-registers-it-directly
  ;; `add-reasoner :brave-cautious` resolves to this constructor; `add-prover` takes the
  ;; value directly, the lower-level route the shipped reasoners are also registered by.
  (when asp?
    (tu/with-neutral-kb [kb tu/fresh]
      (v/add-prover kb (prover/brave-cautious-prover))
      (let [{:keys [pacifist nixon]} (nixon-diamond kb)]
        (is (v/ask? kb (list 'bravely    (list pacifist nixon)) 'CxUniverse))
        (is (not (v/ask? kb (list 'cautiously (list pacifist nixon)) 'CxUniverse)))))))

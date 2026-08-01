(ns vaelii.llm-correct-test
  "The type-level correction pass: a proposal that says the right thing in the wrong
  shape.  Every sentence here is verbatim model output from the eval sweep, so the
  cases are what the models actually write rather than what they might."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.llm.correct :as correct]
            [vaelii.impl.starter :as starter]
            [vaelii.test-util :as tu]))

;; the corrections read the shipped schema — argIsa constraints, declared arities, the
;; genl edges that decide what is a type — so the starter is the fixture
(use-fixtures :once (tu/loaded starter/load-into))
(use-fixtures :each (tu/neutral))

(defn- for-sentence [kb s]
  (correct/correction kb s))

(tu/deftest-kb a-unary-claim-about-a-type-becomes-a-rule
  (let [c (for-sentence kb '(mortal penguin))]
    (is (= :unary-on-type (:rule c)))
    (is (= :high (:confidence c)))
    (testing "the defeasible rule leads"
      (is (= '(set/defaultRule (implies (penguin ?x) (mortal ?x))) (:to c))))
    (testing "and the definitional genl edge is the alternative, not the default"
      ;; asymmetric risk: a defeasible claim stored definitionally cannot take an
      ;; exceptWhen, and the only repair is retracting the edge
      (is (= ['(genl penguin mortal)] (:alternatives c))))))

(tu/deftest-kb a-negated-unary-claim-is-corrected-the-same-way
  ;; this is how the shipped schema states its own worked example, so a model writing
  ;; the fact form has the right claim in the wrong shape
  (let [c (for-sentence kb '(not (flies penguin)))]
    (is (= :unary-on-type (:rule c)))
    (is (= '(set/defaultRule (implies (penguin ?x) (not (flies ?x)))) (:to c)))
    (testing "a negative claim has no genl reading, so none is offered"
      (is (empty? (:alternatives c))))))

(tu/deftest-kb a-relation-between-types-is-lifted
  (let [c (for-sentence kb '(eats penguin fish))]
    (is (= :relation-on-types (:rule c)))
    (is (= '(eatsType penguin fish) (:to c)))
    (testing "the quantified rule spells the meaning out as an alternative"
      (is (some #(= 'implies (first %)) (:alternatives c))))
    (testing "and the inertness of the lift is stated, not hidden"
      (is (re-find #"infers nothing on its own" (:why c))))))

(tu/deftest-kb an-ambiguous-argument-order-is-flagged-rather-than-guessed
  ;; partOf is physical_object x physical_object, so the argIsa constrains nothing
  ;; about direction and `(partOf penguin wing)` reads as "a penguin is part of a wing"
  (let [c (for-sentence kb '(partOf penguin wing))]
    (is (= :low (:confidence c)) "the direction cannot be inferred, so confidence drops")
    (is (= '(partOfType penguin wing) (:to c)))
    (testing "the swapped direction is offered — the same claim read the other way,
             without coining a second predicate"
      (is (some #(= '(partOfType wing penguin) %) (:alternatives c))))
    (is (re-find #"check the direction" (:why c)))))

(tu/deftest-kb a-declared-inverse-names-the-other-direction
  (let [c (for-sentence kb '(parentOf person person))]
    (when c
      (testing "childOf is declared the inverse of parentOf, so its lift is offered"
        (is (some #(= 'childOfType (first %)) (:alternatives c)))))))

(tu/deftest-kb a-repeated-argument-is-the-one-safe-arity-repair
  (let [c (for-sentence kb '(partOf penguin beak beak))]
    (is (= [:arity-surplus :relation-on-types] (:rules c))
        "the stutter is dropped, then the type-level relation it exposes is lifted")
    (is (= '(partOfType penguin beak) (:to c))
        "dropping the stutter needs no guess, but (partOf penguin beak) is still a
         relation between two type symbols — which the engine refuses outright"))
  (testing "a genuine surplus is reported with no rewrite, since which argument to drop
           is a claim about what the author meant"
    (let [c (for-sentence kb '(partOf penguin beak wing))]
      (is (= :arity-surplus (:rule c)))
      (is (nil? (:to c)))
      (is (= :low (:confidence c))))))

(tu/deftest-kb structural-vocabulary-is-left-alone
  ;; genl, disjoint, comment and argIsa talk about types by design — a type in their
  ;; arguments is correct, and rewriting it would be the bug
  (doseq [s '[(genl penguin bird)
              (disjoint penguin fish)
              (comment penguin "A flightless bird.")
              (argIsa eats 1 animal)]]
    (is (nil? (for-sentence kb s)) (str "should not correct " (pr-str s)))))

(tu/deftest-kb instance-level-content-is-left-alone
  (testing "the whole point is to correct type-level claims, not ordinary facts"
    (is (nil? (for-sentence kb '(eats Pingu SomeFish))))
    (is (nil? (for-sentence kb '(implies (parentOf ?x ?y) (ancestorOf ?x ?y)))))))

(tu/deftest-kb corrections-carry-the-line-they-came-from
  (let [entries [['(genl penguin bird) 'BiologyContext]
                 ['(mortal penguin) 'BiologyContext]
                 ['(eats penguin fish) 'BiologyContext]]
        {:keys [corrections unchanged]} (correct/corrections kb entries)]
    (is (= 2 (count corrections)))
    (is (= 1 (count unchanged)))
    (is (= [1 2] (map :index corrections)) "so a caller can point at the line")
    (is (every? #(= 'BiologyContext (:context %)) corrections))))

(tu/deftest-kb applying-a-correction-yields-a-storable-entry
  (let [c (for-sentence kb '(mortal penguin))
        c (assoc c :context 'BiologyContext)]
    (is (= ['(set/defaultRule (implies (penguin ?x) (mortal ?x))) 'BiologyContext]
           (correct/apply-correction c)))
    (testing "and an alternative is selected by index"
      (is (= ['(genl penguin mortal) 'BiologyContext]
             (correct/apply-correction c 0))))
    (testing "a report-only correction yields nothing, so it cannot be stored blind"
      (is (nil? (correct/apply-correction
                 (assoc (for-sentence kb '(partOf penguin beak wing))
                        :context 'BiologyContext)))))))

(tu/deftest-kb the-corrected-sentence-is-admissible
  ;; a correction the engine would refuse is worse than no correction
  (doseq [s '[(mortal penguin) (not (flies penguin)) (eats penguin fish)
              (partOf penguin beak beak)]]
    (let [c (for-sentence kb s)]
      (when-let [to (:to c)]
        (is (empty? (v/check kb to 'BiologyContext))
            (str (pr-str s) " -> " (pr-str to) " must be storable")))
      (doseq [alt (:alternatives c)]
        (is (empty? (v/check kb alt 'BiologyContext))
            (str (pr-str s) " alternative " (pr-str alt) " must be storable"))))))

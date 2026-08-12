;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.generator-test
  "Rule generators: a rule whose consequent is a rule, whose firing stamps that rule out
  with its holes filled (docs/generators.md).

  The scoping rule is the thing to pin, because nothing in the spelling announces it.
  A variable the generator's antecedents also mention is a **hole** — bound by the join,
  ground in the mint.  Every other variable in the stamped rule is the stamped rule's
  own and must survive as a variable, or the mint is a rule that matches one tuple
  instead of a pattern.  Half these tests are about that one distinction.

  The other half is what a mint *is*: derived content, justified by the firing, so it
  leaves the way any conclusion leaves.  That only works because both chainers ask
  belief of a rule before using it, so `a-defeated-generator-stops-stamping` and
  `retracting-the-fill-retracts-the-rule` are as much tests of `res/rule-believed?` as
  of the generator."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.rules :as vr]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- rule-sentexes
  "The stored rules in `ctx`, as sentexes — a rule is the sentex with an `:antecedent`."
  [kb ctx]
  (filter :antecedent (v/sentexes-in-context kb ctx)))

(defn- stamped
  "The rules in `ctx` that a generator minted — every stored rule but the generators."
  [kb ctx]
  (remove vr/generator-sentex? (rule-sentexes kb ctx)))

;; ---- the shape works ------------------------------------------------------

(tu/deftest-kb a-generator-stamps-one-rule-per-firing
  (tu/with-terms [planVerb outcomeEmotion planOf feels succeededAt failedAt Joy Regret]
    (v/assert kb (list 'implies
                       (list 'and (list planVerb '?outcome)
                             (list outcomeEmotion '?outcome '?emotion))
                       (list 'implies
                             (list 'and (list planOf '?a '?p) (list '?outcome '?a '?p))
                             (list feels '?a '?emotion)))
              'UniverseContext)
    (v/assert kb (list planVerb succeededAt) 'UniverseContext)
    (v/assert kb (list planVerb failedAt) 'UniverseContext)
    (v/assert kb (list outcomeEmotion succeededAt Joy) 'UniverseContext)
    (v/assert kb (list outcomeEmotion failedAt Regret) 'UniverseContext)
    (testing "one stamped rule per fill, and no more"
      (is (= 2 (count (stamped kb 'UniverseContext)))))
    (testing "the hole is ground in the mint and the stamped rule keeps its own variables"
      (let [s (:sentence (first (filter #(some #{succeededAt}
                                               (vr/antecedent-predicates (:sentence %)))
                                        (stamped kb 'UniverseContext))))]
        (is (some? s) "a rule was stamped for succeededAt")
        ;; the stamped rule's own `?a` / `?p` survive as variables — canonically
        ;; renumbered, but variables
        (is (every? #(re-matches #"\?var\d+" (str %))
                    (filter #(and (symbol? %) (.startsWith (str %) "?"))
                            (tree-seq sequential? seq s)))
            "no stamped variable was frozen into a constant")))))

(tu/deftest-kb a-stamped-rule-draws-conclusions
  (tu/with-terms [planVerb outcomeEmotion planOf feels succeededAt Joy Tom Plan]
    (v/assert kb (list 'implies
                       (list 'and (list planVerb '?outcome)
                             (list outcomeEmotion '?outcome '?emotion))
                       (list 'implies
                             (list 'and (list planOf '?a '?p) (list '?outcome '?a '?p))
                             (list feels '?a '?emotion)))
              'UniverseContext)
    (v/assert kb (list planVerb succeededAt) 'UniverseContext)
    (v/assert kb (list outcomeEmotion succeededAt Joy) 'UniverseContext)
    (v/assert kb (list planOf Tom Plan) 'UniverseContext)
    (v/assert kb (list succeededAt Tom Plan) 'UniverseContext)
    (is (= #{Joy} (into #{} (map '?e) (v/ask kb (list feels Tom '?e) 'UniverseContext))))))

(tu/deftest-kb both-arrival-orders-agree
  ;; order independence, the first invariant: whether the generator or the facts it
  ;; ranges over arrive first cannot change what the KB believes.  A generator needs no
  ;; retroactive sweep of its own for this — it is an ordinary rule, and a newly
  ;; asserted rule is a datum that joins over what is already stored.
  ;;
  ;; Two disjoint term sets in the one KB rather than two KBs: the temporaries are
  ;; gensym'd, so neither order can see the other's vocabulary.
  (let [run (fn [generator-first?]
              (tu/with-terms [marker pairing subject feels src Joy Tom Plan]
                (let [gen   #(v/assert kb (list 'implies
                                                (list 'and (list marker '?o)
                                                      (list pairing '?o '?e))
                                                (list 'implies
                                                      (list 'and (list subject '?a '?p)
                                                            (list '?o '?a '?p))
                                                      (list feels '?a '?e)))
                                       'UniverseContext)
                      facts #(do (v/assert kb (list marker src) 'UniverseContext)
                                 (v/assert kb (list pairing src Joy) 'UniverseContext)
                                 (v/assert kb (list subject Tom Plan) 'UniverseContext)
                                 (v/assert kb (list src Tom Plan) 'UniverseContext))]
                  (if generator-first? (do (gen) (facts)) (do (facts) (gen)))
                  {:derived (into #{} (map '?e) (v/ask kb (list feels Tom '?e)
                                                       'UniverseContext))
                   :joy     Joy})))
        a   (run true)
        b   (run false)]
    (is (= #{(:joy a)} (:derived a)) "generator first derives the conclusion")
    (is (= #{(:joy b)} (:derived b)) "facts first derives it too")))

(tu/deftest-kb the-wrapper-on-the-stamped-rule-sets-its-direction
  ;; the answer to "how do I say the generated rule is a default / backward one": the
  ;; wrapper rides inside the consequent, where substitution never touches it
  (tu/with-terms [marker src dst thing]
    (v/assert kb (list 'implies (list marker '?p)
                       (list 'set/defaultRule
                             (list 'implies (list '?p '?x) (list dst '?x))))
              'UniverseContext)
    (v/assert kb (list marker src) 'UniverseContext)
    (let [minted (first (stamped kb 'UniverseContext))]
      (is (some? minted) "a rule was stamped")
      (is (:defeasible minted) "the stamped rule carries the defaultRule the template set")
      (is (= :both (:direction minted))))))

;; ---- a mint is derived content -------------------------------------------

(tu/deftest-kb retracting-the-fill-retracts-the-rule
  (tu/with-terms [marker src dst Fido]
    (v/assert kb (list 'implies (list marker '?p)
                       (list 'implies (list '?p '?x) (list dst '?x)))
              'UniverseContext)
    (let [fill (v/assert kb (list marker src) 'UniverseContext)]
      (v/assert kb (list src Fido) 'UniverseContext)
      (testing "the stamped rule fired"
        (is (seq (v/sentexes-matching kb (list dst Fido) 'UniverseContext))))
      (let [minted (:id (first (stamped kb 'UniverseContext)))]
        (is (some? minted))
        (v/retract! kb fill)
        (testing "the mint is no longer believed"
          (is (not (v/in? kb minted))))
        (testing "and neither is what it concluded"
          (is (empty? (v/sentexes-matching kb (list dst Fido) 'UniverseContext))))))))

(tu/deftest-kb a-disbelieved-rule-does-not-fire
  ;; the belief filter on its own, with no generator in sight: this is the property
  ;; `res/rule-believed?` adds, and a mint is only retractable because it holds
  (tu/with-terms [marker src dst Fido Rex]
    (v/assert kb (list 'implies (list marker '?p)
                       (list 'implies (list '?p '?x) (list dst '?x)))
              'UniverseContext)
    (let [fill (v/assert kb (list marker src) 'UniverseContext)]
      (v/assert kb (list src Fido) 'UniverseContext)
      (v/retract! kb fill)
      (testing "a fact arriving after the mint lost its support draws nothing"
        (v/assert kb (list src Rex) 'UniverseContext)
        (v/forward-chain kb)
        (is (empty? (v/sentexes-matching kb (list dst Rex) 'UniverseContext)))))))

(tu/deftest-kb one-rule-stamped-two-ways-is-one-handle
  ;; dedup is the ordinary sentex dedup, so it costs nothing: two fills that substitute
  ;; to the same rule share a handle and collect a justification each
  (tu/with-terms [markerA markerB src dst]
    (doseq [m [markerA markerB]]
      (v/assert kb (list 'implies (list m '?p)
                         (list 'implies (list '?p '?x) (list dst '?x)))
                'UniverseContext))
    (v/assert kb (list markerA src) 'UniverseContext)
    (v/assert kb (list markerB src) 'UniverseContext)
    (is (= 1 (count (stamped kb 'UniverseContext)))
        "the two generators stamped one rule, not two")
    (let [h (:id (first (stamped kb 'UniverseContext)))]
      (is (<= 2 (count (v/supporting-justifications kb h)))
          "and it rests on both firings"))))

;; ---- what is refused ------------------------------------------------------

(defn- refusal
  "The `:type` `assert` throws for `sentence`, or `:accepted`."
  [kb sentence]
  (try (v/assert kb sentence 'UniverseContext) :accepted
       (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))

(tu/deftest-kb a-generated-rule-cannot-itself-generate
  (tu/with-terms [aa bb cc dd]
    (is (= :not-well-formed
           (refusal kb (list 'implies (list aa '?x)
                             (list 'implies (list bb '?x)
                                   (list 'implies (list cc '?x) (list dd '?x)))))))))

(tu/deftest-kb a-generator-is-forward-only
  (tu/with-terms [marker dst]
    (is (= :not-indexable
           (refusal kb (list 'set/backwardRule
                             (list 'implies (list marker '?p)
                                   (list 'implies (list '?p '?x) (list dst '?x)))))))))

(tu/deftest-kb a-generator-sharing-no-variable-is-refused
  ;; it would stamp the same rule at every firing, which is a rule the author could
  ;; have written
  (tu/with-terms [marker src dst]
    (is (= :not-range-restricted
           (refusal kb (list 'implies (list marker '?p)
                             (list 'implies (list src '?x) (list dst '?x))))))))

(tu/deftest-kb the-stamped-rule-owes-its-own-range-restriction
  (tu/with-terms [marker dst]
    (is (= :not-range-restricted
           (refusal kb (list 'implies (list marker '?p)
                             (list 'implies (list '?p '?x) (list dst '?x '?loose))))))))

(tu/deftest-kb a-hole-may-stand-in-functor-position-but-a-non-hole-may-not
  (tu/with-terms [marker dst]
    (testing "a hole in functor position is what a generator is for"
      (is (= :accepted
             (refusal kb (list 'implies (list marker '?p)
                               (list 'implies (list '?p '?x) (list dst '?x)))))))
    (testing "a variable functor beside the hole binds to nothing, so it is unindexable"
      ;; `?p` is a hole and fine; `?q` is not and never will be, so every mint this
      ;; generator could produce is a rule the index cannot key
      (is (= :not-indexable
             (refusal kb (list 'implies (list marker '?p)
                               (list 'implies (list 'and (list '?p '?x) (list '?q '?x))
                                     (list dst '?x)))))))
    (testing "and with no hole at all the sharper complaint comes first"
      (is (= :not-range-restricted
             (refusal kb (list 'implies (list marker '?p)
                               (list 'implies (list '?q '?x) (list dst '?x)))))))))

(tu/deftest-kb an-exceptWhen-on-the-stamped-rule-is-refused
  ;; it would be dropped in silence — a firing has no way to split an exception into
  ;; the meta-sentex that carries it — and a guard that vanishes is worse than one
  ;; refused
  (tu/with-terms [marker src dst blocked Fido]
    (is (= :not-well-formed
           (refusal kb (list 'implies (list marker '?p)
                             (list 'exceptWhen (list blocked '?x)
                                   (list 'implies (list '?p '?x) (list dst '?x)))))))
    (testing "but an exceptWhen on the generator says when not to generate, and holds"
      (is (= :accepted
             (refusal kb (list 'exceptWhen (list blocked '?p)
                               (list 'implies (list marker '?p)
                                     (list 'implies (list '?p '?x) (list dst '?x)))))))
      (v/assert kb (list blocked src) 'UniverseContext)
      (v/assert kb (list marker src) 'UniverseContext)
      (is (empty? (stamped kb 'UniverseContext))
          "the blocked fill stamped nothing")
      (v/assert kb (list src Fido) 'UniverseContext)
      (is (empty? (v/sentexes-matching kb (list dst Fido) 'UniverseContext))))))

(tu/deftest-kb a-stamped-existential-head-skolemizes-when-the-stamped-rule-fires
  ;; the generator's firing must NOT skolemize — the stamped rule's variables are its
  ;; own — but an `exists` the author marked inside the stamped rule still means what it
  ;; means, one firing later and against the stamped rule's own handle
  (tu/with-terms [marker src linked Fido]
    (v/assert kb (list 'implies (list marker '?p)
                       (list 'implies (list '?p '?x)
                             (list 'exists '?y (list linked '?x '?y))))
              'UniverseContext)
    (v/assert kb (list marker src) 'UniverseContext)
    (is (= 1 (count (stamped kb 'UniverseContext))))
    (v/assert kb (list src Fido) 'UniverseContext)
    (is (seq (v/sentexes-matching kb (list linked Fido '?y) 'UniverseContext))
        "the stamped rule minted its witness")))

(tu/deftest-kb a-generator-cycle-is-refused
  (tu/with-terms [mm nn kk pp qq]
    (testing "one generator stamping what another reads"
      (is (= :accepted
             (refusal kb (list 'implies (list mm '?o)
                               (list 'implies (list '?o '?a) (list kk '?a))))))
      (is (= :not-stratified
             (refusal kb (list 'implies (list 'and (list kk '?o) (list nn '?o))
                               (list 'implies (list '?o '?a) (list pp '?a)))))))
    (testing "and a generator that feeds itself"
      (is (= :not-stratified
             (refusal kb (list 'implies (list qq '?o)
                               (list 'implies (list '?o '?a) (list qq '?a)))))))))

(tu/deftest-kb the-cycle-check-sees-a-wrapped-generator-too
  ;; every generator is filed under the one key `implies`, which means peeling the
  ;; wrapper off the stamped rule first — it is the stamped rule's, not the
  ;; generator's.  Without the peel this generator files under `set/defaultRule`, the
  ;; roster misses it, and the cycle below is admitted.
  (tu/with-terms [mm nn kk pp]
    (is (= :accepted
           (refusal kb (list 'implies (list mm '?o)
                             (list 'set/defaultRule
                                   (list 'implies (list '?o '?a) (list kk '?a)))))))
    (is (= :not-stratified
           (refusal kb (list 'implies (list 'and (list kk '?o) (list nn '?o))
                             (list 'implies (list '?o '?a) (list pp '?a))))))))

(tu/deftest-kb check-predicts-assert-on-every-generator-refusal
  ;; the repo's contract, and it matters most at the one door that writes two records:
  ;; an editor validating a generator must be told what the firing would refuse
  (tu/with-terms [marker dst aa bb cc dd]
    (doseq [[label sentence]
            [["depth 2"      (list 'implies (list aa '?x)
                                   (list 'implies (list bb '?x)
                                         (list 'implies (list cc '?x) (list dd '?x))))]
             ["backward"     (list 'set/backwardRule
                                   (list 'implies (list marker '?p)
                                         (list 'implies (list '?p '?x) (list dst '?x))))]
             ["loose var"    (list 'implies (list marker '?p)
                                   (list 'implies (list '?p '?x) (list dst '?x '?loose)))]]]
      (testing label
        (let [predicted (v/check kb sentence 'UniverseContext)
              thrown    (refusal kb sentence)]
          (is (seq predicted) "check reports a problem")
          (is (= thrown (:type (first predicted)))
              "and it is the one assert throws"))))))

;; ---- the mint goes through the same door ---------------------------------

(tu/deftest-kb a-mint-that-cannot-stand-is-dropped-and-recorded
  ;; a fill can put a name in functor position that the index cannot key.  The firing
  ;; must not throw — a fixpoint may not abort halfway through itself — so the mint is
  ;; dropped and lands in the violation ledger instead.
  (tu/with-terms [marker dst]
    (v/assert kb (list 'implies (list marker '?p)
                       (list 'implies (list '?p '?x) (list dst '?x)))
              'UniverseContext)
    (v/clear-violations! kb)
    ;; a fill that is a *number* heads a literal no index can key
    (v/assert kb (list marker 7) 'UniverseContext)
    (testing "nothing was stored for it"
      (is (empty? (stamped kb 'UniverseContext))))
    (testing "and the drop is readable"
      (is (seq (v/violations kb))))))

(tu/deftest-kb a-stamped-conjunctive-consequent-is-polycanonicalized
  ;; the same split an asserted rule gets: one rule per conjunct, each keyed by its own
  ;; consequent predicate, or `rules-by-consequent` could not answer for either
  (tu/with-terms [marker src dstA dstB]
    (v/assert kb (list 'implies (list marker '?p)
                       (list 'implies (list '?p '?x)
                             (list 'and (list dstA '?x) (list dstB '?x))))
              'UniverseContext)
    (v/assert kb (list marker src) 'UniverseContext)
    (is (= 2 (count (stamped kb 'UniverseContext)))
        "one stamped rule per conjunct")
    (is (= #{dstA dstB}
           (into #{} (map #(vr/consequent-predicate (:sentence %)))
                 (stamped kb 'UniverseContext))))))

(tu/deftest-kb a-mint-is-reachable-by-the-index-both-ways
  ;; the whole point of minting rather than interpreting: what gets stored is an
  ;; ordinary rule, so it is keyed by concrete predicates and both engines find it
  (tu/with-terms [marker src dst Fido]
    (v/assert kb (list 'implies (list marker '?p)
                       (list 'implies (list '?p '?x) (list dst '?x)))
              'UniverseContext)
    (v/assert kb (list marker src) 'UniverseContext)
    (let [h (:id (first (stamped kb 'UniverseContext)))]
      (testing "posted under the stamped antecedent, not under a variable"
        (is (contains? (set (p/rules-by-antecedent (:index kb) src)) h)))
      (testing "and under the stamped consequent"
        (is (contains? (set (p/rules-by-consequent (:index kb) dst)) h))))
    (testing "so a backward goal reaches it too"
      (v/assert kb (list src Fido) 'UniverseContext)
      (is (v/provable? kb (list dst Fido) 'UniverseContext)))))

(tu/deftest-kb asserting-a-stamped-rule-gives-it-a-ground-of-its-own
  ;; A stamped rule is a *conclusion*: it rests on the generator's justification and
  ;; goes when the generator does.  Asserting the same rule is a second and independent
  ;; ground for it, and the rule door marks the premise for it as the fact door does —
  ;; so the rule outlives the generator that first stamped it, and carries the class
  ;; the assertion stated rather than none.
  (tu/with-terms [marker src dst Fido]
    (let [gh (v/assert kb (list 'implies (list marker '?p)
                                (list 'implies (list '?p '?x) (list dst '?x)))
                       'UniverseContext)]
      (v/assert kb (list marker src) 'UniverseContext)
      (let [sx (first (stamped kb 'UniverseContext))]
        (is (some? sx) "the generator stamped a rule")
        (is (false? (v/premise? kb (:id sx))) "a conclusion, resting on the generator")
        (let [h (v/assert kb (:sentence sx) 'UniverseContext {:strength :monotonic})]
          (is (= (:id sx) h) "one rule, one handle — the assertion is not a second sentex")
          (is (true? (v/premise? kb h)) "and now a premise in its own right")
          (is (= :monotonic (:strength (v/sentex kb h)))))
        (testing "so retracting the generator leaves the asserted rule standing"
          (v/retract! kb gh)
          (is (v/in? kb (:id sx)))
          (v/assert kb (list src Fido) 'UniverseContext)
          (is (seq (v/sentexes-matching kb (list dst Fido) 'UniverseContext))
              "and still firing"))))))

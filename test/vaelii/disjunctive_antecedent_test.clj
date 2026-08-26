;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.disjunctive-antecedent-test
  "`or` in a rule antecedent: a pet is fed if it is a dog **or** a cat.

  The claim every test here holds is the one
  [docs/canonicalization.md](../../docs/canonicalization.md) makes — the connective
  **disappears**.  `(implies (or A B) C)` is stored as the two rules `(implies A C)` and
  `(implies B C)` (`rules/expand-rule`), and from there down there is no disjunction
  left: each alternative is an ordinary rule sentex with its own handle, its own
  justifications and its own retraction, it dedups against an individually asserted
  twin, and `why` names the one that actually fired.

  So the tests split in two.  The first half asserts that the expansion is **invisible**
  — the same beliefs, the same retraction behaviour and the same handles a hand-written
  pair of rules would give.  The second half asserts the positions from which the
  connective cannot disappear are **refused**, each naming the rewrite that is
  expressible: a conclusion (a choice, so `set/assumptionRule` and a solve), a closed
  query body, an `exceptWhen` query, and a width past which expanding is the wrong
  storage.

  House rules as everywhere else: gensym'd temporaries via `tu/with-terms`, engine
  vocabulary (`or`, `implies`, `set/defaultRule`, `exceptWhen`, contexts) literal, and
  the neutral fixture asserts the KB is restored."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- fed-if-dog-or-cat
  "The rule the file is named for, as the author writes it."
  [dog cat fed]
  (list 'implies (list 'or (list dog '?p) (list cat '?p)) (list fed '?p)))

(defn- problem-of
  "The refusal `assert` throws for `sentence`, as `[type message]` — or `:accepted`."
  [kb sentence context]
  (try (v/assert kb sentence context) :accepted
       (catch clojure.lang.ExceptionInfo e
         [(:type (ex-data e)) (.getMessage e)])))

;; ---- 1. both disjuncts fire ---------------------------------------------
;; DECISION: `(implies (or A B) C)` is stored as one rule per alternative, so a datum
;; satisfying *either* alternative reaches the conclusion.  A single stored rule reading
;; the `or` as a literal on a predicate named `or` — which is what the engine did before
;; the expansion existed — satisfies neither and is the failure this pins.

(tu/deftest-kb a-pet-is-fed-if-it-is-a-dog-or-a-cat
  (tu/with-terms [dog cat fed Muffet Tibbles Gerald CxPets]
    (let [hs (v/assert kb (fed-if-dog-or-cat dog cat fed) CxPets)]
      (testing "one written rule, two stored rules, and the vector says so"
        (is (vector? hs))
        (is (= 2 (count hs)))
        (is (= 2 (count (distinct hs)))))
      (v/assert kb (list dog Muffet)  CxPets)
      (v/assert kb (list cat Tibbles) CxPets)
      (v/assert kb (list dog Gerald)  CxPets)
      (testing "the dog disjunct fires"
        (is (v/ask? kb (list fed Muffet) CxPets)))
      (testing "the cat disjunct fires"
        (is (v/ask? kb (list fed Tibbles) CxPets)))
      (testing "and nothing else does"
        (is (not (v/ask? kb (list fed Tibbles) 'CxUniverse)))))))

;; ---- 2. one alternative's fact retracted leaves the other's conclusion ---
;; DECISION: each alternative is an ordinary rule with its own justifications, so the
;; TMS sweeps exactly the conclusions that rested on the retracted datum.  A rule stored
;; once with both alternatives folded together would have one justification per
;; conclusion regardless of which alternative supported it.

(tu/deftest-kb retracting-the-fact-behind-one-disjunct-leaves-the-other-conclusion
  (tu/with-terms [dog cat fed Muffet Tibbles CxPets]
    (v/assert kb (fed-if-dog-or-cat dog cat fed) CxPets)
    (v/assert kb (list dog Muffet)  CxPets)
    (v/assert kb (list cat Tibbles) CxPets)
    (v/retract! kb (v/handle-of kb (list dog Muffet) CxPets))
    (testing "the conclusion that rested on the retracted datum is gone"
      (is (not (v/ask? kb (list fed Muffet) CxPets))))
    (testing "the other alternative's conclusion stands"
      (is (v/ask? kb (list fed Tibbles) CxPets)))))

;; ---- 3. retracting the rule sweeps every conclusion ----------------------
;; DECISION: the vector `assert` returns is the author's record of the whole rule.
;; Retracting **one** handle retracts that alternative and only that one; retracting
;; every handle is what retracts the rule the author wrote.

(tu/deftest-kb retracting-one-handle-retracts-one-alternative-and-all-of-them-the-rule
  (tu/with-terms [dog cat fed Muffet Tibbles CxPets]
    (let [hs (v/assert kb (fed-if-dog-or-cat dog cat fed) CxPets)]
      (v/assert kb (list dog Muffet)  CxPets)
      (v/assert kb (list cat Tibbles) CxPets)
      (v/retract! kb (first hs))
      (testing "one handle retracted sweeps that alternative's conclusions only"
        (is (= #{false true}
               #{(v/ask? kb (list fed Muffet) CxPets)
                 (v/ask? kb (list fed Tibbles) CxPets)})))
      (v/retract! kb (second hs))
      (testing "every handle retracted sweeps them all"
        (is (not (v/ask? kb (list fed Muffet) CxPets)))
        (is (not (v/ask? kb (list fed Tibbles) CxPets)))))))

;; ---- 4. an equivalent single rule dedups to one of the handles -----------
;; DECISION: an expanded rule is not a private copy — it is the rule, canonicalized on
;; its own, so an author who writes one of the alternatives out afterwards finds the
;; stored one and joins its slots exactly as any re-assert does.  Were it otherwise the
;; KB would hold two rules concluding the same thing from the same antecedent, and
;; retracting the one the author remembers writing would leave the other firing.

(tu/deftest-kb an-individually-asserted-twin-dedups-to-the-expanded-rule
  (tu/with-terms [dog cat fed CxPets]
    (let [hs   (v/assert kb (fed-if-dog-or-cat dog cat fed) CxPets)
          twin (v/assert kb (list 'implies (list dog '?d) (list fed '?d)) CxPets)]
      (testing "the twin is one of the handles the disjunctive rule already stored"
        (is (integer? twin))
        (is (contains? (set hs) twin)))
      (testing "and no third rule was created — the two handles are still the two"
        (is (= (set hs)
               #{(v/handle-of kb (list 'implies (list dog '?x) (list fed '?x)) CxPets)
                 (v/handle-of kb (list 'implies (list cat '?x) (list fed '?x)) CxPets)}))))))

;; ---- 5. order independence ----------------------------------------------
;; DECISION: "The same knowledge in any order yields the same beliefs"
;; (docs/nmtms.md).  Two orders are at stake here and both are pinned: the facts before
;; or after the rule, and the *disjuncts* written either way round.  The second is the
;; one the expansion could get wrong on its own — a disjunct order that reached the
;; canonicalizer would give two spellings two pairs of handles.

(tu/deftest-kb the-disjuncts-canonicalize-to-the-same-two-handles-in-either-order
  (tu/with-terms [dog cat fed Muffet Tibbles CxPets]
    (let [forward  (v/assert kb (fed-if-dog-or-cat dog cat fed) CxPets)
          backward (v/assert kb (list 'implies
                                      (list 'or (list cat '?q) (list dog '?q))
                                      (list fed '?q))
                             CxPets)]
      (testing "the reversed spelling is the same two rules"
        (is (= (set forward) (set backward))))
      (testing "and the facts reach the same beliefs asserted after the rule"
        (v/assert kb (list dog Muffet)  CxPets)
        (v/assert kb (list cat Tibbles) CxPets)
        (is (v/ask? kb (list fed Muffet)  CxPets))
        (is (v/ask? kb (list fed Tibbles) CxPets))))))

(tu/deftest-kb the-facts-may-arrive-before-the-rule
  (tu/with-terms [dog cat fed Muffet Tibbles CxPets]
    (v/assert kb (list dog Muffet)  CxPets)
    (v/assert kb (list cat Tibbles) CxPets)
    (v/assert kb (fed-if-dog-or-cat dog cat fed) CxPets)
    (testing "a rule asserted after its data joins over what is already stored"
      (is (v/ask? kb (list fed Muffet)  CxPets))
      (is (v/ask? kb (list fed Tibbles) CxPets)))))

;; ---- 6. why names the alternative that fired ----------------------------
;; DECISION: the expansion is what is stored, so it is what the justification names.
;; An explanation quoting the disjunctive rule as written would be quoting a sentence no
;; handle holds, and the reader could not retract what it named.

(tu/deftest-kb why-shows-the-expanded-rule-that-fired
  (tu/with-terms [dog cat fed Muffet CxPets]
    (v/assert kb (fed-if-dog-or-cat dog cat fed) CxPets)
    (v/assert kb (list dog Muffet) CxPets)
    (let [tree  (v/why kb (v/handle-of kb (list fed Muffet) CxPets))
          rules (into #{} (map :rule) (:support tree))]
      (testing "the rule named is the dog alternative, with no or left in it"
        (is (= #{(list 'implies (list dog '?p) (list fed '?p))} rules)))
      (testing "and the datum it rests on is the dog fact"
        (is (= [(list dog Muffet)]
               (mapv :sentence (:because (first (:support tree))))))))))

;; ---- 7. an exceptWhen excepts every alternative --------------------------
;; DECISION: "The exception belongs on the rule it excepts" (docs/exceptions.md), and
;; the exception is a meta-sentex keyed by **rule handle** — so a rule stored as several
;; owes one exception meta-sentex per handle, aligned to that alternative's own varmap.
;; One shared meta would except whichever alternative happened to be stored first.

(tu/deftest-kb an-exception-on-a-disjunctive-default-rule-blocks-both-branches
  (tu/with-terms [dog cat fed sick Muffet Tibbles Gerald CxPets]
    (let [metas (v/assert kb (list 'exceptWhen (list sick '?p)
                                   (list 'set/defaultRule
                                         (fed-if-dog-or-cat dog cat fed)))
                          CxPets)]
      (testing "one exception meta-sentex per alternative"
        (is (vector? metas))
        (is (= 2 (count (distinct metas)))))
      (v/assert kb (list dog Muffet)  CxPets)
      (v/assert kb (list cat Tibbles) CxPets)
      (v/assert kb (list dog Gerald)  CxPets)
      (v/assert kb (list sick Muffet)  CxPets)
      (v/assert kb (list sick Tibbles) CxPets)
      (testing "the dog branch is excepted"
        (is (not (v/ask? kb (list fed Muffet) CxPets))))
      (testing "the cat branch is excepted too"
        (is (not (v/ask? kb (list fed Tibbles) CxPets))))
      (testing "and the unexcepted binding still concludes, so nothing passed vacuously"
        (is (v/ask? kb (list fed Gerald) CxPets))))))

;; ---- 8. the width cap ----------------------------------------------------
;; DECISION: the width is paid in handles, index entries and TMS nodes rather than at
;; query time, and nested disjuncts multiply — so a rule that reads like one line can
;; cost thousands.  Sixteen alternatives is the cap, and the refusal names the count so
;; the author can see how far over the line the typo put them.

(tu/deftest-kb a-rule-over-the-alternative-cap-is-refused-with-its-count
  (tu/with-terms [a b c d e f g h i j fed CxPets]
    (let [pair (fn [x y] (list 'or (list x '?p) (list y '?p)))
          wide (list 'implies
                     (list 'and (pair a b) (pair c d) (pair e f) (pair g h) (pair i j))
                     (list fed '?p))
          [ty msg] (problem-of kb wide CxPets)]
      (testing "refused under its own type"
        (is (= :disjunction-too-wide ty)))
      (testing "and the message names the count and the cap"
        (is (re-find #"expands to 32" msg))
        (is (re-find #"cap of 16" msg))))
    (testing "sixteen alternatives is under the cap and stores sixteen rules"
      (let [pair (fn [x y] (list 'or (list x '?p) (list y '?p)))
            ok   (list 'implies
                       (list 'and (pair a b) (pair c d) (pair e f) (pair g h))
                       (list fed '?p))]
        (is (= 16 (count (v/assert kb ok CxPets))))))))

;; ---- 9. a disjunctive conclusion is a choice, not a derivation -----------
;; DECISION: forward chaining places a sentex, not a choice — belief is a label on one
;; stored sentence rather than on a set of them.  What the engine *does* have is the
;; choice itself, so the refusal points at `set/assumptionRule` and a solve rather than
;; leaving the author to guess there is no answer.

(tu/deftest-kb or-in-a-consequent-is-refused-pointing-at-assumptionRule
  (tu/with-terms [dog fed watered CxPets]
    (let [[ty msg] (problem-of kb (list 'implies (list dog '?p)
                                        (list 'or (list fed '?p) (list watered '?p)))
                               CxPets)]
      (is (= :not-well-formed ty))
      (testing "the message names the home a disjunctive head has"
        (is (re-find #"set/assumptionRule" msg))
        (is (re-find #"docs/solving\.md" msg))))
    (testing "and a bare disjunction is not one assertable sentence either"
      (let [[ty msg] (problem-of kb (list 'or (list dog 'Rex) (list fed 'Rex)) CxPets)]
        (is (= :not-well-formed ty))
        (is (re-find #"set/assumptionRule" msg))))
    (testing "`check` predicts both without storing anything"
      (is (= [:not-well-formed]
             (mapv :type (v/check kb (list 'implies (list dog '?p)
                                           (list 'or (list fed '?p) (list watered '?p)))
                                  CxPets)))))))

;; ---- 10. range restriction is asked per alternative ---------------------
;; DECISION: the flat read passes — `?p` *is* somewhere in the antecedents — and then
;; one of the two rules the author wrote concludes about a variable nothing binds.  So
;; the check runs per alternative, and refuses the **whole** rule naming the disjunct
;; the bad alternative took, since half a rule is not what anybody wrote.

(tu/deftest-kb a-disjunct-that-does-not-bind-the-consequent-is-refused-by-name
  (tu/with-terms [dog cat fed CxPets]
    (let [[ty msg] (problem-of kb (list 'implies
                                        (list 'or (list dog '?p) (list cat '?q))
                                        (list fed '?p))
                               CxPets)]
      (is (= :not-range-restricted ty))
      (testing "the message names the unbound variable and the disjunct that took it"
        (is (re-find #"consequent variable \?p" msg))
        (is (re-find (re-pattern (str "\\(" (name cat) " \\?q\\)")) msg))))
    (testing "and nothing was stored — the whole rule is refused, not half of it"
      (is (empty? (v/sentexes-matching kb (list 'implies (list dog '?x) (list fed '?x))
                                       CxPets))))))

;; ---- 11. distribution, and the product with a conjunctive consequent -----
;; DECISION: the two polycanonicalizations compose.  `(implies (and (or A B) D) C)`
;; distributes to two rules, and a rule that disjoins its antecedent *and* conjoins its
;; consequent stores the product.

(tu/deftest-kb a-disjunct-beside-a-conjunct-distributes
  (tu/with-terms [dog cat hungry fed Muffet Tibbles Gerald CxPets]
    (v/assert kb (list 'implies
                       (list 'and (list 'or (list dog '?p) (list cat '?p))
                             (list hungry '?p))
                       (list fed '?p))
              CxPets)
    (v/assert kb (list dog Muffet)     CxPets)
    (v/assert kb (list hungry Muffet)  CxPets)
    (v/assert kb (list cat Tibbles)    CxPets)
    (v/assert kb (list hungry Tibbles) CxPets)
    (v/assert kb (list dog Gerald)     CxPets)
    (testing "each alternative keeps the conjunct beside it"
      (is (v/ask? kb (list fed Muffet)  CxPets))
      (is (v/ask? kb (list fed Tibbles) CxPets)))
    (testing "and the conjunct is still required"
      (is (not (v/ask? kb (list fed Gerald) CxPets))))))

(tu/deftest-kb a-disjunctive-antecedent-and-a-conjunctive-consequent-store-the-product
  (tu/with-terms [dog cat fed happy Muffet CxPets]
    (let [hs (v/assert kb (list 'implies
                                (list 'or (list dog '?p) (list cat '?p))
                                (list 'and (list fed '?p) (list happy '?p)))
                       CxPets)]
      (testing "two alternatives times two conjuncts is four rules"
        (is (= 4 (count (distinct hs)))))
      (v/assert kb (list dog Muffet) CxPets)
      (is (v/ask? kb (list fed Muffet)   CxPets))
      (is (v/ask? kb (list happy Muffet) CxPets)))))

(tu/deftest-kb an-or-with-one-disjunct-is-the-disjunct
  (tu/with-terms [dog fed Muffet CxPets]
    (let [h (v/assert kb (list 'implies (list 'or (list dog '?p)) (list fed '?p)) CxPets)]
      (testing "one alternative is one rule, and the handle is not wrapped in a vector"
        (is (integer? h)))
      (testing "and it is the same rule the bare spelling stores"
        (is (= h (v/assert kb (list 'implies (list dog '?p) (list fed '?p)) CxPets))))
      (v/assert kb (list dog Muffet) CxPets)
      (is (v/ask? kb (list fed Muffet) CxPets)))))

(tu/deftest-kb an-empty-or-is-refused
  (tu/with-terms [fed CxPets]
    (let [[ty msg] (problem-of kb (list 'implies (list 'or) (list fed '?p)) CxPets)]
      (is (= :not-well-formed ty))
      (is (re-find #"at least one alternative" msg)))))

;; ---- 12. the positions a closed query body cannot union -----------------
;; DECISION: `unknown`, `thereExists` and the aggregates are each answered as **one**
;; closed level-6 query, and nothing there unions two runs — so an `or` under one of
;; them would decide the rule without being evaluated, which is the one way a guard
;; passes everything silently.  Each refusal names the rewrite that is expressible.

(tu/deftest-kb or-inside-a-closed-query-body-is-refused-with-its-rewrite
  (tu/with-terms [dog cat fed CxPets]
    (testing "unknown — De Morgan gives two antecedents"
      (let [[ty msg] (problem-of kb (list 'implies
                                          (list 'unknown (list 'or (list dog '?p)
                                                               (list cat '?p)))
                                          (list fed '?p))
                                 CxPets)]
        (is (= :not-well-formed ty))
        (is (re-find #"neither A nor B is derivable" msg))))
    (testing "not — the same rewrite one frame out"
      (let [[ty msg] (problem-of kb (list 'implies
                                          (list 'and (list dog '?p)
                                                (list 'not (list 'or (list cat '?p)
                                                                 (list dog '?p))))
                                          (list fed '?p))
                                 CxPets)]
        (is (= :not-well-formed ty))
        (is (re-find #"or cannot stand under not" msg))))
    (testing "an exceptWhen query — one exceptWhen per alternative, block-if-any"
      (let [[ty msg] (problem-of kb (list 'exceptWhen
                                          (list 'or (list dog '?p) (list cat '?p))
                                          (list 'implies (list dog '?p) (list fed '?p)))
                                 CxPets)]
        (is (= :not-well-formed ty))
        (is (re-find #"one exceptWhen per alternative" msg))))))

;; ---- 13. a goal is refused rather than expanded -------------------------
;; DECISION: a rule is expanded once, at the write door; a goal would have to be
;; expanded at every read, and `goal-conjunction` normalizes to one conjunction that the
;; planner orders once and every engine walks as one.  Answering the union at `prove`
;; while `query-plan` and `abduce` refused it would make one spelling mean something
;; different at each door, so every read door refuses it alike and names the rewrite.

(tu/deftest-kb a-disjunctive-goal-is-refused-at-every-read-door
  (tu/with-terms [dog cat Muffet CxPets]
    (let [goal (list 'or (list dog Muffet) (list cat Muffet))]
      (doseq [[door f] [["ask"   #(v/ask kb goal CxPets)]
                        ["prove" #(v/prove kb goal CxPets)]
                        ["query" #(v/query kb goal CxPets)]
                        ["matching" #(v/sentexes-matching kb goal CxPets)]]]
        (testing door
          (let [^clojure.lang.ExceptionInfo e
                (try (f) nil (catch clojure.lang.ExceptionInfo ex ex))]
            (is (some? e) (str door " accepted a disjunctive goal"))
            (is (= :shape (:type (ex-data e))))
            (is (re-find #"or cannot stand in a goal" (.getMessage e))))))
      (testing "a conjunct that disjoins is refused too"
        (let [e (try (v/prove kb [(list dog Muffet) goal] CxPets) nil
                     (catch clojure.lang.ExceptionInfo ex ex))]
          (is (= :shape (:type (ex-data e)))))))))

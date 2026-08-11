;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.skolem-test
  "Head existentials + skolemization: `(implies (P ?x) (exists ?y (Q ?x ?y)))` fires
  forward on `(P a)` to derive `(Q a K)` with `K` a deterministic skolem constant — the
  same constant every time the rule fires on the same antecedent binding, so the
  fixpoint terminates.  See docs/skolem.md."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.core-context :as core-context]
            [vaelii.impl.nat :as nat]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh #(doto (tu/fresh) (core-context/load-into))))

(def ^:private C 'UniverseContext)

(defn- witness
  "The skolem constant in the (single) believed match of `goal`, at argument `pos`."
  [kb goal pos]
  (let [ms (v/sentexes-matching kb goal C)]
    (when (seq ms) (nth (:sentence (first ms)) pos))))

;; ---- basic skolemization -------------------------------------------------

(tu/deftest-kb an-existential-head-derives-a-skolem-witness
  (tu/with-terms [pP qQ A]
    (v/assert-rule kb [(list pP '?x)] (list 'exists '?y (list qQ '?x '?y)) C)
    (v/assert kb (list pP A) C {:strength :monotonic})
    (let [k (witness kb (list qQ A '?w) 2)]
      (is (some? k) "the rule fired and derived (Q A K)")
      (is (nat/reified-nat-symbol? k) "K is a nat/ skolem constant, not a variable")
      (is (= 1 (count (v/sentexes-matching kb (list qQ A '?w) C))) "exactly one witness"))))

;; ---- determinism ---------------------------------------------------------

(tu/deftest-kb the-skolem-is-deterministic-per-antecedent-binding
  (tu/with-terms [pP qQ A A2]
    (v/assert-rule kb [(list pP '?x)] (list 'exists '?y (list qQ '?x '?y)) C)
    (v/assert kb (list pP A)  C {:strength :monotonic})
    (let [k1 (witness kb (list qQ A '?w) 2)]
      (testing "re-firing on the same binding reuses the one constant (fixpoint)"
        (v/forward-chain kb)
        (v/forward-chain kb)
        (is (= 1 (count (v/sentexes-matching kb (list qQ A '?w) C))) "still one witness, not a new one each round")
        (is (= k1 (witness kb (list qQ A '?w) 2)) "and it is the same constant"))
      (testing "a different antecedent binding gets a distinct witness"
        (v/assert kb (list pP A2) C {:strength :monotonic})
        (let [k2 (witness kb (list qQ A2 '?w) 2)]
          (is (nat/reified-nat-symbol? k2))
          (is (not= k1 k2) "(P A) and (P A2) skolemize to different constants"))))))

;; ---- termination ---------------------------------------------------------

(tu/deftest-kb forward-chaining-reaches-a-fixpoint
  (tu/with-terms [pP qQ A]
    (v/assert-rule kb [(list pP '?x)] (list 'exists '?y (list qQ '?x '?y)) C)
    (v/assert kb (list pP A) C {:strength :monotonic})
    (testing "the chain converges without minting constants unboundedly"
      (is (not (:truncated? (:last (v/chain-stats kb)))) "no depth truncation")
      (is (= 1 (count (v/sentexes-matching kb (list qQ A '?w) C)))))))

;; ---- belief-following retraction -----------------------------------------

(tu/deftest-kb retracting-the-antecedent-drops-the-witness-and-its-nat
  (tu/with-terms [pP qQ A]
    (v/assert-rule kb [(list pP '?x)] (list 'exists '?y (list qQ '?x '?y)) C)
    (let [h (v/assert kb (list pP A) C {:strength :monotonic})
          k (witness kb (list qQ A '?w) 2)]
      (is (some? k))
      (v/retract! kb h)
      (testing "the derived witness falls with its antecedent"
        (is (empty? (v/sentexes-matching kb (list qQ A '?w) C))))
      (testing "no dangling nat/ symbol — the skolem's termOfUnit is cleaned up"
        (is (nil? (nat/nat-expression kb k)) "K's expression is no longer stored")))))

;; ---- the range-restriction guard is intact -------------------------------

(tu/deftest-kb an-unmarked-unbound-head-variable-is-still-rejected
  (tu/with-terms [pP qQ]
    (testing "without an exists marker an unbound consequent variable is refused"
      (let [e (try (v/assert-rule kb [(list pP '?x)] (list qQ '?x '?y) C)
                   nil
                   (catch clojure.lang.ExceptionInfo e e))]
        (is (some? e) "the assert threw")
        (is (= :not-range-restricted (:type (ex-data e))))))
    (testing "an accidental (non-existential) unbound var inside an exists head is still caught"
      (let [e (try (v/assert-rule kb [(list pP '?x)]
                                  (list 'exists '?y (list qQ '?z '?y)) C)   ; ?z bound by nothing
                   nil
                   (catch clojure.lang.ExceptionInfo e e))]
        (is (= :not-range-restricted (:type (ex-data e))) "?z is not the marked variable")))))

(tu/deftest-kb the-witness-is-a-function-of-the-rule-content
  ;; the skolem NAT keys on the rule's content digest, never on anything
  ;; store-assigned: retracting the rule and re-asserting it — a new handle — re-fires
  ;; to the *same* witness, so a fact stated about the witness keeps referring to it.
  (tu/with-terms [pP qQ likes Tom A]
    (let [hr (v/assert-rule kb [(list pP '?x)] (list 'exists '?y (list qQ '?x '?y)) C)]
      (v/assert kb (list pP A) C {:strength :monotonic})
      (let [k1 (witness kb (list qQ A '?w) 2)]
        (is (some? k1) "the rule fired")
        ;; a premise about the witness is a real use, so it keeps the constant's
        ;; termOfUnit alive across the retraction
        (v/assert kb (list likes Tom k1) C {:strength :monotonic})
        (v/retract! kb hr)
        (is (nil? (witness kb (list qQ A '?w) 2)) "the derived witness fell with its rule")
        (let [hr2 (v/assert-rule kb [(list pP '?x)] (list 'exists '?y (list qQ '?x '?y)) C)
              k2  (witness kb (list qQ A '?w) 2)]
          (is (not= hr hr2) "the re-asserted rule takes a new handle")
          (is (= k1 k2) "and still mints the same witness — content, not handle")
          (is (v/query? kb (list likes Tom k2) C) "so the fact about the witness co-refers"))))))

;; ---- shared witness across a conjunctive head ----------------------------

(tu/deftest-kb a-conjunctive-existential-head-shares-one-witness
  (tu/with-terms [pP qQ rR A]
    (v/assert-rule kb [(list pP '?x)]
                   (list 'exists '?y (list 'and (list qQ '?x '?y) (list rR '?y))) C)
    (v/assert kb (list pP A) C {:strength :monotonic})
    (let [k-q (witness kb (list qQ A '?w) 2)
          k-r (witness kb (list rR '?w) 1)]
      (is (nat/reified-nat-symbol? k-q))
      (is (nat/reified-nat-symbol? k-r))
      (is (= k-q k-r) "(Q A K) and (R K) share the same K"))))

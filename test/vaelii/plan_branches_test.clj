;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.plan-branches-test
  "Two things `vaelii.plan-test` leaves open: the planner's short-circuit branch when
  a **recursive** literal is present, and what actually happens when an evaluable runs
  with its variables still unbound.

  The short-circuit (`plan/order`, the `(< (count gens) 2)` arm) exists because there
  is nothing to *choose* between when at most one generator is reorderable — but it
  still has work to do, and the work is exactly the thing the arm's comment names:
  the deferred literals can be pulled forward **past the recursive one**, which is
  pinned last.  `plan-test` reaches that arm only with `recs` empty, so the
  `(concat gens early recs (drop-i defs early))` assembly — the only place the four
  groups are spliced back together — is never checked with all four non-trivial.  A
  reassembly that emitted `recs` before `early` would lose the early prune the branch
  exists for; one that forgot `drop-i` would emit the deferred literal twice.

  The second is a claim `vaelii.impl.plan`'s docstring makes outright: an evaluable
  run before its arguments are bound \"does not throw, it quietly yields *no*
  solutions\".  Everything in the suite tests that as an *ordering* fact — the
  evaluable ends up last, so it never runs unbound — and with `plan/*enabled*` false
  the antecedents are still in canonical order, which pins evaluables last anyway.
  Nothing executes one unbound.  The tests at the bottom do, because the whole
  justification for treating deferred literals as reorderable-but-pinned rests on the
  failure mode being empty rather than an exception."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.plan :as plan]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

;; ---- the short-circuit arm, with a recursive literal in play ----------------

(tu/deftest-kb one-generator-plus-a-recursive-literal-still-pulls-the-deferred-forward
  ;; The uncovered branch: `gens` has one member so there is no ordering decision, but
  ;; `recs` is non-empty and the deferred literal must land *between* them.  Emitting
  ;; `recs` before `early` type-checks, keeps every literal, and throws away the only
  ;; reason this arm does anything at all — the test would then run once per recursive
  ;; solution instead of pruning before the recursion is entered.
  (tu/with-terms [step reaches Aa Bb CxPlan]
    (v/assert kb (list step Aa Bb) CxPlan)
    (let [gen (list step '?x '?y)
          rec (list reaches '?y '?z)
          flt (list 'lessThan '?x '?y)
          ordered (plan/order kb [gen rec flt] CxPlan {:consequent-pred reaches})]
      (testing "the deferred literal sits behind its binder and ahead of the recursion"
        (is (= [gen flt rec] ordered)))
      (testing "and nothing is dropped or duplicated by the reassembly"
        (is (= 3 (count ordered)))
        (is (= (frequencies [gen rec flt]) (frequencies ordered)))))))

(tu/deftest-kb a-deferred-literal-the-recursion-binds-stays-after-the-recursion
  ;; The complement, and the reason `ready` is consulted rather than the deferred
  ;; literals being hoisted wholesale: `?z` is bound by the recursive literal alone, so
  ;; there is no early point to run the test at.  This is the `drop-i` call with an
  ;; empty `early` — every deferred literal has to come back out of the tail.
  (tu/with-terms [step reaches Aa Bb CxPlan]
    (v/assert kb (list step Aa Bb) CxPlan)
    (let [gen (list step '?x '?y)
          rec (list reaches '?y '?z)
          flt (list 'lessThan '?y '?z)
          ordered (plan/order kb [gen rec flt] CxPlan {:consequent-pred reaches})]
      (testing "an unbindable test cannot be pulled forward past what binds it"
        (is (= [gen rec flt] ordered)))
      (is (= 3 (count ordered))))))

(tu/deftest-kb with-no-generators-at-all-a-ready-deferred-literal-still-overtakes-the-recursion
  ;; `gens` empty — the degenerate end of the same arm.  The variables arrive from the
  ;; caller's `:bound` (a rule expanded under bindings already substituted in), so the
  ;; test is runnable immediately and belongs in front of the recursive literal.
  (tu/with-terms [reaches CxPlan]
    (let [rec (list reaches '?y '?z)
          flt (list 'lessThan '?x '?y)
          ordered (plan/order kb [rec flt] CxPlan
                              {:consequent-pred reaches :bound '#{?x ?y}})]
      (is (= [flt rec] ordered))
      (is (= 2 (count ordered))))))

;; ---- an evaluable that actually runs unbound --------------------------------
;; DECISION (vaelii.impl.plan's docstring): "(evaluate ?z (+ ?x ?y)) run before ?x is
;; bound does not throw, it quietly yields *no* solutions."  That is what licenses the
;; planner to treat deferred literals as ordinary reorderable literals that happen to
;; be pinned — if the failure mode were an exception, a planning bug would take the
;; query down instead of returning a wrong (empty) answer.

(tu/deftest-kb an-unbound-evaluate-yields-no-solutions-rather-than-throwing
  ;; Driven straight at the prover, which is the same call a chainer makes on a deferred
  ;; antecedent whose bindings do not cover it.  `eval-expr` must reach its ::fail
  ;; arm on the unbound symbol; applying `+` to it would be a ClassCastException.
  (tu/with-terms [CxEval]
    (is (empty? (v/ask kb (list 'evaluate '?z (list '+ '?q 1)) CxEval)))
    (testing "and nested one level down, where the failure has to propagate outward"
      (is (empty? (v/ask kb (list 'evaluate '?z (list '* 2 (list '+ '?q 1))) CxEval))))
    (testing "the ground form of the same expression does compute — this is not
              vacuous"
      (is (= [3] (map #(get % '?z)
                      (v/ask kb (list 'evaluate '?z (list '+ 2 1)) CxEval)))))))

(tu/deftest-kb an-unbound-comparison-yields-no-solutions-rather-than-throwing
  ;; `EvaluableProver` refuses a goal whose arguments are not all numbers, so an
  ;; unbound `lessThan` falls through to the fact and rule provers and finds nothing.
  ;; Answering-with-nothing is the documented behaviour; `apply <` on a symbol is not.
  (tu/with-terms [CxEval]
    (is (empty? (v/ask kb (list 'lessThan '?n 35) CxEval)))
    (is (empty? (v/ask kb (list 'greaterThan '?n 35) CxEval)))
    (testing "the ground comparison still answers"
      (is (seq (v/ask kb (list 'lessThan 1 35) CxEval)))
      (is (empty? (v/ask kb (list 'lessThan 35 1) CxEval))))))

;; A bare *goal* nothing binds answers empty, above.  A rule *antecedent* nothing binds
;; is refused instead, and the difference is not inconsistency — a goal is asked and
;; gone, while a rule is stored and re-run.  Answering it empty means the two chainers
;; read one rule differently forever: backward silently finds nothing, forward reaches
;; `chain/solve-deferred`, which throws rather than report a comparison that never ran
;; as one that failed — and by then the rule is stored, so every later assert re-fires
;; it and throws again.  `sentex/check-naf-closed` refuses it at assert time, which is
;; the one point where the author can still fix the typo it almost always is.

(tu/deftest-kb a-rule-antecedent-nothing-binds-is-refused-rather-than-stored
  ;; `?m` appears in no other antecedent, so however the planner arranges these the
  ;; comparison would run unbound.
  (tu/with-terms [age young Tom Bob CxPlan]
    (v/assert kb (list age Tom 30) CxPlan)
    (v/assert kb (list age Bob 40) CxPlan)
    (let [before (v/sentex-count kb)
          e (try (v/assert-rule kb [(list age '?p '?n) (list 'lessThan '?m 35)]
                                (list young '?p) CxPlan {:direction :backward})
                 nil
                 (catch clojure.lang.ExceptionInfo e e))]
      (is (some? e) "nothing in the rule writes ?m")
      (is (= :naf-not-closed (:type (ex-data e))))
      (is (= '[?m] (:unbound (ex-data e))))
      ;; the refusal is at canonicalization, so `handle-of` cannot be the probe — it
      ;; would have to build the very form that is refused
      (is (= before (v/sentex-count kb)) "a refused rule stores nothing"))
    (testing "the bound comparison is stored and runs, so this is not vacuous"
      (v/assert-rule kb [(list age '?p '?n) (list 'lessThan '?n 35)]
                     (list young '?p) CxPlan {:direction :backward})
      (is (= #{Tom} (set (map #(get % '?p)
                              (v/query kb (list young '?p) CxPlan {:max-depth 2})))))
      (testing "and identically with the planner inert"
        (is (= #{Tom} (binding [plan/*enabled* false]
                        (set (map #(get % '?p)
                                  (v/query kb (list young '?p) CxPlan
                                           {:max-depth 2}))))))))))

(tu/deftest-kb an-evaluate-antecedent-nothing-binds-is-refused-too
  ;; `evaluate` writes its first argument and reads the rest, so `?z` is not an input
  ;; and `?q` is — the split `sentex/deferred-input-vars` makes.
  (tu/with-terms [age bumped Tom CxPlan]
    (v/assert kb (list age Tom 30) CxPlan)
    (let [e (try (v/assert-rule kb [(list age '?p '?n) (list 'evaluate '?z (list '+ '?q 1))]
                                (list bumped '?p) CxPlan {:direction :backward})
                 nil
                 (catch clojure.lang.ExceptionInfo e e))]
      (is (some? e))
      (is (= :naf-not-closed (:type (ex-data e))))
      (is (= '[?q] (:unbound (ex-data e)))
          "?z is the output and is not required to be bound"))
    (testing "binding the expression's variable from the other antecedent stores it"
      (tu/with-terms [lifted]
        (v/assert-rule kb [(list age '?p '?n) (list 'evaluate '?z (list '+ '?n 1))]
                       (list lifted '?p) CxPlan {:direction :backward})
        (is (= #{Tom} (set (map #(get % '?p)
                                (v/query kb (list lifted '?p) CxPlan
                                         {:max-depth 2})))))))))

(tu/deftest-kb one-evaluate-may-feed-another-but-only-downhill
  ;; A deferred literal's output binds the ones written *after* it, because that is the
  ;; order the join runs them in — `plan/order` pins deferred literals where the author
  ;; put them.  An aggregate's output is the exception (the placement phase reorders it
  ;; into dependency order), and nothing here is an aggregate, so written order decides.
  (tu/with-terms [age chained Tom CxPlan]
    (v/assert kb (list age Tom 30) CxPlan)
    (testing "written in dependency order, the chain runs"
      (v/assert-rule kb [(list age '?p '?n)
                         (list 'evaluate '?q (list '+ '?n 1))
                         (list 'evaluate '?z (list '* '?q 2))]
                     (list chained '?p '?z) CxPlan {:direction :backward})
      (is (= [62] (map #(get % '?z)
                       (v/query kb (list chained Tom '?z) CxPlan {:max-depth 2})))))
    (testing "written the other way up, it is refused rather than run unbound"
      (tu/with-terms [uphill]
        (let [e (try (v/assert-rule kb [(list age '?p '?n)
                                        (list 'evaluate '?z (list '* '?q 2))
                                        (list 'evaluate '?q (list '+ '?n 1))]
                                    (list uphill '?p '?z) CxPlan {:direction :backward})
                     nil
                     (catch clojure.lang.ExceptionInfo e e))]
          (is (some? e))
          (is (= :naf-not-closed (:type (ex-data e))))
          (is (= '[?q] (:unbound (ex-data e)))))))))

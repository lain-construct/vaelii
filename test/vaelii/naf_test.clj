;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.naf-test
  "Negation as failure: `(unknown S)` and `(thereExists ?x S)`.

  `unknown` is closed-world negation — it holds exactly while `S` is not derivable —
  and `thereExists` existentially closes a variable off, so `(unknown (thereExists ?x
  S))` says 'there is no x such that S'.  Both are answered by a prover at level 6 (no
  backchaining), are ground/closed only, and store nothing.  See docs/naf.md."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.starter :as starter]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded starter/load-into))
(use-fixtures :each (tu/neutral))

;; ---- free-vars: what "fully bound to evaluate" means --------------------

(deftest free-vars-respects-the-quantifier
  (testing "a plain literal contributes every variable"
    (is (= '#{?x ?y} (sx/free-vars '(parentOf ?x ?y)))))
  (testing "unknown is transparent"
    (is (= '#{?x} (sx/free-vars '(unknown (flies ?x))))))
  (testing "thereExists subtracts its binder, so a closed existential has no free var"
    (is (= #{} (sx/free-vars '(thereExists ?x (parentOf ?x Tom)))))
    (is (= '#{?y} (sx/free-vars '(thereExists ?x (parentOf ?x ?y))))))
  (testing "the two combine — (unknown (thereExists ?x (P ?x ?y))) is free only in ?y"
    (is (= '#{?y} (sx/free-vars '(unknown (thereExists ?x (parentOf ?x ?y))))))
    (is (= #{}    (sx/free-vars '(unknown (thereExists ?x (parentOf ?x Tom)))))))
  (testing "a conjunction contributes every conjunct's variables, so closure covers all of them"
    (is (= '#{?x ?y} (sx/free-vars '(unknown (and (flies ?x) (parentOf ?x ?y))))))
    (is (= '#{?x} (sx/free-vars '(unknown (and (thereExists ?c (parentOf ?x ?c))
                                               (adult ?x))))))))

(deftest naf-query-conjuncts-flattens-to-what-is-evaluated
  (testing "a bare literal is one conjunct"
    (is (= '[(flies Tweety)] (sx/naf-query-conjuncts '(unknown (flies Tweety))))))
  (testing "a conjunction is its conjuncts"
    (is (= '[(flies Tweety) (adult Tweety)]
           (sx/naf-query-conjuncts '(unknown (and (flies Tweety) (adult Tweety)))))))
  (testing "nesting is flattened — a nested `and` is a goal no prover claims"
    (is (= '[(a X) (b X) (c X)]
           (sx/naf-query-conjuncts '(unknown (and (a X) (and (b X) (c X))))))))
  (testing "a quantifier is left intact: it is the prover's, not the flattener's"
    (is (= '[(thereExists ?c (parentOf ?c Tom))]
           (sx/naf-query-conjuncts '(unknown (thereExists ?c (parentOf ?c Tom))))))))

;; ---- unknown: closed-world negation -------------------------------------

(tu/deftest-kb unknown-holds-for-what-is-not-derivable
  (tu/with-terms [flies happy Tweety]
    (v/assert kb (list 'flies Tweety) 'CxWell)
    (testing "a fact that is not stored is unknown"
      (is (v/ask? kb (list 'unknown (list 'happy Tweety))))
      (is (not (v/ask? kb (list 'unknown (list 'flies Tweety))))
          "a stored, believed fact is NOT unknown"))))

(tu/deftest-kb unknown-follows-belief-a-later-fact-flips-it
  (tu/with-terms [flies Tweety]
    (testing "before the fact arrives, the literal is unknown"
      (is (v/ask? kb (list 'unknown (list 'flies Tweety)))))
    (let [h (v/assert kb (list 'flies Tweety) 'CxWell)]
      (testing "once asserted and believed, it is no longer unknown"
        (is (not (v/ask? kb (list 'unknown (list 'flies Tweety))))))
      (v/retract! kb h)
      (testing "retracting the fact makes it unknown again"
        (is (v/ask? kb (list 'unknown (list 'flies Tweety))))))))

(tu/deftest-kb unknown-refuses-an-open-goal
  ;; "must be fully bound to evaluate": an open `(unknown (flies ?x))` is not a test
  ;; but a search over the whole domain's complement, so the NAF prover refuses it —
  ;; exactly the honest refusal `different` makes (FactProver is always listed, but it
  ;; finds no stored `(unknown ...)` fact, so nothing answers).
  (let [applicable (fn [goal] (set (map :prover (v/query-plan kb goal '?ctx))))]
    (testing "the NAF prover claims a *closed* unknown"
      (is (contains? (applicable '(unknown (flies Tweety))) "UnknownProver")))
    (testing "but refuses an *open* one"
      (is (not (contains? (applicable '(unknown (flies ?x))) "UnknownProver")))
      (is (not (v/ask? kb '(unknown (flies ?x))))))))

;; ---- thereExists: existential closure -----------------------------------

(tu/deftest-kb there-exists-is-a-witnessed-existence-check
  (tu/with-terms [parentOf Ann Tom Nemo]
    (v/assert kb (list 'parentOf Ann Tom) 'CxWell)
    (testing "holds when the body is witnessed, projecting the variable out"
      (is (v/ask? kb (list 'thereExists '?x (list 'parentOf '?x Tom))))
      (is (empty? (get (tu/sole-answer (v/ask kb (list 'thereExists '?x (list 'parentOf '?x Tom)))) '?x))
          "the quantified variable does not leak into the answer"))
    (testing "fails when nothing witnesses it"
      (is (not (v/ask? kb (list 'thereExists '?x (list 'parentOf '?x Nemo))))))))

(tu/deftest-kb unknown-combined-with-there-exists
  (tu/with-terms [parentOf Ann Tom Orphan]
    (v/assert kb (list 'parentOf Ann Tom) 'CxWell)
    (testing "(unknown (thereExists ...)) is 'nobody stands in the relation'"
      (is (v/ask? kb (list 'unknown (list 'thereExists '?x (list 'parentOf '?x Orphan))))
          "no known parent of Orphan")
      (is (not (v/ask? kb (list 'unknown (list 'thereExists '?x (list 'parentOf '?x Tom)))))
          "Tom has a known parent, so it is not unknown"))))

;; ---- neither is assertible ----------------------------------------------

(tu/deftest-kb naf-operators-are-not-assertible
  (tu/with-terms [flies Tweety]
    (testing "asserting a query operator as a fact is refused (it stores nothing)"
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list 'unknown (list 'flies Tweety)) 'CxWell)))
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list 'thereExists '?x (list 'flies '?x)) 'CxWell))))))

;; ---- unknown in a rule antecedent: derive-time blocking -----------------

(tu/deftest-kb unknown-antecedent-fires-and-blocks-at-derive-time
  (tu/with-terms [pp qq rr Aa Bb]
    ;; (pp ?x) & unknown(qq ?x) => (rr ?x)
    (v/assert kb (list 'implies (list 'and (list 'pp '?x) (list 'unknown (list 'qq '?x))) (list 'rr '?x))
              'CxWell)
    (v/assert kb (list 'pp Aa) 'CxWell)          ; qq Aa absent -> fires
    (v/assert kb (list 'qq Bb) 'CxWell)          ; qq Bb present *before* pp Bb -> blocked
    (v/assert kb (list 'pp Bb) 'CxWell)
    (testing "fires when the NAF query is not derivable"
      (is (v/ask? kb (list 'rr Aa) 'CxWell)))
    (testing "does not fire when the NAF query holds at derive time"
      (is (not (v/ask? kb (list 'rr Bb) 'CxWell))))))

;; ---- order independence: block on late arrival, revive on retract -------

(tu/deftest-kb unknown-is-order-independent-block-then-revive
  (tu/with-terms [pp qq rr Aa]
    (v/assert kb (list 'implies (list 'and (list 'pp '?x) (list 'unknown (list 'qq '?x))) (list 'rr '?x))
              'CxWell)
    (v/assert kb (list 'pp Aa) 'CxWell)
    (testing "derived while the NAF query is absent"
      (is (v/ask? kb (list 'rr Aa) 'CxWell)))
    (let [h (v/assert kb (list 'qq Aa) 'CxWell)]
      (testing "a later fact that satisfies the query blocks and sweeps the conclusion"
        (is (not (v/ask? kb (list 'rr Aa) 'CxWell)))
        (is (nil? (v/handle-of kb (list 'rr Aa) 'CxWell))
            "the conclusion is deleted, not merely disbelieved (garbage collection, not defeat)"))
      (v/retract! kb h)
      (testing "retracting it revives the conclusion by re-derivation"
        (is (v/ask? kb (list 'rr Aa) 'CxWell))))))

(tu/deftest-kb unknown-is-order-independent-when-a-merge-is-what-arrives
  ;; A merge is the other way `S` becomes derivable, and it is not a fact arriving: the
  ;; inner query is answered under the term's **representative**, so `(unknown (qq Kept))`
  ;; is false for a firing that bound `?x` to a spelling the merge retired — with nothing
  ;; on `qq` having moved, so no predicate-keyed trigger can see it.
  ;;
  ;; `rewriteOf` rather than `sameAs` because the direction is the point: `sameAs` elects
  ;; by content, and if the `qq` fact's own term lost the election it would migrate, and
  ;; the migration would post an ordinary trigger that hides the channel under test.
  (tu/with-terms [pp qq rr Kept Retired]
    (v/assert kb (list 'implies (list 'and (list pp '?x) (list 'unknown (list qq '?x)))
                       (list rr '?x))
              'CxWell)
    (v/assert kb (list qq Kept) 'CxWell)
    (v/assert kb (list pp Retired) 'CxWell)
    (is (v/ask? kb (list rr Retired) 'CxWell)
        "derived while nothing under qq reaches that individual")
    (let [h (v/assert kb (list 'rewriteOf Kept Retired) 'CxWell)]
      (testing "the merge makes the inner query derivable, so the conclusion is swept"
        (is (= 1 (count (v/sentexes-matching kb (list qq '?x) 'CxWell)))
            "and qq's own extent never moved")
        (is (empty? (v/sentexes-matching kb (list rr '?x) 'CxWell))
            "under either spelling — the conclusion migrated and then went"))
      (v/retract! kb h)
      (testing "and splitting the class again revives it"
        (is (v/ask? kb (list rr Retired) 'CxWell))))))

(tu/deftest-kb a-merge-can-complete-a-conjunction-through-the-conjunct-that-was-short
  ;; The conjunctive reading of the merge channel: `qq` holds of one spelling and `rr` of
  ;; the other, so under the firing's own binding the conjunction is one conjunct short
  ;; and the rule concludes.  Merging the two makes *both* answerable under one
  ;; representative — with nothing on either predicate arriving or leaving, so no
  ;; predicate-keyed trigger sees it and `recheck-equality-edge` is the whole channel.
  (tu/with-terms [pp qq rr ss Kept Retired]
    (v/assert kb (list 'implies (list 'and (list pp '?x)
                                      (list 'unknown (list 'and (list qq '?x) (list rr '?x))))
                       (list ss '?x))
              'CxWell)
    (v/assert kb (list qq Kept) 'CxWell)
    (v/assert kb (list rr Retired) 'CxWell)
    (v/assert kb (list pp Retired) 'CxWell)
    (is (v/ask? kb (list ss Retired) 'CxWell)
        "derived while qq reaches Kept and the firing binds Retired")
    (let [h (v/assert kb (list 'rewriteOf Kept Retired) 'CxWell)]
      (testing "the merge answers both conjuncts under one representative, so it is swept"
        (is (= 1 (count (v/sentexes-matching kb (list qq '?x) 'CxWell)))
            "and qq's own extent never moved")
        (is (empty? (v/sentexes-matching kb (list ss '?x) 'CxWell))
            "under either spelling — the conclusion migrated and then went"))
      (v/retract! kb h)
      (testing "and splitting the class again revives it"
        (is (v/ask? kb (list ss Retired) 'CxWell))))))

(tu/deftest-kb a-conjunction-reaches-the-same-belief-when-the-merge-arrives-first
  ;; The oracle for the test above.  Merged first, the firing is refused at derive time
  ;; and no trigger is involved at all, so the two orders must agree.
  (tu/with-terms [pp qq rr ss Kept Retired]
    (v/assert kb (list 'rewriteOf Kept Retired) 'CxWell)
    (v/assert kb (list 'implies (list 'and (list pp '?x)
                                      (list 'unknown (list 'and (list qq '?x) (list rr '?x))))
                       (list ss '?x))
              'CxWell)
    (v/assert kb (list qq Kept) 'CxWell)
    (v/assert kb (list rr Retired) 'CxWell)
    (v/assert kb (list pp Retired) 'CxWell)
    (is (empty? (v/sentexes-matching kb (list ss '?x) 'CxWell))
        "merged first, the rule never concludes")))

(tu/deftest-kb an-unknown-reaches-the-same-belief-when-the-merge-arrives-first
  ;; the oracle for the test above: merged first, the firing is refused at derive time
  ;; and no trigger is involved at all, so the two orders must agree.
  (tu/with-terms [pp qq rr Kept Retired]
    (v/assert kb (list 'rewriteOf Kept Retired) 'CxWell)
    (v/assert kb (list 'implies (list 'and (list pp '?x) (list 'unknown (list qq '?x)))
                       (list rr '?x))
              'CxWell)
    (v/assert kb (list qq Kept) 'CxWell)
    (v/assert kb (list pp Retired) 'CxWell)
    (is (empty? (v/sentexes-matching kb (list rr '?x) 'CxWell))
        "merged first, the rule never concludes")))

(tu/deftest-kb unknown-with-there-exists-in-a-rule
  (tu/with-terms [person owns ownerless Zed]
    ;; a person nothing owns is ownerless
    (v/assert kb (list 'implies (list 'and (list 'person '?p)
                                      (list 'unknown (list 'thereExists '?c (list 'owns '?c '?p))))
                       (list 'ownerless '?p))
              'CxWell)
    (v/assert kb (list 'person Zed) 'CxWell)
    (testing "holds while nothing witnesses the existential"
      (is (v/ask? kb (list 'ownerless Zed) 'CxWell)))
    (let [h (v/assert kb (list 'owns (tu/tmp-ind "Hat") Zed) 'CxWell)]
      (testing "a witness blocks it"
        (is (not (v/ask? kb (list 'ownerless Zed) 'CxWell))))
      (v/retract! kb h)
      (testing "removing the witness revives it"
        (is (v/ask? kb (list 'ownerless Zed) 'CxWell))))))

(tu/deftest-kb standalone-there-exists-antecedent-is-a-parent
  (tu/with-terms [person parentOf a_parent Dad Kid Childless]
    ;; positive existential antecedent: a person with a child is a parent
    (v/assert kb (list 'implies (list 'and (list 'person '?x)
                                      (list 'thereExists '?y (list 'parentOf '?x '?y)))
                       (list 'a_parent '?x))
              'CxWell)
    (v/assert kb (list 'human Dad) 'CxWell)
    (v/assert kb (list 'person Childless) 'CxWell)
    (v/assert kb (list 'parentOf Dad Kid) 'CxWell)
    (testing "fires for a witnessed existential, not for an unwitnessed one"
      (is (v/ask? kb (list 'a_parent Dad) 'CxWell))
      (is (not (v/ask? kb (list 'a_parent Childless) 'CxWell))))))

;; ---- a conjunctive NAF query --------------------------------------------
;; `(unknown (and A B))` is `exceptWhen`'s conjunction inlined per literal: closure
;; leaves every conjunct ground, so they share nothing after substitution and each is an
;; independent existence check — block if **all** hold.  One evaluator answers both
;; (`provers/exception-holds?`), so the two cannot drift.

(tu/deftest-kb unknown-over-a-conjunction-blocks-only-when-every-conjunct-holds
  (tu/with-terms [pp qq rr ss Both One Neither]
    (v/assert kb (list 'implies (list 'and (list pp '?x)
                                      (list 'unknown (list 'and (list qq '?x) (list rr '?x))))
                       (list ss '?x))
              'CxWell)
    (v/assert kb (list qq Both) 'CxWell)
    (v/assert kb (list rr Both) 'CxWell)
    (v/assert kb (list qq One) 'CxWell)
    (doseq [i [Both One Neither]] (v/assert kb (list pp i) 'CxWell))
    (testing "every conjunct derivable — the query holds, so the firing is blocked"
      (is (not (v/ask? kb (list ss Both) 'CxWell))))
    (testing "one conjunct short is not the query holding"
      (is (v/ask? kb (list ss One) 'CxWell))
      (is (v/ask? kb (list ss Neither) 'CxWell)))))

(tu/deftest-kb every-conjunct-of-a-NAF-query-is-watched
  ;; The re-check index is keyed per predicate, and a conjunction blocks on the *last*
  ;; of its conjuncts to arrive — so a rule posted under the first predicate alone would
  ;; never be re-checked for the second, and belief would depend on arrival order.
  (tu/with-terms [pp qq rr ss Aa]
    (v/assert kb (list 'implies (list 'and (list pp '?x)
                                      (list 'unknown (list 'and (list qq '?x) (list rr '?x))))
                       (list ss '?x))
              'CxWell)
    (v/assert kb (list pp Aa) 'CxWell)
    (v/assert kb (list qq Aa) 'CxWell)
    (is (v/ask? kb (list ss Aa) 'CxWell)
        "one conjunct holding leaves the query underivable")
    (let [h (v/assert kb (list rr Aa) 'CxWell)]      ; the *second* conjunct, last
      (testing "completing the conjunction blocks and sweeps the conclusion"
        (is (not (v/ask? kb (list ss Aa) 'CxWell)))
        (is (nil? (v/handle-of kb (list ss Aa) 'CxWell))))
      (v/retract! kb h)
      (testing "and breaking it again revives the conclusion by re-derivation"
        (is (v/ask? kb (list ss Aa) 'CxWell))))))

(tu/deftest-kb a-conjunctive-NAF-goal-agrees-with-the-rule-antecedent
  ;; The backward reading of the same query: `UnknownProver` answers a conjunction the
  ;; way `exception-holds?` does, or `ask` and forward chaining would disagree about one
  ;; rule.
  (tu/with-terms [qq rr Both One]
    (v/assert kb (list qq Both) 'CxWell)
    (v/assert kb (list rr Both) 'CxWell)
    (v/assert kb (list qq One) 'CxWell)
    (is (not (v/ask? kb (list 'unknown (list 'and (list qq Both) (list rr Both)))))
        "both conjuncts derivable — the conjunction is known")
    (is (v/ask? kb (list 'unknown (list 'and (list qq One) (list rr One))))
        "one conjunct short — the conjunction is not derivable")))

(tu/deftest-kb a-nested-NAF-conjunction-is-flattened-not-left-as-a-goal
  ;; A nested `and` is not a goal any prover claims, so left as one conjunct it would come
  ;; back unanswerable and read as *not derivable* — the conjunction never holding, the
  ;; antecedent guarding nothing.  Conjunction is associative, so flattening is the
  ;; reading; the canonical form is flat, which is what makes the two spellings one rule.
  (tu/with-terms [pp qq rr tt ss All]
    (let [nested (list 'implies (list 'and (list pp '?x)
                                      (list 'unknown (list 'and (list qq '?x)
                                                           (list 'and (list rr '?x)
                                                                 (list tt '?x)))))
                       (list ss '?x))
          flat   (list 'implies (list 'and (list pp '?y)
                                      (list 'unknown (list 'and (list qq '?y) (list rr '?y)
                                                           (list tt '?y))))
                       (list ss '?y))
          h1     (v/assert kb nested 'CxWell)
          h2     (v/assert kb flat 'CxWell)]
      (is (= h1 h2) "the nested spelling and the flat one are one rule")
      (doseq [p [pp qq rr tt]] (v/assert kb (list p All) 'CxWell))
      (is (not (v/ask? kb (list ss All) 'CxWell))
          "every conjunct of the flattened query holds, so the firing is blocked"))))

(tu/deftest-kb a-thereExists-conjunct-is-watched-by-what-it-quantifies
  ;; A conjunct may itself be an existential — legal, because the binder is local to that
  ;; one conjunct, so the conjuncts still share nothing.  The re-check key has to be the
  ;; predicate *inside* the quantifier (`watched-query` per conjunct): keyed on
  ;; `thereExists`, which no fact carries, the arrival that completes the query is invisible.
  (tu/with-terms [person kidOf adult lonely Ppp Qqq]
    (v/assert kb (list 'implies (list 'and (list 'person '?x)
                                      (list 'unknown
                                            (list 'and (list 'thereExists '?c (list kidOf '?x '?c))
                                                  (list adult '?x))))
                       (list lonely '?x))
              'CxWell)
    (v/assert kb (list 'person Ppp) 'CxWell)
    (v/assert kb (list adult Ppp) 'CxWell)
    (is (v/ask? kb (list lonely Ppp) 'CxWell)
        "adult but childless — the existential conjunct is short, so the query does not hold")
    (let [h (v/assert kb (list kidOf Ppp Qqq) 'CxWell)]
      (testing "a witness arriving completes the query through the *existential* conjunct"
        (is (not (v/ask? kb (list lonely Ppp) 'CxWell))))
      (v/retract! kb h)
      (testing "and removing it revives the conclusion"
        (is (v/ask? kb (list lonely Ppp) 'CxWell))))))

(tu/deftest-kb a-conjunctive-NAF-antecedent-is-honoured-by-a-backward-only-rule
  ;; The companion of the single-literal case below: a backward-only rule is never
  ;; pre-materialized, so whoever expands it evaluates the conjunction itself.
  (tu/with-terms [pp qq rr ss Both One]
    (v/assert kb (list 'set/backwardRule
                       (list 'implies (list 'and (list pp '?x)
                                            (list 'unknown (list 'and (list qq '?x) (list rr '?x))))
                             (list ss '?x)))
              'CxWell)
    (v/assert kb (list pp Both) 'CxWell)
    (v/assert kb (list qq Both) 'CxWell)
    (v/assert kb (list rr Both) 'CxWell)
    (v/assert kb (list pp One) 'CxWell)
    (v/assert kb (list qq One) 'CxWell)
    (is (empty? (v/prove kb (list ss Both) 'CxWell))
        "both conjuncts derivable — the rule does not conclude")
    (is (seq (v/prove kb (list ss One) 'CxWell))
        "one conjunct short — it does")))

(tu/deftest-kb a-negated-conjunct-is-watched-and-blocks-when-it-arrives
  ;; `not` is the one frame the watched-predicate walk leaves alone, because the trigger
  ;; side keys an arriving `(not S)` under `not` as well — coarse, one bucket for every
  ;; negated condition, but the two agree, and peeling one side alone is what would break
  ;; it.  The claim is the arrival, so this is the test that would catch a peel.
  (tu/with-terms [bb ff aa oo Ned]
    (v/assert kb (list 'implies (list 'and (list bb '?x)
                                      (list 'unknown (list 'and (list 'not (list ff '?x))
                                                           (list aa '?x))))
                       (list oo '?x))
              'CxWell)
    (v/assert kb (list bb Ned) 'CxWell)
    (v/assert kb (list aa Ned) 'CxWell)
    (is (v/ask? kb (list oo Ned) 'CxWell)
        "the negated conjunct is not derivable, so the conjunction is short")
    (v/assert kb (list 'not (list ff Ned)) 'CxWell)
    (is (not (v/ask? kb (list oo Ned) 'CxWell))
        "and its arrival completes the query, so the conclusion is swept")))

(tu/deftest-kb an-aggregate-conjunct-is-watched-by-its-census-body
  ;; An aggregate's own functor is a predicate no fact carries, so the key has to be what
  ;; its body counts — the per-conjunct case of what `naf-predicates` has always done for
  ;; a bare aggregate query.
  (tu/with-terms [person kidOf adult gg Moe K1 K2]
    (v/assert kb (list 'implies (list 'and (list 'person '?x)
                                      (list 'unknown
                                            (list 'and (list 'agg/count 2 '?c (list kidOf '?x '?c))
                                                  (list adult '?x))))
                       (list gg '?x))
              'CxWell)
    (v/assert kb (list 'person Moe) 'CxWell)
    (v/assert kb (list adult Moe) 'CxWell)
    (v/assert kb (list kidOf Moe K1) 'CxWell)
    (is (v/ask? kb (list gg Moe) 'CxWell)
        "one kid — the census is not 2, so the conjunction is short")
    (v/assert kb (list kidOf Moe K2) 'CxWell)
    (is (not (v/ask? kb (list gg Moe) 'CxWell))
        "the count reaching 2 completes the query, on a predicate the aggregate frames")))

(tu/deftest-kb conjunct-order-is-not-a-NAF-rule-s-identity
  ;; The claim `sort-conjuncts` makes for an exceptWhen exception, and for the same
  ;; reason: independent ground checks, so their written order is not their identity.
  (tu/with-terms [pp qq rr ss]
    (let [h1 (v/assert kb (list 'implies (list 'and (list pp '?x)
                                               (list 'unknown (list 'and (list qq '?x) (list rr '?x))))
                                (list ss '?x))
                       'CxWell)
          h2 (v/assert kb (list 'implies (list 'and (list pp '?y)
                                               (list 'unknown (list 'and (list rr '?y) (list qq '?y))))
                                (list ss '?y))
                       'CxWell)
          h3 (v/assert kb (list 'implies (list 'and (list pp '?z)
                                               (list 'unknown (list 'and (list qq '?z) (list rr '?z)
                                                                    (list qq '?z))))
                                (list ss '?z))
                       'CxWell)]
      (is (= h1 h2) "two spellings of one conjunction are one rule")
      (is (= h1 h3) "and a repeated conjunct is not a different condition"))))

(tu/deftest-kb a-one-conjunct-NAF-and-loses-the-and-it-never-needed
  (tu/with-terms [mm nn zz]
    (let [h1 (v/assert kb (list 'implies (list 'and (list mm '?x)
                                               (list 'unknown (list 'and (list nn '?x))))
                                (list zz '?x))
                       'CxWell)
          h2 (v/assert kb (list 'implies (list 'and (list mm '?y) (list 'unknown (list nn '?y)))
                                (list zz '?y))
                       'CxWell)]
      (is (= h1 h2) "a lone conjunct is the bare literal, and stores as it"))))

;; ---- well-formedness of NAF rule antecedents ----------------------------

(tu/deftest-kb an-aggregate-refuses-a-reduction-variable-no-census-conjunct-produces
  ;; A census body is joined like a NAF query, so its conjuncts share `?v` — but the join
  ;; runs generators first, so a `?v` only a *computed* conjunct reads is a count over a
  ;; variable nothing in the body can bind.  The same hole an `unknown` is refused for.
  (tu/with-terms [person childOf sick counted]
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo #"which no conjunct of it binds"
         (v/assert kb (list 'implies
                            (list 'and (list person '?x)
                                  (list 'agg/count '?n '?c (list 'and (list childOf '?x '?x)
                                                                 (list 'unknown (list sick '?c))))
                                  (list 'lessThan 1 '?n))
                            (list counted '?x))
                   'CxWell)))
    (testing "and the same body with a generator binding it is admitted"
      (is (some? (v/assert kb (list 'implies
                                    (list 'and (list person '?x)
                                          (list 'agg/count '?n '?c
                                                (list 'and (list childOf '?x '?c)
                                                      (list sick '?c)))
                                          (list 'lessThan 1 '?n))
                                    (list counted '?x))
                           'CxWell))))))

;; ---- the joined NAF query: conjuncts sharing a quantifier's variable ----

(tu/deftest-kb a-quantified-conjunction-takes-one-witness-for-all-its-conjuncts
  ;; The whole point of the join: "has no sick child" must not hold of a parent whose
  ;; child is well merely because *some other* individual is sick.
  (tu/with-terms [childOf sick Tom Kid Stranger]
    (v/assert kb (list childOf Tom Kid) 'CxWell)
    (v/assert kb (list sick Stranger) 'CxWell)
    (let [q (list 'unknown (list 'thereExists '?c (list 'and (list childOf Tom '?c)
                                                        (list sick '?c))))]
      (testing "a well child and a sick stranger leave the existential unsatisfied"
        (is (v/ask? kb q 'CxWell)
            "read flat, the two conjuncts would each find their own witness and this would fail"))
      (v/assert kb (list sick Kid) 'CxWell)
      (testing "and the same child being sick is what satisfies it"
        (is (not (v/ask? kb q 'CxWell)))))))

(tu/deftest-kb a-joined-NAF-antecedent-blocks-and-revives
  (tu/with-terms [person childOf sick unworried Tom Kid]
    (v/assert kb (list 'implies
                       (list 'and (list person '?x)
                             (list 'unknown (list 'thereExists '?c
                                                  (list 'and (list childOf '?x '?c)
                                                        (list sick '?c)))))
                       (list unworried '?x))
              'CxWell)
    (v/assert kb (list person Tom) 'CxWell)
    (v/assert kb (list childOf Tom Kid) 'CxWell)
    (testing "no sick child, so the rule fires"
      (is (v/ask? kb (list unworried Tom) 'CxWell)))
    (let [h (v/assert kb (list sick Kid) 'CxWell)]
      (testing "the *second* conjunct's predicate is watched too, so the firing is swept"
        (is (not (v/ask? kb (list unworried Tom) 'CxWell)))
        (is (nil? (v/handle-of kb (list unworried Tom) 'CxWell))))
      (v/retract! kb h)
      (testing "and retracting it revives the conclusion by re-derivation"
        (is (v/ask? kb (list unworried Tom) 'CxWell))))))

(tu/deftest-kb a-joined-NAF-antecedent-is-order-independent
  ;; The same knowledge in the other order: the sick child is there before the rule is.
  (tu/with-terms [person childOf sick unworried Tom Kid]
    (v/assert kb (list person Tom) 'CxWell)
    (v/assert kb (list childOf Tom Kid) 'CxWell)
    (v/assert kb (list sick Kid) 'CxWell)
    (v/assert kb (list 'implies
                       (list 'and (list person '?x)
                             (list 'unknown (list 'thereExists '?c
                                                  (list 'and (list childOf '?x '?c)
                                                        (list sick '?c)))))
                       (list unworried '?x))
              'CxWell)
    (is (not (v/ask? kb (list unworried Tom) 'CxWell))
        "the rule never fires, which is the answer the other arrival order settles on")))

(tu/deftest-kb every-conjunct-of-a-quantified-query-is-a-negative-edge
  ;; Stratification reads the conjuncts through the quantifier, so a cycle through the
  ;; *second* one is refused as readily as one through the first.
  (tu/with-terms [person childOf sick unworried]
    (v/assert kb (list 'implies
                       (list 'and (list person '?x)
                             (list 'unknown (list 'thereExists '?c
                                                  (list 'and (list childOf '?x '?c)
                                                        (list sick '?c)))))
                       (list unworried '?x))
              'CxWell)
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo #"not stratified"
         (v/assert kb (list 'implies (list unworried '?y) (list sick '?y)) 'CxWell)))))

(tu/deftest-kb a-standalone-existential-over-a-conjunction-is-the-join-written-out
  ;; A *positive* standalone `thereExists` needs no NAF machinery: its conjunction is
  ;; spliced in as that many antecedents, which is the join a reader would have written.
  (tu/with-terms [parentOf sick worried Ann Kid]
    (let [h1 (v/assert kb (list 'implies
                                (list 'and (list 'thereExists '?c
                                                 (list 'and (list parentOf '?x '?c)
                                                       (list sick '?c))))
                                (list worried '?x))
                       'CxWell)
          h2 (v/assert kb (list 'implies (list 'and (list parentOf '?p '?k) (list sick '?k))
                                (list worried '?p))
                       'CxWell)]
      (is (= h1 h2) "the desugared rule is the hand-written join, to the same handle"))
    (v/assert kb (list parentOf Ann Kid) 'CxWell)
    (v/assert kb (list sick Kid) 'CxWell)
    (is (v/ask? kb (list worried Ann) 'CxWell))))

;; ---- a closed extent: (not (P a)) read as negation as failure ----------

(tu/deftest-kb a-closed-extent-answers-the-negative-from-the-absence-of-a-positive
  ;; "the months of the year are exactly these twelve"
  (tu/with-terms [month_of_year January February Smarch CxCalendar CxSibling]
    (v/assert kb (list 'genlCx CxCalendar 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxSibling 'CxUniverse) 'CxUniverse)
    (v/assert kb (list month_of_year January) CxCalendar)
    (v/assert kb (list month_of_year February) CxCalendar)
    (testing "without the grant, a month nobody listed is merely unknown"
      (is (not (v/ask? kb (list 'not (list month_of_year Smarch)) CxCalendar))))
    (v/assert kb (list 'closed_extent_predicate month_of_year) CxCalendar)
    (testing "under the grant, nothing answering the positive is what answers the negative"
      (is (v/ask? kb (list 'not (list month_of_year Smarch)) CxCalendar))
      (is (not (v/ask? kb (list 'not (list month_of_year January)) CxCalendar))
          "a member is not refuted by its own extent"))
    (testing "and the grant is scoped: a sibling theory reading the same predicate
              answers as it did before"
      (is (not (v/ask? kb (list 'not (list month_of_year Smarch)) CxSibling))))
    (testing "a member arriving withdraws the negative"
      (let [h (v/assert kb (list month_of_year Smarch) CxCalendar)]
        (is (not (v/ask? kb (list 'not (list month_of_year Smarch)) CxCalendar)))
        (v/retract! kb h)
        (is (v/ask? kb (list 'not (list month_of_year Smarch)) CxCalendar))))))

(tu/deftest-kb a-closed-extent-rule-antecedent-is-negation-as-failure
  (tu/with-terms [month_of_year candidate not_a_month Smarch CxCalendar]
    (v/assert kb (list 'genlCx CxCalendar 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'closed_extent_predicate month_of_year) CxCalendar)
    (v/assert kb (list 'implies (list 'and (list candidate '?m)
                                      (list 'not (list month_of_year '?m)))
                       (list not_a_month '?m))
              CxCalendar)
    (v/assert kb (list candidate Smarch) CxCalendar)
    (testing "the rule fires on the absence of a member, with nothing negative stored"
      (is (v/ask? kb (list not_a_month Smarch) CxCalendar))
      (is (nil? (v/handle-of kb (list 'not (list month_of_year Smarch)) CxCalendar))
          "and nothing about the negative space was stored to make it fire"))
    (let [h (v/assert kb (list month_of_year Smarch) CxCalendar)]
      (testing "the member arriving withdraws the firing"
        (is (not (v/ask? kb (list not_a_month Smarch) CxCalendar)))
        (is (nil? (v/handle-of kb (list not_a_month Smarch) CxCalendar))
            "withdrawn, not merely disbelieved"))
      (v/retract! kb h)
      (testing "and retracting it revives the conclusion"
        (is (v/ask? kb (list not_a_month Smarch) CxCalendar))))))

(tu/deftest-kb a-closed-extent-rule-is-order-independent
  ;; The same knowledge in the other order: the member is there before the rule and
  ;; before the grant.
  (tu/with-terms [month_of_year candidate not_a_month Smarch CxCalendar]
    (v/assert kb (list 'genlCx CxCalendar 'CxUniverse) 'CxUniverse)
    (v/assert kb (list candidate Smarch) CxCalendar)
    (v/assert kb (list 'implies (list 'and (list candidate '?m)
                                      (list 'not (list month_of_year '?m)))
                       (list not_a_month '?m))
              CxCalendar)
    (v/assert kb (list 'closed_extent_predicate month_of_year) CxCalendar)
    (testing "the grant arriving after the rule is what makes it fire"
      (is (v/ask? kb (list not_a_month Smarch) CxCalendar)))
    (v/assert kb (list month_of_year Smarch) CxCalendar)
    (testing "and a member arriving after that withdraws it, as in the other order"
      (is (not (v/ask? kb (list not_a_month Smarch) CxCalendar))))))

(tu/deftest-kb a-stored-negative-still-works-under-a-closed-extent
  (tu/with-terms [month_of_year candidate not_a_month Smarch CxCalendar]
    (v/assert kb (list 'genlCx CxCalendar 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'closed_extent_predicate month_of_year) CxCalendar)
    (v/assert kb (list 'implies (list 'and (list candidate '?m)
                                      (list 'not (list month_of_year '?m)))
                       (list not_a_month '?m))
              CxCalendar)
    (v/assert kb (list candidate Smarch) CxCalendar)
    (v/assert kb (list 'not (list month_of_year Smarch)) CxCalendar)
    (is (v/ask? kb (list not_a_month Smarch) CxCalendar)
        "a stored negative answers the antecedent as it always did")))

(tu/deftest-kb a-closed-extent-cycle-through-negation-is-refused
  (tu/with-terms [month_of_year candidate CxCalendar]
    (v/assert kb (list 'genlCx CxCalendar 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'closed_extent_predicate month_of_year) CxCalendar)
    (testing "a rule concluding P whose body reads (not (P …)) under the grant"
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo #"not stratified"
           (v/assert kb (list 'implies (list 'and (list candidate '?m)
                                             (list 'not (list month_of_year '?m)))
                              (list month_of_year '?m))
                     CxCalendar))))))

(tu/deftest-kb a-grant-that-would-close-a-cycle-is-refused
  ;; The other arrival order: the rule is stored first, and the grant is what would add
  ;; the negative edge.
  (tu/with-terms [month_of_year candidate CxCalendar]
    (v/assert kb (list 'genlCx CxCalendar 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'implies (list 'and (list candidate '?m)
                                      (list 'not (list month_of_year '?m)))
                       (list month_of_year '?m))
              CxCalendar)
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo #"not stratified"
         (v/assert kb (list 'closed_extent_predicate month_of_year) CxCalendar)))))

(tu/deftest-kb why-not-says-the-extent-is-closed
  (tu/with-terms [month_of_year Smarch CxCalendar]
    (v/assert kb (list 'genlCx CxCalendar 'CxUniverse) 'CxUniverse)
    (testing "without the grant it is simply not stored"
      (is (= :not-stored (:reason (v/why-not kb (list month_of_year Smarch) CxCalendar)))))
    (v/assert kb (list 'closed_extent_predicate month_of_year) CxCalendar)
    (testing "under it the KB is not silent — the extent is complete and this is not in it"
      (is (= :closed-extent
             (:reason (v/why-not kb (list month_of_year Smarch) CxCalendar)))))))

;; ---- forall: sugar for the nested NAF ----------------------------------

(deftest forall-desugars-to-a-nested-unknown
  (testing "forall ?y (B => H) is not-exists ?y (B and not-H), two unknowns in a closed world"
    (is (= '(unknown (thereExists ?y (and (childOf ?x ?y) (unknown (asleep ?y)))))
           (sx/desugar-forall-literal '(forall ?y (implies (childOf ?x ?y) (asleep ?y)))))))
  (testing "a conjunctive body contributes that many conjuncts to the join"
    (is (= '(unknown (thereExists ?y (and (childOf ?x ?y) (minor ?y) (unknown (asleep ?y)))))
           (sx/desugar-forall-literal
            '(forall ?y (implies (and (childOf ?x ?y) (minor ?y)) (asleep ?y)))))))
  (testing "a forall over something that is not an implication is refused"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"not an \(implies"
                          (sx/desugar-forall-literal '(forall ?y (asleep ?y))))))
  (testing "free-vars subtracts the binder, so a closed forall is closed"
    (is (= '#{?x} (sx/free-vars '(forall ?y (implies (childOf ?x ?y) (asleep ?y))))))))

(tu/deftest-kb a-stored-forall-rule-shows-the-nested-form
  (tu/with-terms [person childOf asleep all_kids_asleep]
    (let [sugar (list 'implies
                      (list 'and (list person '?x)
                            (list 'forall '?y (list 'implies (list childOf '?x '?y)
                                                    (list asleep '?y))))
                      (list all_kids_asleep '?x))
          nested (list 'implies
                       (list 'and (list person '?p)
                             (list 'unknown
                                   (list 'thereExists '?k
                                         (list 'and (list childOf '?p '?k)
                                               (list 'unknown (list asleep '?k))))))
                       (list all_kids_asleep '?p))]
      (is (= (:sentence (v/canonical-sentex kb sugar 'CxWell))
             (:sentence (v/canonical-sentex kb nested 'CxWell)))
          "the sugar exists at the door and nowhere past it")
      (is (= (v/assert kb sugar 'CxWell) (v/assert kb nested 'CxWell))
          "so the two are one rule, to one handle"))))

(tu/deftest-kb all-of-bobs-children-are-asleep
  ;; The common-sense reading, in the order the classical one is argued in.
  (tu/with-terms [person childOf asleep all_kids_asleep Bob Kid1 Kid2 Kid3]
    (v/assert kb (list 'implies
                       (list 'and (list person '?x)
                             (list 'forall '?y (list 'implies (list childOf '?x '?y)
                                                     (list asleep '?y))))
                       (list all_kids_asleep '?x))
              'CxWell)
    (v/assert kb (list person Bob) 'CxWell)
    (testing "vacuously true - Bob has no children, so nothing is a counterexample"
      (is (v/ask? kb (list all_kids_asleep Bob) 'CxWell)))
    (v/assert kb (list childOf Bob Kid1) 'CxWell)
    (v/assert kb (list asleep Kid1) 'CxWell)
    (v/assert kb (list childOf Bob Kid2) 'CxWell)
    (v/assert kb (list asleep Kid2) 'CxWell)
    (testing "two children, both asleep"
      (is (v/ask? kb (list all_kids_asleep Bob) 'CxWell)))
    (let [h (v/assert kb (list childOf Bob Kid3) 'CxWell)]
      (testing "a third child nobody says is asleep is the counterexample"
        (is (not (v/ask? kb (list all_kids_asleep Bob) 'CxWell)))
        (is (nil? (v/handle-of kb (list all_kids_asleep Bob) 'CxWell))
            "the conclusion is withdrawn, not merely disbelieved"))
      (testing "and the goal form agrees with the rule antecedent"
        (is (not (v/ask? kb (list 'forall '?y (list 'implies (list childOf Bob '?y)
                                                    (list asleep '?y)))
                         'CxWell))))
      (v/retract! kb h)
      (testing "retracting that child revives the conclusion"
        (is (v/ask? kb (list all_kids_asleep Bob) 'CxWell))))
    (testing "and the third child back, asleep, is not a counterexample"
      (v/assert kb (list childOf Bob Kid3) 'CxWell)
      (v/assert kb (list asleep Kid3) 'CxWell)
      (is (v/ask? kb (list all_kids_asleep Bob) 'CxWell)))))

(tu/deftest-kb forall-is-order-independent
  ;; The counterexample is already there when the rule arrives.
  (tu/with-terms [person childOf asleep all_kids_asleep Bob Kid1]
    (v/assert kb (list person Bob) 'CxWell)
    (v/assert kb (list childOf Bob Kid1) 'CxWell)
    (v/assert kb (list 'implies
                       (list 'and (list person '?x)
                             (list 'forall '?y (list 'implies (list childOf '?x '?y)
                                                     (list asleep '?y))))
                       (list all_kids_asleep '?x))
              'CxWell)
    (is (not (v/ask? kb (list all_kids_asleep Bob) 'CxWell)))
    (v/assert kb (list asleep Kid1) 'CxWell)
    (is (v/ask? kb (list all_kids_asleep Bob) 'CxWell)
        "and the same knowledge in either order settles the same way")))

(tu/deftest-kb a-forall-over-what-the-rule-concludes-is-a-cycle-through-negation
  ;; Both halves of the desugar are negative edges: the body's predicate and the head's.
  (tu/with-terms [person childOf asleep all_kids_asleep]
    (v/assert kb (list 'implies
                       (list 'and (list person '?x)
                             (list 'forall '?y (list 'implies (list childOf '?x '?y)
                                                     (list asleep '?y))))
                       (list all_kids_asleep '?x))
              'CxWell)
    (testing "a rule concluding the forall's head predicate closes the cycle"
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo #"not stratified"
           (v/assert kb (list 'implies (list all_kids_asleep '?z) (list asleep '?z)) 'CxWell))))
    (testing "and so does one concluding its body predicate"
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo #"not stratified"
           (v/assert kb (list 'implies (list all_kids_asleep '?z) (list childOf '?z '?z))
                     'CxWell))))))

(tu/deftest-kb a-forall-binder-that-escapes-is-refused
  (tu/with-terms [person childOf asleep flagged]
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo #"escapes its quantifier"
         (v/assert kb (list 'implies
                            (list 'and (list person '?x) (list asleep '?y)
                                  (list 'forall '?y (list 'implies (list childOf '?x '?y)
                                                          (list asleep '?y))))
                            (list flagged '?x))
                   'CxWell)))))

(tu/deftest-kb forall-is-not-assertible
  (tu/with-terms [childOf asleep Bob Kid]
    (testing "the written spelling carries a variable, so the ground check refuses it first"
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo #"not ground"
           (v/assert kb (list 'forall '?y (list 'implies (list childOf Bob '?y)
                                                (list asleep '?y)))
                     'CxWell))))
    (testing "and a ground one reaches the query-operator arm, like unknown's"
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo #"query operator"
           (v/assert kb (list 'forall Kid (list 'implies (list childOf Bob Kid)
                                                (list asleep Kid)))
                     'CxWell))))))

(tu/deftest-kb a-computed-conjunct-nothing-in-the-query-binds-is-refused
  (tu/with-terms [person childOf asleep settled]
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo #"nothing in the query binds"
         (v/assert kb (list 'implies
                            (list 'and (list person '?x)
                                  (list 'unknown (list 'thereExists '?c
                                                       (list 'and (list childOf '?x '?x)
                                                             (list 'unknown (list asleep '?c))))))
                            (list settled '?x))
                   'CxWell)))))

(tu/deftest-kb an-empty-NAF-conjunction-is-refused
  (tu/with-terms [person nobody]
    (testing "nothing can make it derivable, so it would guard nothing"
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo #"empty conjunction"
           (v/assert kb (list 'implies (list 'and (list person '?x) (list 'unknown (list 'and)))
                              (list nobody '?x))
                     'CxWell))))))

(tu/deftest-kb unknown-must-be-closed-by-the-generators
  (tu/with-terms [person likes knows loner]
    (testing "an unknown whose free variable no generator binds is refused"
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo #"not closed"
           (v/assert kb (list 'implies (list 'and (list 'person '?x) (list 'unknown (list 'likes '?x '?z)))
                              (list 'loner '?x))
                     'CxWell))))
    (testing "and so is a conjunction one of whose conjuncts is open — closure is what
              makes the conjuncts independent ground checks"
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo #"not closed"
           (v/assert kb (list 'implies (list 'and (list 'person '?x)
                                             (list 'unknown (list 'and (list knows '?x)
                                                                  (list likes '?x '?z))))
                              (list 'loner '?x))
                     'CxWell))))))

(tu/deftest-kb there-exists-variable-must-be-local
  (tu/with-terms [person foo bar]
    (testing "a quantified variable that escapes its thereExists is refused"
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo #"escapes its quantifier"
           (v/assert kb (list 'implies (list 'and (list 'person '?x) (list 'thereExists '?x (list 'foo '?x)))
                              (list 'bar '?x))
                     'CxWell))))))

;; ---- stratification: no cycle through negation --------------------------

(tu/deftest-kb a-cycle-through-unknown-is-refused
  (tu/with-terms [aa bb cc dd ee]
    (testing "an acyclic NAF rule is accepted"
      (is (v/assert kb (list 'implies (list 'and (list 'aa '?x) (list 'unknown (list 'bb '?x)))
                             (list 'cc '?x))
                    'CxWell)))
    (testing "closing the loop — a rule concluding the NAF predicate — is refused"
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo #"not stratified"
           (v/assert kb (list 'implies (list 'cc '?x) (list 'bb '?x)) 'CxWell))))
    (testing "a one-rule cycle (unknown on what it concludes) is refused"
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo #"not stratified"
           (v/assert kb (list 'implies (list 'and (list 'dd '?x) (list 'unknown (list 'ee '?x)))
                              (list 'ee '?x))
                     'CxWell))))))

(tu/deftest-kb a-cycle-through-any-conjunct-of-a-NAF-conjunction-is-refused
  ;; Every conjunct is a negative dependency, not just the first: the negative edges are
  ;; drawn from `rules/naf-predicates`, which reads the whole conjunction, so a rule
  ;; concluding *any* conjunct's predicate closes a cycle through negation.  Keyed on the
  ;; conjunction's own functor instead, the check would see one predicate — `and`, which
  ;; nothing concludes — and refuse nothing at all.
  (tu/with-terms [gg aa bb cc]
    (is (v/assert kb (list 'implies (list 'and (list gg '?x)
                                          (list 'unknown (list 'and (list aa '?x) (list bb '?x))))
                           (list cc '?x))
                  'CxWell)
        "the acyclic conjunctive rule is accepted")
    (testing "closing the loop through the first conjunct is refused"
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo #"not stratified"
           (v/assert kb (list 'implies (list cc '?x) (list aa '?x)) 'CxWell))))
    (testing "and through the second, which is the one a single-predicate key would miss"
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo #"not stratified"
           (v/assert kb (list 'implies (list cc '?x) (list bb '?x)) 'CxWell))))))

;; ---- backward agreement: a NAF antecedent under rule expansion ----------
;; A backward-only rule cannot be pre-materialized by forward chaining, so whoever
;; expands it has to evaluate the `unknown` itself.  Both backward chainers do, and this
;; is the analogue of the `different`-in-a-backward-rule case: the invariant is that no
;; two readers of one rule disagree about it, forward chaining included.

(tu/deftest-kb every-backward-chainer-evaluates-unknown-in-a-backward-only-rule
  (tu/with-terms [pp qq rr Aa Bb]
    (v/assert kb (list 'set/backwardRule
                       (list 'implies (list 'and (list 'pp '?x) (list 'unknown (list 'qq '?x)))
                             (list 'rr '?x)))
              'CxWell)
    (v/assert kb (list 'pp Aa) 'CxWell)
    (v/assert kb (list 'pp Bb) 'CxWell)
    (v/assert kb (list 'qq Bb) 'CxWell)
    (testing "the rule forward-derives nothing (it is backward-only)"
      (is (empty? (v/sentexes-matching kb (list 'rr '?x) 'CxWell))))
    (testing "every backward chainer expands the rule and honours the unknown"
      ;; the node engine (`query` at a depth) and the recur DFS must agree
      (doseq [provable? [#(v/query? kb % 'CxWell {:max-depth 2})
                         #(v/provable? kb % 'CxWell)]]
        (is (provable? (list 'rr Aa)) "qq Aa absent -> provable")
        (is (not (provable? (list 'rr Bb))) "qq Bb present -> not provable"))
      (is (= 1 (count (v/prove kb (list 'rr Aa) 'CxWell))))
      (is (= 0 (count (v/prove kb (list 'rr Bb) 'CxWell)))))))

;; ---- prove/backward now evaluate a deferred antecedent ------------------
;; The gap that was: the recursive chainer discharged an antecedent by fact
;; matching + rule expansion only, so a rule with a DEFERRED antecedent (different /
;; evaluate / unknown) proved nothing there — while `ask` and forward chaining honoured
;; it.  A backward-ONLY rule forces the backward path (forward cannot pre-materialize).

(tu/deftest-kb prove-and-backward-honour-every-deferred-antecedent
  (tu/with-terms [rel distinctPair age nextAge Ann Bob Tom]
    ;; `different` — the unique-name test
    (v/assert kb (list rel Ann Bob) 'CxWell)
    (v/assert kb (list rel Ann Ann) 'CxWell)
    (v/assert kb (list 'set/backwardRule
                       (list 'implies (list 'and (list rel '?x '?y) (list 'different '?x '?y))
                             (list distinctPair '?x '?y)))
              'CxWell)
    (testing "different: prove and backward honour it in a backward-only rule"
      (is (v/provable? kb (list distinctPair Ann Bob) 'CxWell))
      (is (not (v/provable? kb (list distinctPair Ann Ann) 'CxWell)))
      (is (= 1 (count (v/prove kb (list distinctPair Ann Bob) 'CxWell))))
      (is (= 0 (count (v/prove kb (list distinctPair Ann Ann) 'CxWell)))))
    ;; `evaluate` — computed, binds its output
    (v/assert kb (list age Tom 40) 'CxWell)
    (v/assert kb (list 'set/backwardRule
                       (list 'implies (list 'and (list age '?p '?n) (list 'evaluate '?next (list '+ '?n 1)))
                             (list nextAge '?p '?next)))
              'CxWell)
    (testing "evaluate: prove checks and backward binds the computed value"
      (is (v/provable? kb (list nextAge Tom 41) 'CxWell))
      (is (not (v/provable? kb (list nextAge Tom 99) 'CxWell)))
      (is (= [41] (map #(get % '?a) (v/prove kb (list nextAge Tom '?a) 'CxWell)))))))

;; ---- belief-sensitivity: unknown reads belief, not mere storage ---------
;; `(unknown S)` holds of an `S` that is stored but currently OUT (a defeated
;; default), because a level-6 match is belief-filtered.  Closed-world negation is
;; about what is *believed*, not what happens to sit in the store.

(tu/deftest-kb unknown-holds-of-a-defeated-default
  (tu/with-terms [happy Zed]
    (v/assert kb (list 'happy Zed) 'CxWell {:strength :default})
    (testing "while believed, it is not unknown"
      (is (not (v/ask? kb (list 'unknown (list 'happy Zed))))))
    ;; a monotonic negation defeats the default: (happy Zed) goes OUT but stays stored
    (v/assert kb (list 'not (list 'happy Zed)) 'CxWell {:strength :monotonic})
    (testing "the default is now stored-but-disbelieved"
      (is (some? (v/handle-of kb (list 'happy Zed) 'CxWell)) "still stored")
      (is (not (v/ask? kb (list 'happy Zed) 'CxWell)) "but not believed"))
    (testing "so the belief-sensitive unknown now holds"
      (is (v/ask? kb (list 'unknown (list 'happy Zed))))
      (is (not (v/ask? kb (list 'unknown (list 'not (list 'happy Zed)))))
          "the believed negation is *not* unknown"))))

;; ---- block-if-any across several unknown antecedents --------------------
;; Each `(unknown S)` is an INDEPENDENT block condition (unlike an exception's
;; conjuncts, which block only when all hold): any one derivable inner blocks.

(tu/deftest-kb multiple-unknowns-block-if-any-holds
  (tu/with-terms [pp qq ss rr Aa]
    (v/assert kb (list 'implies (list 'and (list 'pp '?x)
                                      (list 'unknown (list 'qq '?x))
                                      (list 'unknown (list 'ss '?x)))
                       (list 'rr '?x))
              'CxWell)
    (v/assert kb (list 'pp Aa) 'CxWell)
    (testing "fires only when BOTH inners are absent"
      (is (v/ask? kb (list 'rr Aa) 'CxWell)))
    (let [h (v/assert kb (list 'ss Aa) 'CxWell)]
      (testing "one inner holding is enough to block"
        (is (not (v/ask? kb (list 'rr Aa) 'CxWell))))
      (v/retract! kb h)
      (testing "and revives when it leaves"
        (is (v/ask? kb (list 'rr Aa) 'CxWell))))))

;; ---- subtype fan-out: the NAF query and its trigger follow genl ---------
;; `(unknown (super ?x))` must be blocked by a `(sub ?x)` fact — the level-6 query
;; fans the functor over its spec closure — and a *later* `sub` fact must trigger a
;; re-check of a rule that only ever mentions `super`.

(tu/deftest-kb unknown-follows-the-subtype-closure
  ;; bound (gensym'd) types/predicates throughout, so `genl`, the rule's NAF query,
  ;; and the subtype fact all name the *same* terms
  (tu/with-terms [sub super pp rr Aa]
    (v/assert kb (list 'genl sub super) 'CxWell)
    (v/assert kb (list 'implies (list 'and (list pp '?x) (list 'unknown (list super '?x)))
                       (list rr '?x))
              'CxWell)
    (v/assert kb (list pp Aa) 'CxWell)
    (testing "with no super/sub membership, it fires"
      (is (v/ask? kb (list rr Aa) 'CxWell)))
    (let [h (v/assert kb (list sub Aa) 'CxWell)]
      (testing "a subtype fact satisfies the supertype NAF query and blocks it"
        (is (not (v/ask? kb (list rr Aa) 'CxWell))
            "(sub Aa) makes (super Aa) derivable, so (unknown (super Aa)) fails"))
      (v/retract! kb h)
      (testing "removing it revives the conclusion"
        (is (v/ask? kb (list rr Aa) 'CxWell))))))

;; ---- context scoping: a fact the conclusion cannot see does not block ---
;; The `unknown` is evaluated in the conclusion's PLACEMENT context, so a fact in a
;; sibling context — one the placement context does not see via genlCx — cannot
;; make its inner derivable.  This is why it is a derive-time check, not a global
;; `?ctx` join filter.

(tu/deftest-kb unknown-respects-the-placement-context
  (tu/with-terms [pp qq rr Aa CxPar CxSubA CxSubB]
    ;; two sibling contexts under a common parent; siblings do not see each other
    (v/assert kb (list 'genlCx CxSubA CxPar) 'CxWell)
    (v/assert kb (list 'genlCx CxSubB CxPar) 'CxWell)
    ;; rule + generator live in SubA, so the conclusion is placed in SubA
    (v/assert kb (list 'implies (list 'and (list 'pp '?x) (list 'unknown (list 'qq '?x)))
                       (list 'rr '?x))
              CxSubA)
    (v/assert kb (list 'pp Aa) CxSubA)
    (testing "the conclusion is derived in SubA"
      (is (v/ask? kb (list 'rr Aa) CxSubA)))
    ;; a qq fact in the *sibling* SubB is invisible from SubA, so it must NOT block
    (let [h (v/assert kb (list 'qq Aa) CxSubB)]
      (testing "a fact in an unseen sibling context does not satisfy the NAF query"
        (is (v/ask? kb (list 'rr Aa) CxSubA)
            "(qq Aa) in SubB is not visible from SubA, so (unknown (qq Aa)) still holds"))
      (v/retract! kb h))
    ;; but a qq fact in SubA itself IS visible, so it blocks
    (let [h (v/assert kb (list 'qq Aa) CxSubA)]
      (testing "a fact in the placement context does block"
        (is (not (v/ask? kb (list 'rr Aa) CxSubA))))
      (v/retract! kb h))))

;; ---- thereExists with a vector of quantified variables ------------------

(tu/deftest-kb there-exists-binds-a-vector-of-variables
  (tu/with-terms [rel Aa Bb]
    (v/assert kb (list 'rel Aa Bb) 'CxWell)
    (testing "a vector binder closes off all its variables"
      (is (= #{} (sx/free-vars (list 'thereExists ['?x '?y] (list 'rel '?x '?y)))))
      (is (v/ask? kb (list 'thereExists ['?x '?y] (list 'rel '?x '?y))))
      (is (not (v/ask? kb (list 'thereExists ['?x '?y] (list 'rel '?x 'NoSuchThing))))))))

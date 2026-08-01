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
    (is (= #{}    (sx/free-vars '(unknown (thereExists ?x (parentOf ?x Tom))))))))

;; ---- unknown: closed-world negation -------------------------------------

(tu/deftest-kb unknown-holds-for-what-is-not-derivable
  (tu/with-terms [flies happy Tweety]
    (v/assert kb (list 'flies Tweety) 'WellContext)
    (testing "a fact that is not stored is unknown"
      (is (v/ask? kb (list 'unknown (list 'happy Tweety))))
      (is (not (v/ask? kb (list 'unknown (list 'flies Tweety))))
          "a stored, believed fact is NOT unknown"))))

(tu/deftest-kb unknown-follows-belief-a-later-fact-flips-it
  (tu/with-terms [flies Tweety]
    (testing "before the fact arrives, the literal is unknown"
      (is (v/ask? kb (list 'unknown (list 'flies Tweety)))))
    (let [h (v/assert kb (list 'flies Tweety) 'WellContext)]
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
    (v/assert kb (list 'parentOf Ann Tom) 'WellContext)
    (testing "holds when the body is witnessed, projecting the variable out"
      (is (v/ask? kb (list 'thereExists '?x (list 'parentOf '?x Tom))))
      (is (empty? (get (first (v/ask kb (list 'thereExists '?x (list 'parentOf '?x Tom)))) '?x))
          "the quantified variable does not leak into the answer"))
    (testing "fails when nothing witnesses it"
      (is (not (v/ask? kb (list 'thereExists '?x (list 'parentOf '?x Nemo))))))))

(tu/deftest-kb unknown-combined-with-there-exists
  (tu/with-terms [parentOf Ann Tom Orphan]
    (v/assert kb (list 'parentOf Ann Tom) 'WellContext)
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
                   (v/assert kb (list 'unknown (list 'flies Tweety)) 'WellContext)))
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list 'thereExists '?x (list 'flies '?x)) 'WellContext))))))

;; ---- unknown in a rule antecedent: derive-time blocking -----------------

(tu/deftest-kb unknown-antecedent-fires-and-blocks-at-derive-time
  (tu/with-terms [pp qq rr Aa Bb]
    ;; (pp ?x) & unknown(qq ?x) => (rr ?x)
    (v/assert kb (list 'implies (list 'and (list 'pp '?x) (list 'unknown (list 'qq '?x))) (list 'rr '?x))
              'WellContext)
    (v/assert kb (list 'pp Aa) 'WellContext)          ; qq Aa absent -> fires
    (v/assert kb (list 'qq Bb) 'WellContext)          ; qq Bb present *before* pp Bb -> blocked
    (v/assert kb (list 'pp Bb) 'WellContext)
    (testing "fires when the NAF query is not derivable"
      (is (v/ask? kb (list 'rr Aa) 'WellContext)))
    (testing "does not fire when the NAF query holds at derive time"
      (is (not (v/ask? kb (list 'rr Bb) 'WellContext))))))

;; ---- order independence: block on late arrival, revive on retract -------

(tu/deftest-kb unknown-is-order-independent-block-then-revive
  (tu/with-terms [pp qq rr Aa]
    (v/assert kb (list 'implies (list 'and (list 'pp '?x) (list 'unknown (list 'qq '?x))) (list 'rr '?x))
              'WellContext)
    (v/assert kb (list 'pp Aa) 'WellContext)
    (testing "derived while the NAF query is absent"
      (is (v/ask? kb (list 'rr Aa) 'WellContext)))
    (let [h (v/assert kb (list 'qq Aa) 'WellContext)]
      (testing "a later fact that satisfies the query blocks and sweeps the conclusion"
        (is (not (v/ask? kb (list 'rr Aa) 'WellContext)))
        (is (nil? (v/handle-of kb (list 'rr Aa) 'WellContext))
            "the conclusion is deleted, not merely disbelieved (garbage collection, not defeat)"))
      (v/retract! kb h)
      (testing "retracting it revives the conclusion by re-derivation"
        (is (v/ask? kb (list 'rr Aa) 'WellContext))))))

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
              'WellContext)
    (v/assert kb (list qq Kept) 'WellContext)
    (v/assert kb (list pp Retired) 'WellContext)
    (is (v/ask? kb (list rr Retired) 'WellContext)
        "derived while nothing under qq reaches that individual")
    (let [h (v/assert kb (list 'rewriteOf Kept Retired) 'WellContext)]
      (testing "the merge makes the inner query derivable, so the conclusion is swept"
        (is (= 1 (count (v/sentexes-matching kb (list qq '?x) 'WellContext)))
            "and qq's own extent never moved")
        (is (empty? (v/sentexes-matching kb (list rr '?x) 'WellContext))
            "under either spelling — the conclusion migrated and then went"))
      (v/retract! kb h)
      (testing "and splitting the class again revives it"
        (is (v/ask? kb (list rr Retired) 'WellContext))))))

(tu/deftest-kb an-unknown-reaches-the-same-belief-when-the-merge-arrives-first
  ;; the oracle for the test above: merged first, the firing is refused at derive time
  ;; and no trigger is involved at all, so the two orders must agree.
  (tu/with-terms [pp qq rr Kept Retired]
    (v/assert kb (list 'rewriteOf Kept Retired) 'WellContext)
    (v/assert kb (list 'implies (list 'and (list pp '?x) (list 'unknown (list qq '?x)))
                       (list rr '?x))
              'WellContext)
    (v/assert kb (list qq Kept) 'WellContext)
    (v/assert kb (list pp Retired) 'WellContext)
    (is (empty? (v/sentexes-matching kb (list rr '?x) 'WellContext))
        "merged first, the rule never concludes")))

(tu/deftest-kb unknown-with-there-exists-in-a-rule
  (tu/with-terms [person owns ownerless Zed]
    ;; a person nothing owns is ownerless
    (v/assert kb (list 'implies (list 'and (list 'person '?p)
                                      (list 'unknown (list 'thereExists '?c (list 'owns '?c '?p))))
                       (list 'ownerless '?p))
              'WellContext)
    (v/assert kb (list 'person Zed) 'WellContext)
    (testing "holds while nothing witnesses the existential"
      (is (v/ask? kb (list 'ownerless Zed) 'WellContext)))
    (let [h (v/assert kb (list 'owns (tu/tmp-ind "Hat") Zed) 'WellContext)]
      (testing "a witness blocks it"
        (is (not (v/ask? kb (list 'ownerless Zed) 'WellContext))))
      (v/retract! kb h)
      (testing "removing the witness revives it"
        (is (v/ask? kb (list 'ownerless Zed) 'WellContext))))))

(tu/deftest-kb standalone-there-exists-antecedent-is-a-parent
  (tu/with-terms [person parentOf aParent Dad Kid Childless]
    ;; positive existential antecedent: a person with a child is a parent
    (v/assert kb (list 'implies (list 'and (list 'person '?x)
                                      (list 'thereExists '?y (list 'parentOf '?x '?y)))
                       (list 'aParent '?x))
              'WellContext)
    (v/assert kb (list 'person Dad) 'WellContext)
    (v/assert kb (list 'person Childless) 'WellContext)
    (v/assert kb (list 'parentOf Dad Kid) 'WellContext)
    (testing "fires for a witnessed existential, not for an unwitnessed one"
      (is (v/ask? kb (list 'aParent Dad) 'WellContext))
      (is (not (v/ask? kb (list 'aParent Childless) 'WellContext))))))

;; ---- well-formedness of NAF rule antecedents ----------------------------

(tu/deftest-kb unknown-must-be-closed-by-the-generators
  (tu/with-terms [person likes loner]
    (testing "an unknown whose free variable no generator binds is refused"
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo #"not closed"
           (v/assert kb (list 'implies (list 'and (list 'person '?x) (list 'unknown (list 'likes '?x '?z)))
                              (list 'loner '?x))
                     'WellContext))))))

(tu/deftest-kb there-exists-variable-must-be-local
  (tu/with-terms [person foo bar]
    (testing "a quantified variable that escapes its thereExists is refused"
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo #"escapes its quantifier"
           (v/assert kb (list 'implies (list 'and (list 'person '?x) (list 'thereExists '?x (list 'foo '?x)))
                              (list 'bar '?x))
                     'WellContext))))))

;; ---- stratification: no cycle through negation --------------------------

(tu/deftest-kb a-cycle-through-unknown-is-refused
  (tu/with-terms [aa bb cc dd ee]
    (testing "an acyclic NAF rule is accepted"
      (is (v/assert kb (list 'implies (list 'and (list 'aa '?x) (list 'unknown (list 'bb '?x)))
                             (list 'cc '?x))
                    'WellContext)))
    (testing "closing the loop — a rule concluding the NAF predicate — is refused"
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo #"not stratified"
           (v/assert kb (list 'implies (list 'cc '?x) (list 'bb '?x)) 'WellContext))))
    (testing "a one-rule cycle (unknown on what it concludes) is refused"
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo #"not stratified"
           (v/assert kb (list 'implies (list 'and (list 'dd '?x) (list 'unknown (list 'ee '?x)))
                              (list 'ee '?x))
                     'WellContext))))))

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
              'WellContext)
    (v/assert kb (list 'pp Aa) 'WellContext)
    (v/assert kb (list 'pp Bb) 'WellContext)
    (v/assert kb (list 'qq Bb) 'WellContext)
    (testing "the rule forward-derives nothing (it is backward-only)"
      (is (empty? (v/sentexes-matching kb (list 'rr '?x) 'WellContext))))
    (testing "every backward chainer expands the rule and honours the unknown"
      ;; the node engine (`query` at a depth) and the recur DFS must agree
      (doseq [provable? [#(v/query? kb % 'WellContext {:max-depth 2})
                         #(v/provable? kb % 'WellContext)]]
        (is (provable? (list 'rr Aa)) "qq Aa absent -> provable")
        (is (not (provable? (list 'rr Bb))) "qq Bb present -> not provable"))
      (is (= 1 (count (v/prove kb (list 'rr Aa) 'WellContext))))
      (is (= 0 (count (v/prove kb (list 'rr Bb) 'WellContext)))))))

;; ---- prove/backward now evaluate a deferred antecedent ------------------
;; The gap that was: the recursive chainer discharged an antecedent by fact
;; matching + rule expansion only, so a rule with a DEFERRED antecedent (different /
;; evaluate / unknown) proved nothing there — while `ask` and forward chaining honoured
;; it.  A backward-ONLY rule forces the backward path (forward cannot pre-materialize).

(tu/deftest-kb prove-and-backward-honour-every-deferred-antecedent
  (tu/with-terms [rel distinctPair age nextAge Ann Bob Tom]
    ;; `different` — the unique-name test
    (v/assert kb (list rel Ann Bob) 'WellContext)
    (v/assert kb (list rel Ann Ann) 'WellContext)
    (v/assert kb (list 'set/backwardRule
                       (list 'implies (list 'and (list rel '?x '?y) (list 'different '?x '?y))
                             (list distinctPair '?x '?y)))
              'WellContext)
    (testing "different: prove and backward honour it in a backward-only rule"
      (is (v/provable? kb (list distinctPair Ann Bob) 'WellContext))
      (is (not (v/provable? kb (list distinctPair Ann Ann) 'WellContext)))
      (is (= 1 (count (v/prove kb (list distinctPair Ann Bob) 'WellContext))))
      (is (= 0 (count (v/prove kb (list distinctPair Ann Ann) 'WellContext)))))
    ;; `evaluate` — computed, binds its output
    (v/assert kb (list age Tom 40) 'WellContext)
    (v/assert kb (list 'set/backwardRule
                       (list 'implies (list 'and (list age '?p '?n) (list 'evaluate '?next (list '+ '?n 1)))
                             (list nextAge '?p '?next)))
              'WellContext)
    (testing "evaluate: prove checks and backward binds the computed value"
      (is (v/provable? kb (list nextAge Tom 41) 'WellContext))
      (is (not (v/provable? kb (list nextAge Tom 99) 'WellContext)))
      (is (= [41] (map #(get % '?a) (v/prove kb (list nextAge Tom '?a) 'WellContext)))))))

;; ---- belief-sensitivity: unknown reads belief, not mere storage ---------
;; `(unknown S)` holds of an `S` that is stored but currently OUT (a defeated
;; default), because a level-6 match is belief-filtered.  Closed-world negation is
;; about what is *believed*, not what happens to sit in the store.

(tu/deftest-kb unknown-holds-of-a-defeated-default
  (tu/with-terms [happy Zed]
    (v/assert kb (list 'happy Zed) 'WellContext {:strength :default})
    (testing "while believed, it is not unknown"
      (is (not (v/ask? kb (list 'unknown (list 'happy Zed))))))
    ;; a monotonic negation defeats the default: (happy Zed) goes OUT but stays stored
    (v/assert kb (list 'not (list 'happy Zed)) 'WellContext {:strength :monotonic})
    (testing "the default is now stored-but-disbelieved"
      (is (some? (v/handle-of kb (list 'happy Zed) 'WellContext)) "still stored")
      (is (not (v/ask? kb (list 'happy Zed) 'WellContext)) "but not believed"))
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
              'WellContext)
    (v/assert kb (list 'pp Aa) 'WellContext)
    (testing "fires only when BOTH inners are absent"
      (is (v/ask? kb (list 'rr Aa) 'WellContext)))
    (let [h (v/assert kb (list 'ss Aa) 'WellContext)]
      (testing "one inner holding is enough to block"
        (is (not (v/ask? kb (list 'rr Aa) 'WellContext))))
      (v/retract! kb h)
      (testing "and revives when it leaves"
        (is (v/ask? kb (list 'rr Aa) 'WellContext))))))

;; ---- subtype fan-out: the NAF query and its trigger follow genl ---------
;; `(unknown (super ?x))` must be blocked by a `(sub ?x)` fact — the level-6 query
;; fans the functor over its spec closure — and a *later* `sub` fact must trigger a
;; re-check of a rule that only ever mentions `super`.

(tu/deftest-kb unknown-follows-the-subtype-closure
  ;; bound (gensym'd) types/predicates throughout, so `genl`, the rule's NAF query,
  ;; and the subtype fact all name the *same* terms
  (tu/with-terms [sub super pp rr Aa]
    (v/assert kb (list 'genl sub super) 'WellContext)
    (v/assert kb (list 'implies (list 'and (list pp '?x) (list 'unknown (list super '?x)))
                       (list rr '?x))
              'WellContext)
    (v/assert kb (list pp Aa) 'WellContext)
    (testing "with no super/sub membership, it fires"
      (is (v/ask? kb (list rr Aa) 'WellContext)))
    (let [h (v/assert kb (list sub Aa) 'WellContext)]
      (testing "a subtype fact satisfies the supertype NAF query and blocks it"
        (is (not (v/ask? kb (list rr Aa) 'WellContext))
            "(sub Aa) makes (super Aa) derivable, so (unknown (super Aa)) fails"))
      (v/retract! kb h)
      (testing "removing it revives the conclusion"
        (is (v/ask? kb (list rr Aa) 'WellContext))))))

;; ---- context scoping: a fact the conclusion cannot see does not block ---
;; The `unknown` is evaluated in the conclusion's PLACEMENT context, so a fact in a
;; sibling context — one the placement context does not see via genlContext — cannot
;; make its inner derivable.  This is why it is a derive-time check, not a global
;; `?ctx` join filter.

(tu/deftest-kb unknown-respects-the-placement-context
  (tu/with-terms [pp qq rr Aa ParContext SubAContext SubBContext]
    ;; two sibling contexts under a common parent; siblings do not see each other
    (v/assert kb (list 'genlContext SubAContext ParContext) 'WellContext)
    (v/assert kb (list 'genlContext SubBContext ParContext) 'WellContext)
    ;; rule + generator live in SubA, so the conclusion is placed in SubA
    (v/assert kb (list 'implies (list 'and (list 'pp '?x) (list 'unknown (list 'qq '?x)))
                       (list 'rr '?x))
              SubAContext)
    (v/assert kb (list 'pp Aa) SubAContext)
    (testing "the conclusion is derived in SubA"
      (is (v/ask? kb (list 'rr Aa) SubAContext)))
    ;; a qq fact in the *sibling* SubB is invisible from SubA, so it must NOT block
    (let [h (v/assert kb (list 'qq Aa) SubBContext)]
      (testing "a fact in an unseen sibling context does not satisfy the NAF query"
        (is (v/ask? kb (list 'rr Aa) SubAContext)
            "(qq Aa) in SubB is not visible from SubA, so (unknown (qq Aa)) still holds"))
      (v/retract! kb h))
    ;; but a qq fact in SubA itself IS visible, so it blocks
    (let [h (v/assert kb (list 'qq Aa) SubAContext)]
      (testing "a fact in the placement context does block"
        (is (not (v/ask? kb (list 'rr Aa) SubAContext))))
      (v/retract! kb h))))

;; ---- thereExists with a vector of quantified variables ------------------

(tu/deftest-kb there-exists-binds-a-vector-of-variables
  (tu/with-terms [rel Aa Bb]
    (v/assert kb (list 'rel Aa Bb) 'WellContext)
    (testing "a vector binder closes off all its variables"
      (is (= #{} (sx/free-vars (list 'thereExists ['?x '?y] (list 'rel '?x '?y)))))
      (is (v/ask? kb (list 'thereExists ['?x '?y] (list 'rel '?x '?y))))
      (is (not (v/ask? kb (list 'thereExists ['?x '?y] (list 'rel '?x 'NoSuchThing))))))))

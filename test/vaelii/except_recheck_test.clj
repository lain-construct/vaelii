;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.except-recheck-test
  "The **cost** of the `exceptWhen` re-check, and the two correctness properties the
  cost fix is allowed to trade nothing for.

  Nothing about an exception is stored, so it is re-evaluated, and the index that says
  *when* is keyed at rule granularity (docs/exceptions.md, \"The re-check index\").
  Rule granularity is right for the index and far too coarse for the evaluation: a rule
  that has fired N times must not pay N level-6 queries every time a relevant fact
  arrives, and must not be re-joined over the whole fact extent every time a settle
  pass blocks something.  Both were measured quadratic; both are asserted linear here.

  **Counting, not timing.**  These assert the number of level-6 exception evaluations —
  `provers/exception-holds?` calls, counted with `with-redefs` as
  `jtms_blocked_test` and `levels_test` count their own work.  A timing test
  measures the machine; a call count measures the algorithm, and
  the quadratic returning is a change in the count long before it is visible in a
  clock.

  Each test builds its own KB on the **isolated** database pair: it rebuilds in a loop,
  which would clear the shared pair out from under another namespace's `:once`
  fixture."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.provers :as provers]
            [vaelii.test-util :as tu]))

(def ^:private ctx 'CxRecheckCost)

(defn- counting-evaluations
  "Run `f`, returning the number of level-6 exception evaluations it caused."
  [f]
  (let [n    (atom 0)
        orig provers/exception-holds?]
    (with-redefs [provers/exception-holds?
                  (fn [& args] (swap! n inc) (apply orig args))]
      (f))
    @n))

(defn- excepted-rule!
  "`(probe_x ?x) => (seen_x ?x)`, excepted when `(skip_x ?x)`."
  [kb]
  (v/assert kb '(exceptWhen (skip_x ?x)
                            (set/defaultRule (implies (and (probe_x ?x)) (seen_x ?x))))
            ctx))

(defn- probe! [kb i] (v/assert kb (list 'probe_x (symbol (str "PX" i))) ctx))

;; ---- the re-check is not quadratic in a rule's firing count -------------

(deftest re-checking-a-rule-does-not-visit-every-firing-it-ever-made
  (testing "a fact on the exception's predicate re-checks the firings it could reach,
            not every firing the queued rule licensed"
    ;; `firings` live justifications of one excepted rule, then `triggers` facts on
    ;; the exception's predicate about individuals the rule never fired for.  Each
    ;; trigger queues the rule; none of them can block anything.  Visiting every
    ;; firing costs firings×triggers queries, visiting only the reachable ones costs
    ;; none at all.
    (let [cost (fn [firings triggers]
                 (tu/with-cleared-kb [kb tu/isolated-fresh]
                   (excepted-rule! kb)
                   (dotimes [i firings] (probe! kb i))
                   (counting-evaluations
                    #(dotimes [i triggers]
                       (v/assert kb (list 'skip_x (symbol (str "Unrelated" i))) ctx)))))
          few  (cost 8 6)
          many (cost 32 6)]
      ;; the headline: quadrupling the firing count must not move the cost
      (is (<= many (+ 4 (* 2 (max 1 few))))
          (str "re-check cost grew with the rule's firing count: " few " -> " many
               " evaluations for the same 6 triggers"))
      ;; and an absolute bound, so the ratio test cannot be satisfied by both
      ;; readings being large
      (is (< many 32)
          (str "6 triggers that can block nothing cost " many " level-6 queries")))))

(deftest re-checking-a-rule-does-not-visit-every-firing-it-refused
  (testing "a fact on the exception's predicate re-checks the refusals it could reach,
            not every firing the queued rule declined to make"
    ;; The twin of the test above, one level earlier.  A firing refused at derive time is
    ;; recorded (docs/exceptions.md, \"A refused firing is remembered as bindings\") and
    ;; re-evaluated when its rule is queued, so the record is a second population the
    ;; same quadratic can hide in — and the same narrowing has to reach it.  Each trigger
    ;; is about an individual no refusal names, so none of them can release anything.
    (let [cost (fn [refusals triggers]
                 (tu/with-cleared-kb [kb tu/isolated-fresh]
                   (excepted-rule! kb)
                   ;; the exception fact first, so the firing is refused rather than
                   ;; placed and swept
                   (dotimes [i refusals]
                     (v/assert kb (list 'skip_x (symbol (str "PX" i))) ctx)
                     (probe! kb i))
                   (counting-evaluations
                    #(dotimes [i triggers]
                       (v/assert kb (list 'skip_x (symbol (str "Unrelated" i))) ctx)))))
          few  (cost 8 6)
          many (cost 32 6)]
      (is (<= many (+ 4 (* 2 (max 1 few))))
          (str "re-check cost grew with the rule's refusal count: " few " -> " many
               " evaluations for the same 6 triggers"))
      (is (< many 32)
          (str "6 triggers that can release nothing cost " many " level-6 queries")))))

(deftest a-blocked-rule-is-not-re-joined-over-the-whole-fact-extent
  (testing "settling a pass that blocks re-derives what it released, not the rule's
            whole extent"
    ;; A second rule derives the exception for every individual, so every firing is
    ;; blocked and swept.  Re-chaining the blocked rule after each pass re-joins it
    ;; over every fact asserted so far — quadratic — while re-chaining only what the
    ;; pass *released* costs nothing, because this pass released nothing.
    (let [cost (fn [n]
                 (tu/with-cleared-kb [kb tu/isolated-fresh]
                   (excepted-rule! kb)
                   (v/assert kb '(set/defaultRule (implies (and (probe_x ?x)) (skip_x ?x))) ctx)
                   (counting-evaluations #(dotimes [i n] (probe! kb i)))))
          small (cost 10)
          big   (cost 40)]
      ;; linear would be 4x, quadratic 16x; 6x separates them with room for the
      ;; constant term
      (is (< big (* 6 (max 1 small)))
          (str "quadrupling the asserts multiplied the exception evaluations by "
               (double (/ big (max 1 small))) " (" small " -> " big ")")))))

;; ---- what the narrowing must never trade away --------------------------
;;
;; The filter above decides, from memory alone, whether a triggering fact could have
;; flipped a firing's exception.  These two are the cases where the cheap answer is
;; the wrong one, and both are load-bearing: a missed re-check is a conclusion that
;; should have been swept and wasn't, which is a wrong answer, while a spurious one
;; is a wasted query.

(deftest a-fact-at-a-subtype-of-the-exceptions-predicate-still-blocks
  (testing "an exception on a general type is satisfied by a fact at a subtype"
    ;; The trigger's predicate is not the exception's — it is *below* it in the genl
    ;; closure — so any filter comparing the two predicates for equality misses this,
    ;; and it is the common case rather than the exotic one: stating the exception at
    ;; the general type is what the taxonomy is for.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (v/assert kb '(genl xpenguin xflightless) ctx)
      (v/assert kb '(exceptWhen (xflightless ?x)
                                (set/defaultRule (implies (and (xbird ?x)) (xflies ?x))))
                ctx)
      (v/assert kb '(xbird Opus) ctx)
      (is (seq (v/sentexes-matching kb '(xflies Opus) '?ctx))
          "the rule concludes while nothing excepts it")
      (v/assert kb '(xpenguin Opus) ctx)
      (is (empty? (v/sentexes-matching kb '(xflies Opus) '?ctx))
          "a penguin fact satisfies the flightless exception through the genl closure"))))

(deftest a-genl-edge-change-still-re-checks-every-firing
  (testing "a taxonomy edge carries no triggering fact, so it re-checks everything"
    ;; Nothing arrives whose predicate the exception mentions — the *closure* moves —
    ;; so this is the path the narrowing deliberately does not apply to.  It is also
    ;; the path a filter keyed on triggering sentences would silently drop.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (v/assert kb '(exceptWhen (xflightless ?x)
                                (set/defaultRule (implies (and (xbird ?x)) (xflies ?x))))
                ctx)
      (v/assert kb '(xbird Tweety) ctx)
      (v/assert kb '(xpenguin Tweety) ctx)
      (is (seq (v/sentexes-matching kb '(xflies Tweety) '?ctx))
          "a penguin is not yet flightless: no edge relates the types")
      (v/assert kb '(genl xpenguin xflightless) ctx)
      (is (empty? (v/sentexes-matching kb '(xflies Tweety) '?ctx))
          "the edge makes the exception hold, and the conclusion is swept"))))

(deftest a-genlCx-edge-rechecks-only-the-exceptions-in-its-cone
  (testing "a genlCx edge outside every excepted rule's placement cone re-checks
            none of them, instead of the whole excepted-rule roster"
    ;; A genlCx edge changes what contexts *see*, so it can flip an exception —
    ;; but only one evaluated in a context the edge's `sub` reaches (`context-down`).
    ;; An edge in an unrelated context cone re-checks nothing, where the old blanket
    ;; re-checked every fired excepted rule.  Counted, not timed: the blanket's cost is
    ;; one level-6 query per fired excepted rule, the narrowing's is none.
    (let [cost (fn [n-rules]
                 (tu/with-cleared-kb [kb tu/isolated-fresh]
                   ;; n distinct excepted rules, each fired once in `ctx` (a conclusion each)
                   (dotimes [i n-rules]
                     (let [p (symbol (str "cprobe" i)) s (symbol (str "cseen" i))
                           k (symbol (str "cskip" i))]
                       (v/assert kb (list 'exceptWhen (list k '?x)
                                          (list 'set/defaultRule
                                                (list 'implies (list 'and (list p '?x)) (list s '?x))))
                                 ctx)
                       (v/assert kb (list p (symbol (str "CI" i))) ctx)))
                   ;; a fresh genlCx edge whose cone (context-down of its sub) does
                   ;; not reach `ctx`, so no fired exception is in it
                   (counting-evaluations
                    #(v/assert kb '(genlCx CxFarSub CxFarSuper)
                               'CxUniverse {:strength :monotonic}))))
          few  (cost 5)
          many (cost 20)]
      (is (= 0 few many)
          (str "an out-of-cone genlCx edge re-checked exceptions instead of "
               "narrowing to its cone: " few " (5 rules) / " many " (20 rules)")))))

(deftest a-released-exception-is-still-re-derived
  (testing "retracting what the exception rested on brings the conclusion back"
    ;; The counterpart to the cost fix: narrowing the re-chain to what a pass released
    ;; must not stop a genuine release from being re-derived.  Revival under
    ;; `exceptWhen` is a re-derivation, not a flipped bit, so this is a real chaining
    ;; run and not a relabel.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (excepted-rule! kb)
      (v/assert kb '(probe_x PX0) ctx)
      (is (seq (v/sentexes-matching kb '(seen_x PX0) '?ctx)) "concluded while unexcepted")
      (let [h (v/assert kb '(skip_x PX0) ctx)]
        (is (empty? (v/sentexes-matching kb '(seen_x PX0) '?ctx)) "blocked and swept")
        (v/retract! kb h)
        (is (seq (v/sentexes-matching kb '(seen_x PX0) '?ctx))
            "the released exception is re-derived by the time retract! returns")))))

;; ---- the choke points: every mutation path posts the re-check -----------
;;
;; exceptWhen correctness depends on every path that stores or removes a sentex
;; posting to the re-check queue.  That contract is now two choke points in
;; `vaelii.impl.integrate` (`sentex-added` / `sentex-removed!`) plus the
;; derivation-path twin in `vaelii.impl.special`, and these tests pin one mutation
;; path per choke: a *derived* arrival (chaining), a *derived* departure through
;; `retract!`'s teardown, and a departure through the excepted-conclusion sweep
;; inside `settle` itself.  Each would silently leave a stale conclusion (or a
;; missing revival) if its path forgot to post — which is exactly the bug class the
;; choke points exist to make unwritable.

(deftest a-derived-fact-triggers-the-re-check
  (testing "an exception satisfied only by inference still blocks: the derived fact
            is a re-check trigger like an asserted one"
    ;; skip_x never arrives as a premise — a second rule concludes it — so the
    ;; trigger must come from the derivation path's choke point.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (excepted-rule! kb)
      (v/assert kb '(set/forwardRule (implies (and (mark_x ?x)) (skip_x ?x))) ctx)
      (v/assert kb '(probe_x PX0) ctx)
      (is (seq (v/sentexes-matching kb '(seen_x PX0) '?ctx)) "concluded while nothing excepts it")
      (v/assert kb '(mark_x PX0) ctx)          ; skip_x PX0 arrives by derivation only
      (is (seq (v/sentexes-matching kb '(skip_x PX0) '?ctx)) "the exception fact was derived")
      (is (empty? (v/sentexes-matching kb '(seen_x PX0) '?ctx))
          "the derived exception blocked the rule and its conclusion was swept"))))

(deftest a-retraction-triggers-the-re-check
  (testing "a fact leaving through retract!'s teardown is a re-check trigger: the
            swept derived exception releases the rule"
    ;; The exception fact is itself derived, so retracting its premise removes it
    ;; through retract!'s removal loop — the removal choke point.  Without the
    ;; posting there, nothing re-chains the released rule and seen_x never appears.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (excepted-rule! kb)
      (v/assert kb '(set/forwardRule (implies (and (mark_x ?x)) (skip_x ?x))) ctx)
      (let [h (v/assert kb '(mark_x PX0) ctx)] ; skip_x PX0 derived before the firing
        (v/assert kb '(probe_x PX0) ctx)
        (is (empty? (v/sentexes-matching kb '(seen_x PX0) '?ctx)) "blocked while the exception holds")
        (v/retract! kb h)                      ; mark_x goes; skip_x is swept with it
        (is (empty? (v/sentexes-matching kb '(skip_x PX0) '?ctx)) "the derived exception fell away")
        (is (seq (v/sentexes-matching kb '(seen_x PX0) '?ctx))
            "the exception's departure re-chained the rule by the time retract! returned")))))

(deftest a-sweep-triggers-the-re-check
  (testing "a conclusion deleted by the exception sweep is itself a trigger: its
            departure releases the rule it was blocking"
    ;; Two excepted rules in a chain: probe_x ⇒ skip_x (except lift_x) and
    ;; probe_x ⇒ seen_x (except skip_x).  Lifting the first sweeps skip_x *inside
    ;; settle*, and that deletion — the sweep's own teardown, not an assert or a
    ;; retract — must release the second rule within the same fixpoint.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (excepted-rule! kb)
      (v/assert kb '(exceptWhen (lift_x ?x)
                                (set/defaultRule (implies (and (probe_x ?x)) (skip_x ?x))))
                ctx)
      (v/assert kb '(probe_x PX0) ctx)
      (is (seq (v/sentexes-matching kb '(skip_x PX0) '?ctx)) "the exception fact is derived")
      (is (empty? (v/sentexes-matching kb '(seen_x PX0) '?ctx)) "and blocks the seen_x rule")
      (v/assert kb '(lift_x PX0) ctx)
      (is (empty? (v/sentexes-matching kb '(skip_x PX0) '?ctx)) "the lift blocks skip_x, which is swept")
      (is (seq (v/sentexes-matching kb '(seen_x PX0) '?ctx))
          "the swept exception released seen_x inside the same settle"))))

;; ---- the genl edge trigger is narrowed to the closures it moves ----------
;;
;; Queueing *every* excepted rule with `:all` on a `genl` / `genlCx` edge change
;; makes taxonomy churn re-evaluate (and re-chain) whole extents of rules whose
;; exceptions the edge could not possibly move.  The genl trigger is therefore
;; keyed by the edge's supertype closure: only rules whose exception is registered
;; at or above the edge's supertype — plus the closure-reading functors `genl` and
;; `disjoint`, whose provers answer across arguments and so cannot be keyed on a
;; predicate at all — are queued.  A **negated** conjunct registers under `not`, which
;; hides the predicate it is about, and is keyed on the edge's *subtype* closure
;; instead (`special/recheck-negated-exceptions`).  (`genlCx` keeps the blanket: a
;; visibility edge changes what every exception can see, which no predicate key can
;; narrow.)

(deftest a-genl-edge-re-checks-only-what-its-closure-touches
  (testing "the touched rule's conclusion is swept; the untouched rule's firings are
            not even re-evaluated"
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      ;; touched: excepts on tall_thing, one firing.  untouched: excepts on skip_x,
      ;; twenty firings — under the old blanket trigger those twenty dominate.
      (v/assert kb '(exceptWhen (tall_thing ?x)
                                (set/defaultRule (implies (and (probe_a ?x)) (big_a ?x))))
                ctx)
      (excepted-rule! kb)
      (dotimes [i 20] (probe! kb i))
      (v/assert kb '(probe_a PA1) ctx)
      (v/assert kb '(giant_thing PA1) ctx)
      (is (seq (v/sentexes-matching kb '(big_a PA1) '?ctx)) "no edge yet: a giant is not yet tall")
      (let [n (counting-evaluations
               #(v/assert kb '(genl giant_thing tall_thing) ctx))]
        (is (empty? (v/sentexes-matching kb '(big_a PA1) '?ctx))
            "the edge reaches the tall_thing exception, so the touched rule is queued
             and its conclusion swept — narrowing must never skip an affected rule")
        (is (= 20 (count (v/sentexes-matching kb '(seen_x ?x) '?ctx)))
            "the untouched rule's conclusions all stand")
        (is (< n 10)
            (str "the edge caused " n " exception evaluations; the untouched rule's "
                 "20 firings must not be among them (the blanket trigger paid 40+)"))))))

;; ---- and the negated conjunct, which registers under a functor that hides it ----
;;
;; `(exceptWhen (not (has_wings ?x)) …)` is ordinary common-sense content, and it
;; registers in the re-check index under the functor `not` rather than under
;; `has_wings` — so the supertype keying above cannot see which predicate it is about
;; and cannot decide it.  Waving every such rule through costs `:all`, which is one
;; level-6 query per firing the rule ever made, on every `genl` edge written anywhere.
;;
;; A ground negation is answered from stored negative sentexes with no genl fan-out, so
;; no edge flips one today.  The wave-through is kept anyway, against contravariant
;; negative matching: reading `(not (dog X))` off a stored `(not (animal X))` walks the
;; **up**-closure of the conjunct's own predicate, and an edge `[sub super]` moves that
;; closure for exactly the predicates at or below `sub`.  So the keying is the edge's
;; subtype closure — the contravariant twin of the supertype walk beside it.  The two
;; tests are the two halves of that claim: outside the moved closure it costs nothing,
;; inside it the rule is still queued.

(defn- negated-exception-cost
  "Level-6 evaluations caused by asserting `(genl <sub> negsuper_t)` on a KB whose one
  excepted rule has fired `firings` times, excepted when `(not (<pred> ?x))` holds."
  [firings sub pred]
  (tu/with-cleared-kb [kb tu/isolated-fresh]
    (v/assert kb (list 'exceptWhen (list 'not (list pred '?x))
                       '(set/defaultRule (implies (and (neg_probe ?x)) (neg_seen ?x))))
              ctx)
    (dotimes [i firings] (v/assert kb (list 'neg_probe (symbol (str "NG" i))) ctx))
    (counting-evaluations
     #(v/assert kb (list 'genl sub 'negsuper_t) ctx {:strength :monotonic}))))

(deftest a-genl-edge-does-not-re-check-a-negation-whose-closure-it-left-alone
  (testing "an edge under a subtype no negated conjunct names re-checks none of that
            rule's firings, however many it made"
    ;; The edge's `sub` is a fresh type; the negated conjunct is about `negskip`, whose
    ;; up-closure the edge did not move.  Nothing the level-6 stack can read about
    ;; `(not (negskip X))` changed, so nothing is queued — and, crucially, the cost does
    ;; not track the rule's firing history.
    (let [few  (negated-exception-cost 8  'negvictim_t 'negskip)
          many (negated-exception-cost 32 'negvictim_t 'negskip)]
      (is (= 0 few many)
          (str "an unrelated genl edge re-evaluated a negated exception's firings: "
               few " (8 firings) / " many " (32 firings)")))))

(deftest a-genl-edge-under-a-negations-own-predicate-still-re-checks-it
  (testing "the wave-through is kept where a contravariant reading could reach: an
            edge whose subtype *is* the negated conjunct's predicate queues the rule"
    ;; The half the narrowing must not trade.  `(genl negskip negsuper_t)` moves
    ;; `genls(negskip)`, which is the closure a contravariant negative match would read
    ;; to answer `(not (negskip X))` off a stored negative sentex at a supertype.  The
    ;; rule is queued, and queued unconditionally, so every firing is re-decided.
    (let [n (negated-exception-cost 8 'negskip 'negskip)]
      (is (= 8 n)
          (str "an edge on the negated conjunct's own predicate re-checked " n
               " of 8 firings; the defensive wave-through must keep all of them")))))

(deftest a-negated-exception-still-blocks-and-releases
  (testing "narrowing the edge trigger changes nothing about what a negation excepts"
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (v/assert kb '(exceptWhen (not (negskip ?x))
                                (set/defaultRule (implies (and (neg_probe ?x)) (neg_seen ?x))))
                ctx)
      (v/assert kb '(neg_probe NG0) ctx)
      (is (seq (v/sentexes-matching kb '(neg_seen NG0) '?ctx))
          "nothing denies negskip of NG0, so the exception does not hold")
      (let [h (v/assert kb '(not (negskip NG0)) ctx)]
        (is (empty? (v/sentexes-matching kb '(neg_seen NG0) '?ctx))
            "the stored negation satisfies the exception and the conclusion is swept")
        (v/retract! kb h)
        (is (seq (v/sentexes-matching kb '(neg_seen NG0) '?ctx))
            "and its departure releases the rule")))))

;; ---- the two channels a fact reaches an exception through sideways -------
;;
;; Both of these move a level-6 exception answer without the arriving fact agreeing with
;; the exception conjunct on a single argument, and one of them without agreeing on the
;; predicate either — so the index's genls keying and the narrowing's argument-agreement
;; test are each blind to one of them on their own.  Each is a settled-belief question
;; disguised as a cost one: the firings that predate the fact keep a conclusion the
;; firings after it correctly drop, so without the trigger *belief depends on arrival
;; order*, which is the invariant docs/nmtms.md opens with.  Both directions are pinned,
;; and so is the arrival order that already worked.

(deftest a-preserved-argument-position-still-withdraws-the-conclusion
  (testing "a claim stated at the supertypes satisfies an exception written at the subtypes"
    ;; `(transitiveInArg bigger n genl)` makes a stored `(bigger dog cat)` answer
    ;; `(bigger poodle siamese)` — `TransitiveInArgProver` walks the *arguments'* reach, so
    ;; the trigger and the conjunct share no argument at all and the argument-agreement
    ;; filter drops the firing unless preservation waves it through.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (v/assert kb '(transitiveInArg pbigger 1 genl) ctx)
      (v/assert kb '(transitiveInArg pbigger 2 genl) ctx)
      (v/assert kb '(genl ppoodle pdog) ctx)
      (v/assert kb '(genl psiamese pcat) ctx)
      (v/assert kb '(exceptWhen (pbigger ppoodle psiamese)
                                (set/defaultRule (implies (and (pmark ?x)) (pseen ?x))))
                ctx)
      (v/assert kb '(pmark PM1) ctx)
      (is (seq (v/sentexes-matching kb '(pseen PM1) '?ctx))
          "fires while nothing excepts it")
      (v/assert kb '(pbigger pdog pcat) ctx)
      (is (v/ask? kb '(pbigger ppoodle psiamese) ctx)
          "the claim is inherited down to the subtypes")
      (is (empty? (v/sentexes-matching kb '(pseen PM1) '?ctx))
          "so the exception holds and the conclusion is swept"))))

(deftest a-preserved-argument-position-still-releases-the-conclusion
  (testing "and removing the inherited claim brings the conclusion back"
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (v/assert kb '(transitiveInArg pbigger 1 genl) ctx)
      (v/assert kb '(transitiveInArg pbigger 2 genl) ctx)
      (v/assert kb '(genl ppoodle pdog) ctx)
      (v/assert kb '(genl psiamese pcat) ctx)
      (v/assert kb '(exceptWhen (pbigger ppoodle psiamese)
                                (set/defaultRule (implies (and (pmark ?x)) (pseen ?x))))
                ctx)
      (v/assert kb '(pbigger pdog pcat) ctx)
      (v/assert kb '(pmark PM1) ctx)
      (is (empty? (v/sentexes-matching kb '(pseen PM1) '?ctx))
          "the exception holds at firing time, so nothing is concluded")
      (v/retract! kb (v/handle-of kb '(pbigger pdog pcat) ctx))
      (is (not (v/ask? kb '(pbigger ppoodle psiamese) ctx)))
      (is (seq (v/sentexes-matching kb '(pseen PM1) '?ctx))
          "the release is a re-derivation, and it happens"))))

(deftest an-argisa-inferred-type-still-withdraws-the-conclusion
  (testing "a fact on an arg-constrained predicate satisfies an exception on the
            declared type"
    ;; `arg` read as an inference rather than as a constraint (`ArgTypeProver`): a
    ;; believed `(motherOf X …)` beside `(arg motherOf 1 mammal)` makes X a mammal,
    ;; with nothing on `mammal` written and no genl path from `motherOf` to it — so the
    ;; index's own keying cannot reach the rule.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (v/assert kb '(arg amotherOf 1 amammal) ctx)
      (v/assert kb '(exceptWhen (amammal AMuffet)
                                (set/defaultRule (implies (and (amark ?x)) (aseen ?x))))
                ctx)
      (v/assert kb '(amark AM1) ctx)
      (is (seq (v/sentexes-matching kb '(aseen AM1) '?ctx))
          "fires while nothing excepts it")
      (v/assert kb '(amotherOf AMuffet ARex) ctx)
      (is (v/ask? kb '(amammal AMuffet) ctx)
          "the usage types the individual")
      (is (empty? (v/sentexes-matching kb '(aseen AM1) '?ctx))
          "so the exception holds and the conclusion is swept"))))

(deftest an-argisa-declaration-arriving-after-the-facts-still-withdraws
  (testing "the other arrival order: the facts first, then the declaration that types them"
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (v/assert kb '(exceptWhen (amammal AMuffet)
                                (set/defaultRule (implies (and (amark ?x)) (aseen ?x))))
                ctx)
      (v/assert kb '(amotherOf AMuffet ARex) ctx)
      (v/assert kb '(amark AM1) ctx)
      (is (seq (v/sentexes-matching kb '(aseen AM1) '?ctx))
          "nothing types AMuffet yet")
      (v/assert kb '(arg amotherOf 1 amammal) ctx)
      (is (v/ask? kb '(amammal AMuffet) ctx))
      (is (empty? (v/sentexes-matching kb '(aseen AM1) '?ctx))
          "the declaration reaches the fact that was already stored"))))

(deftest an-argisa-inferred-type-still-releases-the-conclusion
  (testing "and retracting the typing fact releases the exception"
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (v/assert kb '(arg amotherOf 1 amammal) ctx)
      (v/assert kb '(exceptWhen (amammal AMuffet)
                                (set/defaultRule (implies (and (amark ?x)) (aseen ?x))))
                ctx)
      (v/assert kb '(amotherOf AMuffet ARex) ctx)
      (v/assert kb '(amark AM1) ctx)
      (is (empty? (v/sentexes-matching kb '(aseen AM1) '?ctx)))
      (v/retract! kb (v/handle-of kb '(amotherOf AMuffet ARex) ctx))
      (is (not (v/ask? kb '(amammal AMuffet) ctx)))
      (is (seq (v/sentexes-matching kb '(aseen AM1) '?ctx))
          "nothing types AMuffet any more, so the conclusion is re-derived"))))

;; ---- the third channel: a declaration, not a fact -----------------------
;;
;; The two above move an exception's answer with a *fact* the keying cannot reach.  A
;; **declaration** moves it with no fact at all: the extent of every predicate is
;; exactly what it was, and what changed is what may be concluded from it.
;; `(symmetric sibOf)` makes a stored `(sibOf Ann Bob)` answer `(sibOf Bob Ann)`;
;; `(transitive partOf)` closes a chain; `(inverse childOf parentOf)` answers a goal
;; from the partner predicate's facts; `(transitiveInArg P n R)` opens the inheritance
;; and `(asymmetric P)` is what gives a converse the standing to close it again.
;;
;; None of those sentences is *on* the predicate the exception is written over, so the
;; index's genls keying misses every one.  That is the same settled-belief question the
;; section above is: the firings that predate the declaration keep a conclusion the
;; firings after it correctly drop, and which you get depends on when the declaration
;; arrived.  Each is pinned in the direction its own arrival moves belief, plus the
;; withdrawal that reverses one.

(deftest a-symmetry-declaration-arriving-late-still-withdraws-the-conclusion
  (testing "(symmetric P) makes a stored fact answer its own mirror"
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (v/assert kb '(exceptWhen (ssibOf SBob SAnn)
                                (set/defaultRule (implies (and (smark ?x)) (sseen ?x))))
                ctx)
      (v/assert kb '(ssibOf SAnn SBob) ctx)
      (v/assert kb '(smark SM1) ctx)
      (is (seq (v/sentexes-matching kb '(sseen SM1) '?ctx))
          "the mirror is not answered while nothing says the predicate is symmetric")
      (v/assert kb '(symmetric ssibOf) ctx)
      (is (v/ask? kb '(ssibOf SBob SAnn) ctx)
          "the declaration answers it from the fact that was already stored")
      (is (empty? (v/sentexes-matching kb '(sseen SM1) '?ctx))
          "so the exception holds and the conclusion is swept"))))

(deftest a-transitivity-declaration-arriving-late-still-withdraws-the-conclusion
  (testing "(transitive P) closes a chain that was already stored"
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (v/assert kb '(exceptWhen (tpartOf TPiston TCar)
                                (set/defaultRule (implies (and (tmark ?x)) (tseen ?x))))
                ctx)
      (v/assert kb '(tpartOf TPiston TEngine) ctx)
      (v/assert kb '(tpartOf TEngine TCar) ctx)
      (v/assert kb '(tmark TM1) ctx)
      (is (seq (v/sentexes-matching kb '(tseen TM1) '?ctx))
          "two hops are two facts until somebody says they compose")
      (v/assert kb '(transitive tpartOf) ctx)
      (is (v/ask? kb '(tpartOf TPiston TCar) ctx))
      (is (empty? (v/sentexes-matching kb '(tseen TM1) '?ctx))
          "so the exception holds and the conclusion is swept"))))

(deftest a-reflexivity-declaration-arriving-late-still-withdraws-the-conclusion
  (testing "(reflexive P) answers a self-pair nobody wrote"
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (v/assert kb '(exceptWhen (rlikes RBob RBob)
                                (set/defaultRule (implies (and (rmark ?x)) (rseen ?x))))
                ctx)
      (v/assert kb '(rlikes RAnn RAnn) ctx)
      (v/assert kb '(rmark RM1) ctx)
      (is (seq (v/sentexes-matching kb '(rseen RM1) '?ctx)))
      (v/assert kb '(reflexive rlikes) ctx)
      (is (v/ask? kb '(rlikes RBob RBob) ctx))
      (is (empty? (v/sentexes-matching kb '(rseen RM1) '?ctx))
          "so the exception holds and the conclusion is swept"))))

(deftest an-inverse-declaration-arriving-late-still-withdraws-the-conclusion
  (testing "(inverse P Q) answers a goal on P from Q's facts, so *both* names move"
    ;; The one declaration naming two predicates.  The exception is written over the
    ;; predicate that has no facts of its own, and the declaration is what connects it
    ;; to the one that does.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (v/assert kb '(exceptWhen (ichildOf IBob IAnn)
                                (set/defaultRule (implies (and (imark ?x)) (iseen ?x))))
                ctx)
      (v/assert kb '(iparentOf IAnn IBob) ctx)
      (v/assert kb '(imark IM1) ctx)
      (is (seq (v/sentexes-matching kb '(iseen IM1) '?ctx))
          "nothing connects the two predicates yet")
      (v/assert kb '(inverse ichildOf iparentOf) ctx)
      (is (v/ask? kb '(ichildOf IBob IAnn) ctx))
      (is (empty? (v/sentexes-matching kb '(iseen IM1) '?ctx))
          "so the exception holds and the conclusion is swept"))))

(deftest a-preservation-declaration-arriving-late-still-withdraws-the-conclusion
  (testing "(transitiveInArg P n R) opens the inheritance over facts already stored"
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (v/assert kb '(genl gpoodle gdog) ctx)
      (v/assert kb '(genl gsiamese gcat) ctx)
      (v/assert kb '(gbigger gdog gcat) ctx)
      (v/assert kb '(exceptWhen (gbigger gpoodle gsiamese)
                                (set/defaultRule (implies (and (gmark ?x)) (gseen ?x))))
                ctx)
      (v/assert kb '(gmark GM1) ctx)
      (is (seq (v/sentexes-matching kb '(gseen GM1) '?ctx))
          "the claim about the supertypes reaches nothing until it is declared to")
      (v/assert kb '(transitiveInArg gbigger 1 genl) ctx)
      (v/assert kb '(transitiveInArg gbigger 2 genl) ctx)
      (is (v/ask? kb '(gbigger gpoodle gsiamese) ctx))
      (is (empty? (v/sentexes-matching kb '(gseen GM1) '?ctx))
          "so the exception holds and the conclusion is swept"))))

(deftest an-asymmetry-declaration-arriving-late-moves-the-exceptions-answer
  (testing "(asymmetric P) gives the converse the standing to undercut"
    ;; The one that moves the answer the other way.  `(nbigger nmc nchi)` is a claim the
    ;; general `(nbigger ndog ncat)` reaches past, and it is inert until the predicate is
    ;; declared asymmetric — only then does it count as evidence *against* the pair the
    ;; general claim inherits, and undercut it.
    ;;
    ;; Both firings are asserted: the one made after the declaration, and the one that
    ;; predates it — refused at derive time, so in no blocked set for a release to be
    ;; read off, and re-derived from its recorded refusal instead
    ;; (refused_firing_test, and docs/exceptions.md).
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (v/assert kb '(genl nchi ndog) ctx)
      (v/assert kb '(genl nmc ncat) ctx)
      (v/assert kb '(transitiveInArg nbigger 1 genl) ctx)
      (v/assert kb '(transitiveInArg nbigger 2 genl) ctx)
      (v/assert kb '(nbigger ndog ncat) ctx)
      (v/assert kb '(nbigger nmc nchi) ctx)
      (v/assert kb '(exceptWhen (nbigger nchi nmc)
                                (set/defaultRule (implies (and (nmark ?x)) (nseen ?x))))
                ctx)
      (v/assert kb '(nmark NM1) ctx)
      (is (v/ask? kb '(nbigger nchi nmc) ctx)
          "the general claim reaches the pair, and nothing yet disputes it")
      (is (empty? (v/sentexes-matching kb '(nseen NM1) '?ctx))
          "so the firing is refused at derive time")
      (v/assert kb '(asymmetric nbigger) ctx)
      (is (not (v/ask? kb '(nbigger nchi nmc) ctx))
          "the specific converse now undercuts the general claim")
      (is (seq (v/sentexes-matching kb '(nseen NM1) '?ctx))
          "so the refused firing is re-derived from what it recorded")
      (v/assert kb '(nmark NM2) ctx)
      (is (seq (v/sentexes-matching kb '(nseen NM2) '?ctx))
          "and a firing made after the declaration is not blocked"))))

(deftest withdrawing-a-transitivity-releases-the-inheritance-it-licensed
  (testing "(transitive R) is also the licence every (transitiveInArg P n R) reads at use"
    ;; The indirect one, and the reason `transitive` gets a second posting: nothing
    ;; here mentions `wneeds_oil` except the declaration, and retracting the *relation's*
    ;; transitivity is what stops its reach from closing.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (v/assert kb '(transitive wpartOf) ctx)
      (v/assert kb '(wpartOf WPiston WEngine) ctx)
      (v/assert kb '(wpartOf WEngine WCar) ctx)
      (v/assert kb '(transitiveInArg wneeds_oil 1 wpartOf) ctx)
      (v/assert kb '(wneeds_oil WCar) ctx)
      (v/assert kb '(exceptWhen (wneeds_oil WPiston)
                                (set/defaultRule (implies (and (wmark ?x)) (wseen ?x))))
                ctx)
      (v/assert kb '(wmark WM1) ctx)
      (is (v/ask? kb '(wneeds_oil WPiston) ctx)
          "two hops of a transitive relation, so the claim reaches the piston")
      (is (empty? (v/sentexes-matching kb '(wseen WM1) '?ctx))
          "the exception holds at firing time, so nothing is concluded")
      (v/retract! kb (v/handle-of kb '(transitive wpartOf) ctx))
      (is (not (v/ask? kb '(wneeds_oil WPiston) ctx))
          "a relation nobody says composes is one whose reach may not be closed")
      (is (seq (v/sentexes-matching kb '(wseen WM1) '?ctx))
          "so the exception is released and the conclusion comes back"))))

(deftest a-declaration-does-not-re-check-a-kb-that-declares-no-exception
  (testing "the declaration channel is gated on some rule carrying an exceptWhen"
    ;; Same shape as the arg gate below it: the trigger has to be free for the KB
    ;; that does not use it.  Declarations arriving beside n standing firings of an
    ;; *unexcepted* rule must cost no level-6 evaluations at all.
    (let [cost (fn [n]
                 (tu/with-cleared-kb [kb tu/isolated-fresh]
                   (v/assert kb '(set/defaultRule
                                  (implies (and (dmark ?x)) (dseen ?x)))
                             ctx)
                   (dotimes [i 20] (v/assert kb (list 'dmark (symbol (str "DM" i))) ctx))
                   (counting-evaluations
                    #(dotimes [i n]
                       (v/assert kb (list 'symmetric (symbol (str "dpred" i))) ctx)))))]
      (is (= 0 (cost 5) (cost 40))
          "a declaration re-checked exceptions on a KB that has none"))))

;; ---- the channel that moves no fact at all: the equality closure --------
;;
;; A merge is not a fact arriving or leaving.  It moves what a level-6 condition sees in
;; two ways nothing else does — it **retires a spelling**, so a sentex is gone from every
;; belief-filtered read while still stored and still holding its handle, and it
;; **rewrites the question**, so a condition spelled with a retired term is answered
;; under the representative.  The second is why this channel cannot be keyed on a
;; predicate the way `recheck-genl-edge` is: nothing on the condition's own predicate
;; moves at all.  As above, both directions, and the arrival order that already worked.

;; `rewriteOf` rather than `sameAs` throughout, because the *direction* is the whole
;; point.  A merge elects a representative by content, so with `sameAs` the surviving
;; spelling is whichever name sorts first — and if that is the one the counterexample
;; fact is stored under, the fact migrates and the migration posts an ordinary
;; predicate-keyed trigger, which hides the channel under test.  `(rewriteOf Kept
;; Retired)` names the loser, so the counterexample fact stays exactly where it is and
;; nothing arrives on the exception's own predicate at all.

(defn- merge-rule!
  "`(mmark ?x) => (mseen ?x)`, excepted when `(mskip ?x)`."
  [kb]
  (v/assert kb '(exceptWhen (mskip ?x)
                            (set/defaultRule (implies (and (mmark ?x)) (mseen ?x))))
            ctx))

(deftest a-merge-that-makes-an-exception-hold-withdraws-the-conclusion
  (testing "an exception satisfied only under the firing's representative still blocks"
    ;; `(mskip MTwo)` is stored and the rule fires for `MOne`, so the exception is false.
    ;; The merge retires `MOne` in favour of `MTwo`: the firing's own binding is now a
    ;; spelling the KB does not answer under, and the conjunct it feeds is `(mskip MTwo)`
    ;; — which holds.  Nothing on `mskip` moved.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (merge-rule! kb)
      (v/assert kb '(mskip MTwo) ctx)
      (v/assert kb '(mmark MOne) ctx)
      (is (seq (v/sentexes-matching kb '(mseen ?x) ctx))
          "fires while nothing excepts MOne")
      (let [h (v/assert kb '(rewriteOf MTwo MOne) ctx)]
        (is (= '["(mskip MTwo)"]
               (mapv #(pr-str (:sentence %)) (v/sentexes-matching kb '(mskip ?x) ctx)))
            "and the exception's own predicate is untouched by the merge")
        (is (empty? (v/sentexes-matching kb '(mseen ?x) ctx))
            "so the exception holds and the conclusion is swept, under either spelling")
        (testing "and splitting the class again releases it"
          (v/retract! kb h)
          (is (seq (v/sentexes-matching kb '(mseen MOne) ctx))
              "the release is a re-derivation, and it happens"))))))

(deftest the-merge-arriving-first-reaches-the-same-belief
  (testing "the order that never needed a trigger still agrees with the one that does"
    ;; The point of the test above: this order is the oracle.  Nothing here is keyed on a
    ;; trigger at all — the firing is refused at derive time — so if the merged-last KB
    ;; disagrees with this one, belief depends on arrival order.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (v/assert kb '(rewriteOf MTwo MOne) ctx)
      (merge-rule! kb)
      (v/assert kb '(mskip MTwo) ctx)
      (v/assert kb '(mmark MOne) ctx)
      (is (empty? (v/sentexes-matching kb '(mseen ?x) ctx))
          "merged first, the rule never concludes"))))

(deftest the-exception-fact-arriving-after-the-merge-reaches-the-same-belief
  (testing "a trigger spelled under the representative reaches a firing bound to the
            retired spelling"
    ;; The third order.  The rule fires for `MOne` with nothing excepting it, the merge
    ;; retires `MOne` in favour of `MTwo` (the exception is still false, so the firing
    ;; stands and is twinned under the representative), and only then does `(mskip
    ;; MTwo)` arrive.  That trigger is keyed on `mskip` and narrowed by argument
    ;; shape: the firing's *stored* binding is `MOne`, its re-check asks about `MTwo`,
    ;; and the two orders above agree that the answer is no conclusion at all.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (merge-rule! kb)
      (v/assert kb '(mmark MOne) ctx)
      (v/assert kb '(rewriteOf MTwo MOne) ctx)
      (is (= '["(mseen MTwo)"]
             (mapv #(pr-str (:sentence %)) (v/sentexes-matching kb '(mseen ?x) ctx)))
          "fires, and the merge re-spells the conclusion under the representative")
      (v/assert kb '(mskip MTwo) ctx)
      (is (empty? (v/sentexes-matching kb '(mseen ?x) ctx))
          "the exception holds under the firing's settled binding, so it is swept")
      (is (empty? (v/sentexes-matching kb '(mseen ?x) '?c))
          "under either spelling, in any context"))))

;; ---- and every one of the 24 orders, not the three written out above ----
;;
;; A block condition is decided three times over — at derive time, from a trigger, and
;; off a refusal record — and a merge can arrive before, between or after each part of
;; the knowledge.  So the property is about the whole permutation set rather than about
;; a path, and the sweeps below run all 24 orderings of four assertions and require them
;; to agree.  They differ in *where* the retired spelling sits: in the firing's binding,
;; in the condition's own constant, and inside an `(unknown …)`.  The third is the one
;; whose wrong answer is a conclusion drawn rather than one withheld — an `unknown`
;; reporting a term absent when it has an answer under its representative is unsound,
;; where a silent exception merely fails to guard.

(defn- orderings
  "Every ordering of `coll` — a small local permutation, since the sweeps below are over
  four assertions and the suite carries no combinatorics dependency."
  [coll]
  (if (empty? coll)
    [[]]
    (mapcat (fn [x] (map #(vec (cons x %)) (orderings (remove #{x} coll)))) coll)))

(defn- belief-per-order
  "`{belief [order …]}` over every ordering of `ops` — a map of assertion thunks — with
  `read` taking the belief once each order has been asserted into its own cleared KB."
  [ops read]
  (reduce (fn [acc order]
            (tu/with-cleared-kb [kb tu/isolated-fresh]
              (doseq [k order] ((get ops k) kb))
              (update acc (read kb) (fnil conj []) order)))
          {}
          (orderings (keys ops))))

(defn- one-belief!
  "Assert that every ordering of `ops` reaches `expected`, naming the orders that did
  not when one does not."
  [label ops read expected]
  (let [outcome (belief-per-order ops read)]
    ;; the key set, so a failure prints the beliefs that disagreed rather than 24
    ;; orderings twice over; the message carries the tally and the divergent orders
    (is (= #{expected} (set (keys outcome)))
        (str label ": belief depends on arrival order — "
             (pr-str (into {} (map (fn [[b os]] [b (count os)])) outcome))
             ", the divergent orders being "
             (pr-str (mapcat val (dissoc outcome expected)))))))

(deftest every-arrival-order-of-a-merge-reaches-one-belief
  (testing "the firing's own binding is the retired spelling"
    ;; `(mskip MOne)` is asserted under the retired spelling and canonicalized at the
    ;; door, the rule binds `?x` to `MOne`, and the exception has to be asked under the
    ;; representative wherever the merge lands in the order.
    (one-belief! "a bound term"
                 {:rule  #(merge-rule! %)
                  :mark  #(v/assert % '(mmark MOne) ctx)
                  :merge #(v/assert % '(rewriteOf MTwo MOne) ctx)
                  :skip  #(v/assert % '(mskip MOne) ctx)}
                 #(mapv :sentence (v/sentexes-matching % '(mseen ?x) '?c))
                 []))
  (testing "the exception conjunct's own constant is the retired spelling"
    ;; Nothing the firing binds has merged at all: what moved is a term the *rule* was
    ;; written with, and a rule is held back from an individual-only rewrite migration,
    ;; so the stored condition keeps naming `BOne` for good.
    (one-belief! "a conjunct constant"
                 {:rule  #(v/assert % '(exceptWhen (bskip BOne)
                                                   (set/defaultRule
                                                    (implies (and (bmark ?x)) (bseen ?x))))
                                    ctx)
                  :mark  #(v/assert % '(bmark BM1) ctx)
                  :merge #(v/assert % '(rewriteOf BTwo BOne) ctx)
                  :fact  #(v/assert % '(bskip BTwo) ctx)}
                 #(mapv :sentence (v/sentexes-matching % '(bseen ?x) '?c))
                 []))
  (testing "a firing's own binding, in the polarity where the wrong answer is unsound"
    ;; `(unknown (yskip ?x))` asked under the stored binding is answered *absent* about a
    ;; term the KB answers under its representative, so the rule concludes where it must
    ;; not — where a silently-false exception merely fails to guard.
    (one-belief! "a naf inner query"
                 {:rule  #(v/assert % '(set/defaultRule
                                        (implies (and (ymark ?x) (unknown (yskip ?x)))
                                                 (yseen ?x)))
                                    ctx)
                  :mark  #(v/assert % '(ymark YOne) ctx)
                  :merge #(v/assert % '(rewriteOf YTwo YOne) ctx)
                  :fact  #(v/assert % '(yskip YOne) ctx)}
                 #(mapv :sentence (v/sentexes-matching % '(yseen ?x) '?c))
                 [])))

(deftest a-merged-binding-does-not-re-check-every-firing-a-rule-ever-made
  (testing "a trigger that can block nothing costs no level-6 query, merges or not"
    ;; The narrowing compares the firing's stored bindings with the trigger, and both
    ;; sides are read under the representative — so a KB whose every firing bound a
    ;; merged term narrows exactly as one that merged nothing.  Waving a merged binding
    ;; through instead costs one level-6 query per firing per arriving fact, and on an
    ;; `owl:sameAs`-style import the partition is most of the individuals.
    (let [cost (fn [merged?]
                 (tu/with-cleared-kb [kb tu/isolated-fresh]
                   (excepted-rule! kb)
                   (dotimes [i 20]
                     (probe! kb i)
                     (when merged?
                       (v/assert kb (list 'rewriteOf (symbol (str "PY" i))
                                          (symbol (str "PX" i)))
                                 ctx)))
                   [(counting-evaluations
                     #(v/assert kb '(skip_x Unrelated0) ctx))
                    (count (v/sentexes-matching kb '(seen_x ?x) '?c))]))]
      (is (= [0 20] (cost false)) "20 firings, one unrelated trigger, nothing merged")
      (is (= [0 20] (cost true))
          "the same trigger re-checked every firing because each bound a merged term"))))

(deftest a-genlCx-edge-retakes-a-census-with-no-firing-to-key-on
  (testing "an aggregate rule is exempt from the placement-cone narrowing"
    ;; The narrowing above reads where a rule's firings were *placed*, which is sound for
    ;; every condition that blocks: what a widened cone can change always has a firing to
    ;; be found.  An aggregate binds a value, so a census that rises licenses a firing
    ;; that never existed — there is no placed conclusion to read a context off, and the
    ;; rule is skipped unless it is waved through.
    (let [belief (fn [edge-last?]
                   (tu/with-cleared-kb [kb tu/isolated-fresh]
                     ;; both under the rule's own context, so a firing has somewhere to
                     ;; be placed; the edge under test is the one between them
                     (v/assert kb (list 'genlCx 'CxGSub ctx) ctx
                               {:strength :monotonic})
                     (v/assert kb (list 'genlCx 'CxGUp ctx) ctx
                               {:strength :monotonic})
                     (when-not edge-last?
                       (v/assert kb '(genlCx CxGSub CxGUp) ctx
                                 {:strength :monotonic}))
                     (v/assert kb '(gperson GAnn) 'CxGSub)
                     (v/assert kb '(implies (and (gperson ?x)
                                                 (agg/count ?n ?c (gchildOf ?x ?c))
                                                 (lessThan 2 ?n))
                                            (glarge_family ?x))
                               ctx)
                     (doseq [c '[GC1 GC2 GC3]]
                       (v/assert kb (list 'gchildOf 'GAnn c) 'CxGUp))
                     (when edge-last?
                       (v/assert kb '(genlCx CxGSub CxGUp) ctx
                                 {:strength :monotonic}))
                     (mapv :sentence (v/sentexes-matching kb '(glarge_family ?x)
                                                          'CxGSub))))]
      (is (= '[(glarge_family GAnn)] (belief false))
          "with the edge in place the census sees three children and the rule fires")
      (is (= (belief false) (belief true))
          "and the edge arriving last reaches the same belief"))))

(deftest an-exception-on-an-undeclared-type-is-not-re-checked-by-every-fact
  (testing "the arg channel is keyed on the declaration, not on every fact there is"
    ;; The trigger has to be free for the KB that does not use it, or it is a per-assert
    ;; tax on every load.  n facts of a predicate nothing declares an arg for must
    ;; cost no exception evaluations at all, however many firings are standing.
    (let [cost (fn [n]
                 (tu/with-cleared-kb [kb tu/isolated-fresh]
                   (v/assert kb '(exceptWhen (uskip_thing UOne)
                                             (set/defaultRule
                                              (implies (and (umark ?x)) (useen ?x))))
                             ctx)
                   (dotimes [i 20] (v/assert kb (list 'umark (symbol (str "UM" i))) ctx))
                   (counting-evaluations
                    #(dotimes [i n]
                       (v/assert kb (list 'uplain (symbol (str "UP" i)) 'UVal) ctx)))))]
      (is (= 0 (cost 5) (cost 40))
          "a fact on an unconstrained predicate re-checked exceptions anyway"))))

(deftest an-exception-that-is-itself-a-query-operator-is-watched-by-what-it-reads
  (testing "the re-check key is the predicate the query reads, not the operator's own"
    ;; `exceptWhen`'s query is any closed level-6 goal, so it may be a query *operator* —
    ;; an `unknown`, a `thereExists`, an aggregate.  Keyed on the operator's own functor
    ;; the rule is registered under a predicate no sentex ever carries, so no arriving
    ;; fact can queue it: the exception is evaluated correctly once and re-evaluated
    ;; never, which from the outside is a guard that answers whatever happened first.
    ;;
    ;; Both directions matter and only one of them is visible without a trigger: the
    ;; *initial* answer needs no re-check, so a rule that never fires looks right for the
    ;; wrong reason.  What proves the key is the release — the fact arriving that makes
    ;; the inner query derivable, so the `unknown` goes false and the exception stops
    ;; holding.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (v/assert kb '(exceptWhen (unknown (and (qskip ?x) (rskip ?x)))
                                (set/defaultRule (implies (and (qmark ?x)) (qseen ?x))))
                ctx)
      (v/assert kb '(qmark QOne) ctx)
      (is (empty? (v/sentexes-matching kb '(qseen ?x) ctx))
          "neither conjunct is derivable, so the unknown holds and the exception blocks")
      (v/assert kb '(qskip QOne) ctx)
      (is (empty? (v/sentexes-matching kb '(qseen ?x) ctx))
          "one conjunct short — the inner conjunction still is not derivable")
      (v/assert kb '(rskip QOne) ctx)
      (is (seq (v/sentexes-matching kb '(qseen QOne) ctx))
          "the second conjunct completes it, so the unknown is false and the rule fires")
      (testing "and retracting it blocks again, the release being re-decided each time"
        (v/retract! kb (v/handle-of kb '(rskip QOne) ctx))
        (is (empty? (v/sentexes-matching kb '(qseen ?x) ctx)))))))

(deftest a-cycle-through-an-exception-that-is-a-query-operator-is-refused
  (testing "the negative edge runs to what the exception reads, so the cycle is seen"
    ;; The stratification graph reads the same keys.  An exception that is an
    ;; `(unknown S)` is a negative dependency on `S`'s predicate; keyed on `unknown` —
    ;; which nothing concludes — the graph reaches no rule and refuses nothing.
    (tu/with-cleared-kb [kb tu/isolated-fresh]
      (v/assert kb '(exceptWhen (unknown (cskip ?x))
                                (set/defaultRule (implies (and (cmark ?x)) (cseen ?x))))
                ctx)
      (is (thrown-with-msg?
           clojure.lang.ExceptionInfo #"not stratified"
           (v/assert kb '(implies (cseen ?x) (cskip ?x)) ctx))))))

(deftest a-query-operator-exception-narrows-like-a-flat-one
  (testing "an (unknown S) exception is narrowed to the firings the trigger can reach"
    ;; The narrowing substitutes the firing's bindings into each block literal and asks
    ;; whether a trigger could answer it.  A literal that is not flat and ground has no
    ;; shape to test, so it is kept — the safe direction, and for an exception that *is*
    ;; a query operator it keeps everything: `(unknown (qskip_x PX7))` reads as unshaped
    ;; however specific it is, so every firing is re-decided on every arriving fact and
    ;; the cost is the rule's whole history per trigger.
    ;;
    ;; The frames are peeled for the narrowing exactly as they are for the index key, so
    ;; the literal tested is the one the query reads and the shape test bites again.
    ;; Same claim, same shape, same bound as the flat case above.
    (let [cost (fn [firings triggers]
                 (tu/with-cleared-kb [kb tu/isolated-fresh]
                   (v/assert kb '(exceptWhen (unknown (qskip_x ?x))
                                             (set/defaultRule
                                              (implies (and (qprobe_x ?x)) (qseen_x ?x))))
                             ctx)
                   (dotimes [i firings]
                     (v/assert kb (list 'qprobe_x (symbol (str "QX" i))) ctx))
                   (counting-evaluations
                    #(dotimes [i triggers]
                       (v/assert kb (list 'qskip_x (symbol (str "Unrelated" i))) ctx)))))
          few  (cost 8 6)
          many (cost 32 6)]
      (is (<= many (+ 4 (* 2 (max 1 few))))
          (str "re-check cost grew with the rule's firing count: " few " -> " many
               " evaluations for the same 6 triggers"))
      (is (< many 32)
          (str "6 triggers that can block nothing cost " many " level-6 queries")))))

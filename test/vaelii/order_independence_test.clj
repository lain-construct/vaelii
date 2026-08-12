;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.order-independence-test
  "The engine-wide invariant: **the same knowledge, given in any order, yields the
  same beliefs.**

  This is not a nice-to-have. A common-sense KB learns generalities and specifics in
  whatever order the world supplies them — 'birds fly' before or after 'Tweety is a
  penguin' — and an engine whose answers depend on that order is answering a
  question nobody asked.

  These tests enumerate *every* permutation of a scenario's assertions and demand a
  single distinct outcome. They are the regression net for the region-local
  relabelling in `vaelii.impl.jtms`: a local fixpoint is only legitimate because it
  agrees with the global one, and disagreement shows up here as an order-dependent
  answer.

  Note what a weaker test would have missed. The Nixon-diamond case once asserted
  only that *exactly one* side won — which is true under every order even when the
  winner flips. It passed while the engine was order-dependent, because the tie-break
  keyed on handle id and handles are allocated in assertion order (see
  `vaelii.impl.solve/content-key`). Demanding the *identical reading* every time is
  what catches that, and it is why `observe` returns a map compared as a whole rather
  than a boolean per ordering.

  The Nixon diamond has no winner to be stable about: two rules concluding `P` and
  `¬P` with neither naming the other's case is a **represented dilemma**, so both
  sides stay believed and the pair is reported by `contradictions`
  (docs/exceptions.md, \"What surfaces where\"). The expected outcome is therefore
  \"both always coexist, and exactly one dilemma is always reported\" rather than
  \"the same one side always wins\". The dilemma count is in
  `observe` deliberately: a report that appeared under some orderings and not others,
  or that double-counted a pair, is precisely the order-dependence this file exists to
  catch, and it would be invisible to a belief-only reading."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(defn- permutations [coll]
  (if (<= (count coll) 1)
    (list (seq coll))
    (for [i (range (count coll))
          p (permutations (concat (take i coll) (drop (inc i) coll)))]
      (cons (nth coll i) p))))

(defn- default-rule [antes conseq]
  (list 'set/defaultRule (list 'implies (cons 'and antes) conseq)))

(defn- run-ops
  "Apply `ops` to a freshly cleared KB and return `observe`'s reading of it."
  [ops observe]
  (let [kb (tu/fresh)]
    (doseq [op ops] (op kb))
    (observe kb)))

(defn- outcomes
  "The set of distinct outcomes over every ordering of `ops`."
  [ops observe]
  (into #{} (map #(run-ops % observe)) (permutations ops)))

(defn- one-outcome!
  "Assert that every ordering of `ops` agrees, and return the single outcome."
  [label ops observe]
  (let [os (outcomes ops observe)]
    (is (= 1 (count os))
        (str label ": " (count os) " distinct outcomes across "
             (count (permutations ops)) " orderings — " (pr-str os)))
    (first os)))

;; ---- defaults and their exceptions --------------------------------------

(deftest penguin-cascade-is-order-independent
  ;; 5 assertions, 120 orderings. The default may fire before or after the KB learns
  ;; Tweety is a penguin, before or after it learns penguins are birds at all.
  (let [ops [#(v/assert % (default-rule '[(bird ?x)] '(flies ?x)) 'CxUniverse)
             #(v/assert-rule % '[(penguin ?x)] '(not (flies ?x)) 'CxUniverse)
             #(v/assert % '(genl penguin bird) 'CxUniverse)
             ;; Known-true: a bare rule confers :monotonic and is capped by its weakest
             ;; antecedent, so over this premise the exception concludes :monotonic and
             ;; out-ranks the :default flight rule.  Over a :default premise both sides
             ;; would tie at :default and the pair would be a represented dilemma.
             #(v/assert % '(penguin Tweety) 'CxUniverse {:strength :monotonic})
             #(v/assert % '(bird Robin) 'CxUniverse)]
        observe (fn [kb]
                  {:tweety-flies (boolean (seq (v/sentexes-matching kb '(flies Tweety) 'CxUniverse)))
                   :tweety-grounded (boolean (seq (v/sentexes-matching kb '(not (flies Tweety)) 'CxUniverse)))
                   :robin-flies (boolean (seq (v/sentexes-matching kb '(flies Robin) 'CxUniverse)))
                   :conflicts (count (v/conflicts kb))})
        result (one-outcome! "penguin cascade" ops observe)]
    (testing "and the one outcome is the common-sense one"
      (is (false? (:tweety-flies result)))
      (is (true? (:tweety-grounded result)))
      (is (true? (:robin-flies result)))                ; the exception is not contagious
      (is (zero? (:conflicts result))))
    (tu/clear-kb! (tu/test-kb))))

(deftest exceptwhen-is-order-independent
  ;; The exception is a belief-following meta-sentex split off from the rule, so the
  ;; exceptWhen may arrive before its facts (blocking the firing at derive time) or
  ;; after them (sweeping a conclusion that already fired).  Both must settle to the
  ;; same belief, forward *and* backward — the whole point of the block/sweep machinery
  ;; being order-independent.  24 orderings.
  (let [ops [#(v/assert % '(exceptWhen (penguin ?x)
                                       (set/defaultRule (implies (and (bird ?x)) (flies ?x))))
                        'CxUniverse)
             #(v/assert % '(penguin Tweety) 'CxUniverse)
             #(v/assert % '(bird Tweety) 'CxUniverse)
             #(v/assert % '(bird Robin) 'CxUniverse)]
        observe (fn [kb]
                  {:tweety-query (boolean (seq (v/sentexes-matching kb '(flies Tweety) 'CxUniverse)))
                   :tweety-ask   (v/ask? kb '(flies Tweety) 'CxUniverse)
                   :robin-query  (boolean (seq (v/sentexes-matching kb '(flies Robin) 'CxUniverse)))
                   :conflicts    (count (v/conflicts kb))})
        result (one-outcome! "exceptWhen" ops observe)]
    (testing "the excepted binding never flies, forward or backward; the other does"
      (is (false? (:tweety-query result)))
      (is (false? (:tweety-ask result)))
      (is (true? (:robin-query result)))
      (is (zero? (:conflicts result))))
    (tu/clear-kb! (tu/test-kb))))

(deftest two-independent-exceptions-are-order-independent
  ;; Two exceptWhens on the *same* rule (block-if-either), asserted separately, amend
  ;; the one rule.  Every ordering of the two exceptions, the two triggers, and the
  ;; plain fact must ground each excepted bird and let the plain one fly.  6 items would
  ;; be 720 orderings; a diverse handful pins the interesting ones (exceptions before
  ;; and after their triggers, interleaved) without the runtime.
  (doseq [order [[:r1 :r2 :fp :tp :fo :to :fr]
                 [:fp :fo :fr :tp :to :r1 :r2]
                 [:r1 :fp :tp :r2 :fo :to :fr]
                 [:fr :tp :r2 :fo :fp :r1 :to]
                 [:tp :to :fr :fp :fo :r2 :r1]]]
    (let [kb (tu/fresh)
          op {:r1 #(v/assert kb '(exceptWhen (penguin ?x)
                                             (set/defaultRule (implies (and (bird ?x)) (flies ?x))))
                             'CxUniverse)
              :r2 #(v/assert kb '(exceptWhen (ostrich ?x)
                                             (set/defaultRule (implies (and (bird ?x)) (flies ?x))))
                             'CxUniverse)
              :fp #(v/assert kb '(bird Pengu) 'CxUniverse)
              :tp #(v/assert kb '(penguin Pengu) 'CxUniverse)
              :fo #(v/assert kb '(bird Ostri) 'CxUniverse)
              :to #(v/assert kb '(ostrich Ostri) 'CxUniverse)
              :fr #(v/assert kb '(bird Robby) 'CxUniverse)}]
      (doseq [k order] ((op k)))
      (is (empty? (v/sentexes-matching kb '(flies Pengu) 'CxUniverse)) (str order " penguin flies"))
      (is (empty? (v/sentexes-matching kb '(flies Ostri) 'CxUniverse)) (str order " ostrich flies"))
      (is (seq (v/sentexes-matching kb '(flies Robby) 'CxUniverse)) (str order " robin grounded"))
      (tu/clear-kb! kb))))

(deftest a-default-feeding-a-bare-rule-is-order-independent
  ;; The downstream conclusion (canTravel) must track the defeat of its antecedent
  ;; whichever order the pieces arrive in.
  (let [ops [#(v/assert % (default-rule '[(bird ?x)] '(flies ?x)) 'CxUniverse)
             #(v/assert-rule % '[(flies ?x)] '(canTravel ?x) 'CxUniverse)
             #(v/assert-rule % '[(penguin ?x)] '(not (flies ?x)) 'CxUniverse)
             #(v/assert % '(genl penguin bird) 'CxUniverse)
             ;; known-true, so the exception concludes :monotonic and defeats the default
             #(v/assert % '(penguin Tweety) 'CxUniverse {:strength :monotonic})]
        observe (fn [kb]
                  {:flies (boolean (seq (v/sentexes-matching kb '(flies Tweety) 'CxUniverse)))
                   :travels (boolean (seq (v/sentexes-matching kb '(canTravel Tweety) 'CxUniverse)))})
        result (one-outcome! "default feeding a bare rule" ops observe)]
    (testing "a defeated antecedent withdraws the conclusion built on it"
      (is (false? (:flies result)))
      (is (false? (:travels result))))
    (tu/clear-kb! (tu/test-kb))))

;; ---- the represented dilemma --------------------------------------------

(deftest nixon-diamond-is-the-same-dilemma-every-time
  ;; Two equally-specific defaults collide with no strength and no specificity to
  ;; separate them, and neither rule names the other's case. The engine declines to
  ;; decide that: both sides stay believed and the pair is reported by
  ;; `contradictions`. What must not vary with typing order is the whole reading —
  ;; which sides are believed, that neither was defeated, and that exactly one dilemma
  ;; is reported.
  (let [ops [#(v/assert % (default-rule '[(quaker ?x)] '(pacifist ?x)) 'CxUniverse)
             #(v/assert % (default-rule '[(republican ?x)] '(not (pacifist ?x))) 'CxUniverse)
             #(v/assert % '(quaker Nixon) 'CxUniverse)
             #(v/assert % '(republican Nixon) 'CxUniverse)]
        observe (fn [kb]
                  (let [pos (v/handle-of kb '(pacifist Nixon) 'CxUniverse)
                        neg (v/handle-of kb '(not (pacifist Nixon)) 'CxUniverse)]
                    {:pacifist (boolean (seq (v/sentexes-matching kb '(pacifist Nixon) 'CxUniverse)))
                     :not-pacifist (boolean (seq (v/sentexes-matching kb '(not (pacifist Nixon)) 'CxUniverse)))
                     ;; the defeat-classes, not the handles: handles are allocated in
                     ;; assertion order, so putting one in the reading would make every
                     ;; ordering differ for a reason that is not about belief.  Keyed
                     ;; positive-then-negative, so a defeated or missing side reads as
                     ;; nil in its own slot rather than vanishing into a set.
                     :classes [(v/defeat-class kb pos) (v/defeat-class kb neg)]
                     :contradictions (count (v/contradictions kb))
                     :conflicts (count (v/conflicts kb))}))
        result (one-outcome! "nixon diamond" ops observe)]
    (testing "both sides are believed — the dilemma is represented, not decided"
      (is (true? (:pacifist result)))
      (is (true? (:not-pacifist result))))
    (testing "and neither was defeated — both still stand at :default"
      (is (= [:default :default] (:classes result))))
    (testing "the pair is reported once as a dilemma, not as a conflict"
      (is (= 1 (:contradictions result)))
      (is (zero? (:conflicts result))))
    (tu/clear-kb! (tu/test-kb))))

(deftest the-reported-lists-are-content-ordered-not-arrival-ordered
  ;; The count being stable is not enough, and the two tests above only check counts.
  ;; `settle` stores both readings in arrival order — they come off a hash set of
  ;; handle-keyed nogoods — and `settle/ranked`, called by `conflicts` and by
  ;; `contradictions`, is the whole of what makes the *list* an answer about the
  ;; knowledge.  A reader that stops calling it puts `(first (contradictions kb))` at
  ;; the mercy of which pair was typed first, which no count would notice.  So these
  ;; observe the sequence, not its length.
  ;;
  ;; `clash_oracle_test/the-contradictions-list-is-ordered-by-content-not-arrival` makes
  ;; the same claim for `contradictions` over two hand-written orders; this one covers
  ;; `conflicts` as well and takes every ordering rather than two.
  ;;
  ;; **Three readers call `ranked`, so three arms.**  `preview`'s `:contradictions` is the
  ;; third and the one a count could never catch: its own test reads the field through a
  ;; `set`, which is order-blind on purpose, so dropping the call there would have failed
  ;; nothing.
  ;;
  ;; Three independent pairs, one op each: the pairs share no term, so nothing but the
  ;; ordering rule decides which report leads.  Six orderings.
  (let [pair    (fn [p strength]
                  #(do (v/assert % (list p 'OrderedSubject) 'CxUniverse strength)
                       (v/assert % (list 'not (list p 'OrderedSubject))
                                 'CxUniverse strength)))
        ;; the sort key is each side's sentence, so the predicate name is what orders
        ;; one report against another — named so that content order and any arrival
        ;; order are different questions
        preds   '[ordGamma ordAlpha ordBeta]
        reading (fn [reports]
                  (mapv #(-> % :sides first :sentence pr-str) reports))]
    (testing "contradictions — three represented dilemmas at :default"
      (let [result (one-outcome! "dilemma list ordering"
                                 (mapv #(pair % {}) preds)
                                 (fn [kb] {:order (reading (v/contradictions kb))}))]
        (is (= 3 (count (:order result))) "all three pairs are reported")
        (is (= (sort (:order result)) (:order result))
            "the list is in content order, so no ordering can put a different one first")))
    (testing "conflicts — the same claim for the irreducible :monotonic reading"
      (let [result (one-outcome! "conflict list ordering"
                                 (mapv #(pair % {:strength :monotonic}) preds)
                                 (fn [kb] {:order (reading (v/conflicts kb))}))]
        (is (= 3 (count (:order result))) "all three pairs are reported")
        (is (= (sort (:order result)) (:order result))
            "the list is in content order, so no ordering can put a different one first")))
    (testing "preview — the dilemmas a batch would open, read the same way"
      ;; Here the KB carries only the positives, in every order, and one fixed batch
      ;; opens all three dilemmas at once.  So the batch cannot be what varies: what
      ;; varies is the arrival order of the facts the reports are built from, which is
      ;; exactly what the stored vector is in and exactly what `ranked` has to remove.
      (let [result (one-outcome!
                    "preview dilemma list ordering"
                    (mapv (fn [p] #(v/assert % (list p 'OrderedSubject) 'CxUniverse {}))
                          preds)
                    (fn [kb]
                      {:order (reading
                               (:contradictions
                                (v/preview kb {:add (mapv (fn [p]
                                                            [(list 'not (list p 'OrderedSubject))
                                                             'CxUniverse {}])
                                                          preds)})))}))]
        (is (= 3 (count (:order result))) "the batch opens all three")
        (is (= (sort (:order result)) (:order result))
            "the previewed list is in content order too, and by the same call")))
    (tu/clear-kb! (tu/test-kb))))

;; ---- retraction and revival ---------------------------------------------

(deftest revival-is-order-independent
  ;; Build the default in either order, defeat it, then retract the defeater. The
  ;; conclusion must come back in both cases — belief is recomputed, not replayed.
  (doseq [build [[#(v/assert % (default-rule '[(bird ?x)] '(flies ?x)) 'CxUniverse)
                  #(v/assert % '(bird Sky) 'CxUniverse)]
                 [#(v/assert % '(bird Sky) 'CxUniverse)
                  #(v/assert % (default-rule '[(bird ?x)] '(flies ?x)) 'CxUniverse)]]]
    (let [kb (tu/fresh)]
      (doseq [op build] (op kb))
      (is (seq (v/sentexes-matching kb '(flies Sky) 'CxUniverse)) "the default holds")
      (let [neg (v/assert kb '(not (flies Sky)) 'CxUniverse {:strength :monotonic})]
        (is (empty? (v/sentexes-matching kb '(flies Sky) 'CxUniverse)) "defeated")
        (v/retract! kb neg)
        (is (seq (v/sentexes-matching kb '(flies Sky) 'CxUniverse)) "revived"))))
  (tu/clear-kb! (tu/test-kb)))

(deftest a-revival-that-owes-a-derivation-is-order-independent
  ;; The revival above only had to *relabel*: the conclusion was still stored, so
  ;; recomputing belief brought it back.  This one owes a **derivation**.  A rule joins
  ;; two facts, one is defeated, and the other arrives while it is OUT — so the join runs
  ;; against a belief-filtered matcher that cannot see the defeated half and no firing is
  ;; ever attempted.  Lifting the defeat then moves a label and leaves nothing behind for
  ;; a blocked set or a refusal record to read, so the conclusion exists only if the
  ;; revived datum went back on the agenda (`vaelii.revived-datum-test`).
  ;;
  ;; Not `one-outcome!`, because these ops do not permute freely: a lift cannot precede
  ;; the defeat it lifts, and tying the two together as one op would remove the very
  ;; window this is about — the partner arriving *between* them.  So the three ordered
  ;; steps are held in sequence and the two free ops are slid through every position they
  ;; have: the partner into each of the 4 gaps, and the rule into each of the 5 gaps of
  ;; what that leaves.  Twenty orderings, and the ones where the partner lands in the
  ;; middle are the defect.
  (let [assert-a  #(v/assert % '(vpA VOne VTwo) 'CxUniverse)
        defeat-a  #(v/assert % '(not (vpA VOne VTwo)) 'CxUniverse
                             {:strength :monotonic})
        lift-a    #(v/retract! % (v/handle-of % '(not (vpA VOne VTwo)) 'CxUniverse))
        partner   #(v/assert % '(vpB VTwo VThree) 'CxUniverse {:strength :monotonic})
        rule      #(v/assert-rule % '[(vpA ?x ?z) (vpB ?z ?y)] '(vpC ?x ?y) 'CxUniverse
                                  {:direction :forward})
        insert    (fn [ops i op] (vec (concat (take i ops) [op] (drop i ops))))
        observe   (fn [kb]
                    {:joined     (boolean (seq (v/sentexes-matching kb '(vpC VOne VThree)
                                                                    'CxUniverse)))
                     :antecedent (boolean (seq (v/sentexes-matching kb '(vpA VOne VTwo)
                                                                    'CxUniverse)))})
        outcomes  (into {}
                        (for [p (range 4)
                              r (range 5)
                              :let [ops (insert (insert [assert-a defeat-a lift-a] p partner)
                                                r rule)
                                    kb  (tu/fresh)]]
                          (do (doseq [op ops] (op kb))
                              [[p r] (observe kb)])))]
    (is (= #{{:joined true :antecedent true}} (into #{} (vals outcomes)))
        (str "a fact that comes back believed must derive what it could not while it was "
             "OUT, in every order — " (pr-str (into (sorted-map) outcomes)))))
  (tu/clear-kb! (tu/test-kb)))

(deftest an-un-merge-that-owes-a-derivation-is-order-independent
  ;; The same claim as the test above through the **equality** door, which reaches it by
  ;; a different route and has to: a merge displaces a spelling with no relabel behind
  ;; it, so the flip is in none of the window sets a revival is read off.  While the
  ;; merge stands the twin joins in the displaced spelling's place, so a partner arriving
  ;; then concludes at the twin — and un-merging sweeps the twin and gives the original
  ;; back, leaving the conclusion to be derived again at the surviving spelling or not at
  ;; all.  Mechanism and the second merge route: `vaelii.revived-datum-test`.
  ;;
  ;; Same shape as its sibling: the ordered steps held in sequence, the two free ops slid
  ;; through every gap they have.  The orderings where the partner lands between the
  ;; merge and the un-merge are the defect.
  (let [fact      #(v/assert % '(uqA UDep UZed) 'CxUniverse {:strength :monotonic})
        merge-it  #(v/assert % '(rewriteOf UPref UDep) 'CxUniverse
                             {:strength :monotonic})
        un-merge  #(v/retract! % (v/handle-of % '(rewriteOf UPref UDep) 'CxUniverse))
        partner   #(v/assert % '(uqB UZed UWye) 'CxUniverse {:strength :monotonic})
        rule      #(v/assert-rule % '[(uqA ?x ?z) (uqB ?z ?y)] '(uqC ?x ?y)
                                  'CxUniverse {:direction :forward})
        insert    (fn [ops i op] (vec (concat (take i ops) [op] (drop i ops))))
        observe   (fn [kb]
                    {:conclusions (set (map :sentence
                                            (v/sentexes-matching kb '(uqC ?x ?y)
                                                                 'CxUniverse)))
                     :antecedent  (boolean (seq (v/sentexes-matching kb '(uqA UDep UZed)
                                                                     'CxUniverse)))})
        outcomes  (into {}
                        (for [p (range 4)
                              r (range 5)
                              :let [ops (insert (insert [fact merge-it un-merge] p partner)
                                                r rule)
                                    kb  (tu/fresh)]]
                          (do (doseq [op ops] (op kb))
                              [[p r] (observe kb)])))]
    (is (= #{{:conclusions #{'(uqC UDep UWye)} :antecedent true}}
           (into #{} (vals outcomes)))
        (str "a spelling an un-merge gives back must derive what its twin could not, in "
             "every order — " (pr-str (into (sorted-map) outcomes)))))
  (tu/clear-kb! (tu/test-kb)))

;; ---- the taxonomy caches follow suit ------------------------------------

(deftest genl-closure-is-order-independent
  ;; The cached closures are derived state, so they must land in the same place
  ;; whatever order the edges and their defeater arrive in.
  (let [ops [#(v/assert % '(genl sub_t mid_t) 'CxUniverse)
             #(v/assert % '(genl mid_t super_t) 'CxUniverse)
             #(v/assert % '(sub_t Ind1) 'CxUniverse)]
        observe (fn [kb] {:isa (v/isa? kb 'Ind1 'super_t)})]
    (is (= #{{:isa true}} (outcomes ops observe))
        "transitive membership does not depend on which edge was asserted first"))
  (tu/clear-kb! (tu/test-kb)))

(deftest a-firing-that-subsumes-is-order-independent
  ;; The closure landing in the same place is not enough: matching fans an antecedent
  ;; over its spec closure, so a `genl` edge changes which antecedents the *stored*
  ;; facts satisfy.  The arriving datum is the edge, and firing the rules keyed on
  ;; `genl` is not the same thing as re-firing the rules the edge just connected — so
  ;; without `special/subsumption-seeds` these four sentences derive `(breathes Muffet)`
  ;; in the orders that put the edge before the fact and nothing in the others.
  (let [ops [#(v/assert % '(genl animal_t thing) 'CxUniverse)
             #(v/assert % '(genl dog_t animal_t) 'CxUniverse)
             #(v/assert % '(implies (animal_t ?x) (breathes ?x)) 'CxUniverse)
             #(v/assert % '(dog_t Muffet) 'CxUniverse)]
        observe (fn [kb]
                  {:derived (boolean (seq (v/sentexes-matching kb '(breathes Muffet) 'CxUniverse)))})]
    (is (= {:derived true} (one-outcome! "subsumption firing" ops observe))
        "and the one outcome is the conclusion, not the silence"))
  (tu/clear-kb! (tu/test-kb)))

(deftest a-firing-that-sees-across-a-context-edge-is-order-independent
  ;; The same claim for the other closure, and the same gap.  Matching fans an
  ;; antecedent up the *visibility* cone, so a `genlCx` edge changes which facts a
  ;; stored rule can see — and the arriving datum is again the edge, so firing the rules
  ;; keyed on `genlCx` is not the same thing as re-joining the rules the edge just
  ;; gave a wider view.  Without `special/visibility-seeds` these four sentences derive
  ;; `(vSeenP VA)` in the 17 orders that put the edge before the rule or the fact, and
  ;; nothing in the other 7.
  (let [ops [#(v/assert % '(genlCx CxVMid CxUniverse) 'CxUniverse)
             #(v/assert % '(genlCx CxVLow CxVMid) 'CxUniverse)
             #(v/assert % '(vFactP VA) 'CxVMid)
             #(v/assert % '(implies (vFactP ?x) (vSeenP ?x)) 'CxVLow)]
        observe (fn [kb]
                  {:derived (boolean (seq (v/sentexes-matching kb '(vSeenP VA) 'CxVLow)))})]
    (is (= {:derived true} (one-outcome! "visibility firing" ops observe))
        "a rule fires off what its context can see, whenever it was told it could"))
  (tu/clear-kb! (tu/test-kb)))

(deftest a-rule-above-fires-on-the-facts-of-a-context-newly-wired-under-it
  ;; the other direction of the same edge, and the one that survives a fix taking only
  ;; the first: a rule stated *above* applies in every context that sees it, so wiring a
  ;; new context under it hands the rule that context's own facts and places
  ;; the conclusion there.  Seeding is by fact, so it has to reach both cones.
  (let [ops [#(v/assert % '(genlCx CxXMid CxUniverse) 'CxUniverse)
             #(v/assert % '(genlCx CxXLow CxXMid) 'CxUniverse)
             #(v/assert % '(xFactP XB) 'CxXLow)
             #(v/assert % '(implies (xFactP ?x) (xSeenP ?x)) 'CxXMid)]
        observe (fn [kb]
                  {:derived (boolean (seq (v/sentexes-matching kb '(xSeenP XB) 'CxXLow)))})]
    (is (= {:derived true} (one-outcome! "inherited-rule firing" ops observe))
        "a rule above is inherited into a context wired under it, whenever that happened"))
  (tu/clear-kb! (tu/test-kb)))

;; The ops are shared by the sampled test and the exhaustive one, so the two cannot
;; drift into checking different things — the only difference between them is how many
;; of the 120 orderings they walk.
(def ^:private derived-edge-ops
  [#(v/assert % '(genlCx CxWMid CxUniverse) 'CxUniverse)
   #(v/assert % '(wFactP WA) 'CxWMid)
   #(v/assert % '(implies (wFactP ?x) (wSeenP ?x)) 'CxWLow)
   #(v/assert % '(wWireP CxWLow CxWMid) 'CxUniverse)
   #(v/assert % '(implies (wWireP ?a ?b) (genlCx ?a ?b)) 'CxUniverse)])

(defn- derived-edge-observe [kb]
  {:derived (boolean (seq (v/sentexes-matching kb '(wSeenP WA) 'CxWLow)))})

(deftest a-derived-context-edge-seeds-like-an-asserted-one
  ;; and a rule concluding the edge reaches the same belief an assert does, or the
  ;; fixpoint would depend on whether the spindle was written or inferred.
  ;;
  ;; Four orderings, not all 120, for the reason `two-independent-exceptions` above
  ;; takes a handful: an ordering here costs ~2s — deriving the edge recomputes the
  ;; genlCx closure and re-places what it reaches, where every other test in this
  ;; file runs an ordering in about a millisecond — so the exhaustive walk is four
  ;; minutes, which is more than the whole rest of the suite.  The handful pins the
  ;; positions that matter: the edge rule first and last, and the fact arriving before
  ;; and after the wiring that has to reach it.  The exhaustive 120 is the `^:slow`
  ;; test below, and `lein gate --all` runs it.
  (doseq [order [[0 1 2 3 4] [4 3 2 1 0] [2 4 3 1 0] [1 3 0 4 2]]]
    (let [ops (mapv derived-edge-ops order)
          kb  (tu/fresh)]
      (doseq [op ops] (op kb))
      (is (= {:derived true} (derived-edge-observe kb))
          (str order ": a derived edge has to seed what an asserted one seeds"))))
  (tu/clear-kb! (tu/test-kb)))

(deftest ^:slow every-ordering-of-a-derived-context-edge-agrees
  ;; The exhaustive form of the test above — all 120 orderings, ~2s apiece.  An
  ;; exhaustive cross-product is what the mark is for, and this is the only test in
  ;; this file that earns it.
  (is (= {:derived true}
         (one-outcome! "derived visibility firing" derived-edge-ops derived-edge-observe))
      "a derived edge has to seed what an asserted one seeds, in any order")
  (tu/clear-kb! (tu/test-kb)))

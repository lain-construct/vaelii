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

;; How many orderings the *sampled* order-independence check walks when running the
;; full n! every time is too dear.  Order-independence is enforced here as a
;; regression net, not proven: a deterministic spread of orderings catches a
;; region-local relabelling that went order-sensitive without paying for the whole
;; cross-product.  Almost every scenario below runs an ordering in ~1 ms and so walks
;; all of them (no cap); the cap exists for the one scenario whose every ordering
;; recomputes the genlCx closure and costs ~2 s (the two derived-edge tests at the
;; end).  Raise this — or drop the cap at the call site — for an exhaustive audit.
(def ^:private ordering-sample 16)

(defn- shuffle-seeded
  "A reproducible shuffle: same seed, same order, independent of run.  Test code, so
  `java.util.Random` with a fixed seed rather than `clojure.core/shuffle`'s
  run-varying one — a sampled failure has to reproduce."
  [seed coll]
  (let [al (java.util.ArrayList. ^java.util.Collection coll)]
    (java.util.Collections/shuffle al (java.util.Random. (long seed)))
    (vec al)))

(defn- sampled-orderings
  "A deterministic sample of up to `n` of `orderings`: the identity and the reverse
  always — the two extremes a relabelling is likeliest to split on, which
  `permutations` returns first and last — then a fixed-seed spread of the rest.
  Returns them all unchanged when there are `n` or fewer."
  [n orderings]
  (let [v (vec orderings)]
    (if (<= (count v) n)
      v
      (into [(first v) (peek v)]
            (take (- n 2) (shuffle-seeded 42 (subvec v 1 (dec (count v)))))))))

(defn- default-rule [antes conseq]
  (list 'set/defaultRule (list 'implies (cons 'and antes) conseq)))

(defn- run-ops
  "Apply `ops` to a freshly cleared KB and return `observe`'s reading of it."
  [ops observe]
  (let [kb (tu/fresh)]
    (doseq [op ops] (op kb))
    (observe kb)))

(defn- outcomes
  "The set of distinct outcomes over the given `orderings`."
  [orderings observe]
  (into #{} (map #(run-ops % observe)) orderings))

(defn- one-outcome!
  "Assert that every ordering of `ops` agrees, and return the single outcome.  With a
  `cap`, walk a deterministic sample of that many orderings instead of the full n! —
  for a scenario whose per-ordering cost makes the exhaustive walk too dear to run
  every time (see `ordering-sample`)."
  ([label ops observe] (one-outcome! label ops observe nil))
  ([label ops observe cap]
   (let [all    (permutations ops)
         walked (cond->> all cap (sampled-orderings cap))
         os     (outcomes walked observe)]
     (is (= 1 (count os))
         (str label ": " (count os) " distinct outcomes across " (count walked)
              (when cap (str " sampled of " (count all))) " orderings — " (pr-str os)))
     (first os))))

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

(deftest a-re-assert-never-downgrades-a-premises-class
  ;; The class a sentex is held at is resolved from **content**, so the door cannot let
  ;; arrival order decide it.  A re-assert carrying no `:strength` states nothing about
  ;; the class — the `:default` it falls back to is the door's fallback, not the
  ;; caller's claim — so reading that silence as a downgrade retired the known-true
  ;; mark: asserted monotonic, re-asserted bare, and then met by a known-true negation,
  ;; the original was *defeated*, where the same three sentences without the bare
  ;; re-assert left an irreducible pair.  Six orderings, one outcome.
  (let [ops [#(v/assert % '(flies Tweety) 'CxUniverse {:strength :monotonic})
             #(v/assert % '(flies Tweety) 'CxUniverse)
             #(v/assert % '(not (flies Tweety)) 'CxUniverse {:strength :monotonic})]
        observe (fn [kb]
                  (let [pos (v/handle-of kb '(flies Tweety) 'CxUniverse)
                        neg (v/handle-of kb '(not (flies Tweety)) 'CxUniverse)]
                    {:flies       (v/in? kb pos)
                     :not-flies   (v/in? kb neg)
                     :flies-class (v/defeat-class kb pos)
                     :conflicts   (count (v/conflicts kb))}))
        result (one-outcome! "a bare re-assert of monotonic content" ops observe)]
    (testing "the bare re-assert leaves the known-true mark where it found it"
      (is (= :monotonic (:flies-class result))))
    (testing "so the pair is the irreducible clash it is without the re-assert"
      (is (true? (:flies result)))
      (is (true? (:not-flies result)))
      (is (= 1 (:conflicts result))))
    (testing "and narrowing a class is still retract! and re-assert"
      (let [kb (tu/fresh)
            h  (v/assert kb '(flies Tweety) 'CxUniverse {:strength :monotonic})]
        (v/retract! kb h)
        (is (= :default (v/defeat-class kb (v/assert kb '(flies Tweety) 'CxUniverse)))
            "a retraction takes the class with it, leaving none to inherit")))
    (tu/clear-kb! (tu/test-kb))))

;; ---- a block condition asked over a merged term -------------------------

(defn- blocked-observe
  "The reading a block-condition scenario is judged by: every conclusion the KB holds on
  `seen`, the backward door's answer for each of `subjects`, and the clash report.  The
  stored sentences alone would not separate a conclusion that was never drawn from one
  drawn and then swept under a name nobody asks about."
  [seen subjects]
  (fn [kb]
    {:seen      (set (map :sentence (v/sentexes-matching kb (list seen '?x) '?c)))
     :asked     (mapv #(v/ask? kb (list seen %) 'CxUniverse) subjects)
     :conflicts (count (v/conflicts kb))}))

(deftest a-block-condition-over-a-merged-term-is-order-independent
  ;; A block condition is decided three times over — at derive time from the firing's
  ;; raw bindings, again from a trigger, and again off a refusal record — and a merge
  ;; can retire the spelling either the *binding* or the *conjunct's own constant* is
  ;; written in.  A goal asked under a retired spelling comes back honestly empty, and
  ;; an empty block condition reads as **not excepted**, so the same four sentences
  ;; believed the conclusion or not depending on where the merge landed: 6 of these 24
  ;; orderings for a retired binding, 12 of 24 for a retired conjunct constant.
  ;;
  ;; `except_recheck_test/every-arrival-order-of-a-merge-reaches-one-belief` walks the
  ;; same two shapes over the stored sentences; this reads the backward door and the
  ;; clash report beside them, which is what a stored-sentence reading cannot see.
  (testing "the firing's own binding is the retired spelling"
    ;; `(qmark QOne)` binds `?x` to a term the merge retires, and the exception has to be
    ;; asked under the representative wherever in the order the merge lands.
    (let [ops [#(v/assert % '(exceptWhen (qskip ?x)
                                         (set/defaultRule (implies (and (qmark ?x)) (qseen ?x))))
                          'CxUniverse)
               #(v/assert % '(qmark QOne) 'CxUniverse)
               #(v/assert % '(rewriteOf QTwo QOne) 'CxUniverse)
               #(v/assert % '(qskip QOne) 'CxUniverse)]
          result (one-outcome! "a merged binding" ops (blocked-observe 'qseen '[QOne QTwo]))]
      (is (= {:seen #{} :asked [false false] :conflicts 0} result)
          "the excepted binding concludes nothing under either spelling, forward or backward")))
  (testing "the exception conjunct's own constant is the retired spelling"
    ;; Nothing the firing binds has merged: what moved is a term the *rule* was written
    ;; with, and an individual-only rewrite holds a rule back from migration, so the
    ;; stored condition keeps naming `COne` for good.
    (let [ops [#(v/assert % '(exceptWhen (cskip COne)
                                         (set/defaultRule (implies (and (cmark ?x)) (cseen ?x))))
                          'CxUniverse)
               #(v/assert % '(cmark CBase) 'CxUniverse)
               #(v/assert % '(rewriteOf CTwo COne) 'CxUniverse)
               #(v/assert % '(cskip CTwo) 'CxUniverse)]
          result (one-outcome! "a merged conjunct constant" ops (blocked-observe 'cseen '[CBase]))]
      (is (= {:seen #{} :asked [false] :conflicts 0} result)
          "a conjunct naming a retired term is asked under the representative that answers")))
  (tu/clear-kb! (tu/test-kb)))

(deftest naf-over-a-merged-term-is-order-independent
  ;; The same root cause in the polarity where the wrong answer is **unsound**.  An
  ;; `(unknown S)` inner query asked under a retired spelling is answered *absent* about a
  ;; term the KB has an answer for under its representative, so the rule concludes where
  ;; it must not — where a silently-false exception merely fails to guard.  This one did
  ;; not vary with the ordering at all: it drew the conclusion in all 24.
  (let [ops [#(v/assert % '(set/defaultRule
                            (implies (and (nmark ?x) (unknown (nskip ?x))) (nseen ?x)))
                        'CxUniverse)
             #(v/assert % '(nmark NOne) 'CxUniverse)
             #(v/assert % '(rewriteOf NTwo NOne) 'CxUniverse)
             #(v/assert % '(nskip NOne) 'CxUniverse)]
        result (one-outcome! "naf over a merged term" ops (blocked-observe 'nseen '[NOne NTwo]))]
    (testing "a term with an answer under its representative is not absent"
      (is (= {:seen #{} :asked [false false] :conflicts 0} result))))
  (tu/clear-kb! (tu/test-kb)))

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

;; ---- a declaration that arrives after the content it convicts -----------
;;
;; A constraint declaration is an ingredient of the clash exactly as the two facts are,
;; so all three orderings of "declaration, fact, fact" are the same knowledge and the KB
;; owes them the same answer.  The engine has two doors for that answer and the arrival
;; order picks which: a fact written *after* the declaration is refused at the door (or
;; weighed into `contradictions` where the opposing claim is defeasible), and a
;; declaration written after the facts is reported by the settle's exposure pass, with
;; belief untouched.  Both declarations take the second door by the same route: a
;; declaration in the settle's moved region says what it puts back in question, and the
;; pass sweeps that.
;;
;; **So what a single outcome means here is that the clash is *accounted for*, not that
;; every ordering picks the same door.** Which door is the constraint policy's business
;; (`checks/arbitrating?`), and under `:refuse` the two answers are deliberately
;; different things: a refusal turns a write away, a report leaves belief alone and names
;; what it found.  What may not vary is whether the KB says anything at all — and the
;; failure these tests are the net for is silence: a mark arriving last, and the pair it
;; forbids standing, believed, and mentioned by nothing.
;;
;; The reading `one-outcome!` compares is therefore the account and the believed extent
;; — never the door, which is what the orderings are entitled to differ on.  Two things
;; keep that from being a weakened boolean.  The **count** is compared, not its
;; positivity, so an engine that refused a write *and* reported the pair, or reported one
;; pair twice, fails exactly as one that did neither does.  And every ordering's full
;; reading is kept, so the tests below can go on to check that the doors actually used
;; are the two that exist and that each ordering used exactly one — a claim about the
;; whole set that no single outcome can carry.
;;
;; At `:default` the extent is identical across every ordering too, so the map there is
;; the strongest reading available: the same beliefs, and one account of the clash in
;; them.

(defn- refusing-assert
  "An `assert` op at `strength` that survives the door turning it away, recording the
  refusal in `refusals` instead.  The refusal is one of the two doors these tests read: a
  KB that refuses the write and a KB that reports the pair have both answered, and one
  that does neither has not."
  [refusals strength sentence]
  (fn [kb]
    (try (v/assert kb sentence 'CxUniverse {:strength strength})
         (catch clojure.lang.ExceptionInfo _ (swap! refusals inc)))))

(defn- constraint-reading
  "How one KB accounted for a definitional clash — per door, summed, and the extent the
  account is about.

  `mapv` on the ledger kinds and the extent, `count` everywhere else: every reader here
  is lazy over live state, and this map outlives the KB the ordering walk built it from."
  [kb refusals pattern]
  (let [reported (mapv :violation (v/violations kb))
        weighed  (count (v/contradictions kb))
        stuck    (count (v/conflicts kb))]
    {:refused   refusals
     :reported  reported
     :weighed   weighed
     :stuck     stuck
     :accounted (+ refusals (count reported) weighed stuck)
     :believed  (vec (sort (mapv (comp pr-str :sentence)
                                 (v/sentexes-matching kb pattern 'CxUniverse))))}))

(defn- constraint-outcome!
  "Every ordering of `sentences` at `strength`, as `{:invariant … :readings […]}`.

  `:invariant` is `one-outcome!`'s verdict over the part that may not vary — the account
  and, at `:default`, the extent; `:readings` is every ordering's full reading, for the
  claims about the *set* of doors used that a single outcome cannot make."
  [label strength sentences pattern]
  (let [refusals (atom 0)
        seen     (atom [])
        ops      (mapv #(refusing-assert refusals strength %) sentences)
        invariant
        (one-outcome!
         label ops
         (fn [kb]
           (let [full (constraint-reading kb @refusals pattern)]
             (reset! refusals 0)
             (swap! seen conj full)
             ;; the extent joins the invariant only where nothing is refused — at
             ;; `:monotonic` the refused write is a fact the KB legitimately does not
             ;; hold, and which fact that is depends on which of the two was written
             ;; first, exactly as two known-true claims about one slot always have
             (cond-> (select-keys full [:accounted :stuck])
               (= :default strength) (assoc :believed (:believed full))))))]
    {:invariant invariant :readings @seen}))

(defn- one-door-each!
  "Assert that every ordering used exactly one of the two doors, and that both doors are
  used across the set — a scenario where one door answers every ordering is one that
  never exercised the other."
  [readings]
  (let [doors (mapv (fn [r]
                      (cond-> #{}
                        (pos? (:refused r))        (conj :refused)
                        (seq (:reported r))        (conj :reported)
                        (pos? (:weighed r))        (conj :weighed)
                        (pos? (:stuck r))          (conj :stuck)))
                    readings)]
    (is (every? #(= 1 (count %)) doors)
        (str "every ordering answers by exactly one door — " (pr-str (frequencies doors))))
    (is (< 1 (count (distinct doors)))
        (str "and the scenario reaches more than one of them — " (pr-str (frequencies doors))))))

(deftest a-late-asymmetric-mark-is-accounted-for-in-every-ordering
  ;; `(asymmetric asBelow)` with both directions of one pair: 6 orderings, and the two
  ;; that put the declaration last are the ones with no door left to refuse at — both
  ;; facts are already stored and believed when the mark lands, so the exposure pass is
  ;; the whole of what keeps `conflicts`, `contradictions` and `violations` from all
  ;; being empty over a pair the KB's own vocabulary forbids.
  (let [{:keys [invariant readings]}
        (constraint-outcome! "late asymmetric mark" :monotonic
                             ['(asymmetric asBelow) '(asBelow Aa Bb) '(asBelow Bb Aa)]
                             '(asBelow ?x ?y))]
    (testing "the clash is answered exactly once, whichever of the three arrived last"
      (is (= 1 (:accounted invariant)))
      (is (zero? (:stuck invariant))
          "one side is turned away or the pair is named — never an irreducible conflict"))
    (one-door-each! readings)
    (testing "and the door the late mark takes is the ledger, with both facts standing"
      (let [late (filterv #(= 2 (count (:believed %))) readings)]
        (is (= 2 (count late)) "two of the six put the mark last")
        (is (every? #(= [:asymmetric] (:reported %)) late))))
    (tu/clear-kb! (tu/test-kb))))

(deftest a-late-asymmetric-mark-leaves-the-same-beliefs-in-every-ordering
  ;; The same three sentences at `:default`, where the door refuses nothing — an
  ;; `asymmetric` violation refuses only against a known-true converse — so the whole
  ;; believed extent is identical across all 6 and joins the reading.  What remains for
  ;; arrival order to pick is the account: a represented dilemma when a fact arrived
  ;; last, a ledger entry when the mark did.
  (let [{:keys [invariant readings]}
        (constraint-outcome! "late asymmetric mark at :default" :default
                             ['(asymmetric asAside) '(asAside Aa Bb) '(asAside Bb Aa)]
                             '(asAside ?x ?y))]
    (testing "both directions stand in every ordering, and the clash is named once"
      (is (= ["(asAside Aa Bb)" "(asAside Bb Aa)"] (:believed invariant)))
      (is (= 1 (:accounted invariant)))
      (is (zero? (:stuck invariant))))
    (one-door-each! readings)
    (testing "nothing is refused — a default converse is weighed or reported, not turned away"
      (is (every? #(zero? (:refused %)) readings)))
    (tu/clear-kb! (tu/test-kb))))

(deftest a-late-mark-over-a-transitive-relation-is-accounted-for-in-every-ordering
  ;; The same pair with `(transitive asAbove)` in the scenario: 4 sentences, 24
  ;; orderings, and a second declaration whose own arrival reaches back over the same
  ;; facts.  Transitivity closes the pair into the self-tuples `(asAbove Aa Aa)` and
  ;; `(asAbove Bb Bb)`, which `asymmetric` admits — so the clash under test is still the
  ;; two-way pair, now under a predicate whose extent both marks descend through.
  (let [{:keys [invariant readings]}
        (constraint-outcome! "late mark over a transitive relation" :monotonic
                             ['(transitive asAbove) '(asymmetric asAbove)
                              '(asAbove Aa Bb) '(asAbove Bb Aa)]
                             '(asAbove ?x ?y))]
    (testing "the clash is answered exactly once, whichever of the four arrived last"
      (is (= 1 (:accounted invariant)))
      (is (zero? (:stuck invariant))))
    (one-door-each! readings)
    (tu/clear-kb! (tu/test-kb))))

(deftest a-late-anti-transitive-mark-is-accounted-for-in-every-ordering
  ;; The third mark, and the one whose clash is a **triple**: `antiTransitive` convicts
  ;; the two chain steps and the direct step together, so the entry names three halves
  ;; and no two of them are the pair.  4 sentences, 24 orderings.
  (let [{:keys [invariant readings]}
        (constraint-outcome! "late antiTransitive mark" :monotonic
                             ['(antiTransitive parOfx) '(parOfx Aa Bb)
                              '(parOfx Bb Cc) '(parOfx Aa Cc)]
                             '(parOfx ?x ?y))]
    (testing "the chain is answered exactly once, whichever of the four arrived last"
      (is (= 1 (:accounted invariant)))
      (is (zero? (:stuck invariant))))
    (one-door-each! readings)
    (testing "the six orderings that put the mark last name the chain in the ledger"
      (let [late (filterv #(= 3 (count (:believed %))) readings)]
        (is (= 6 (count late)))
        (is (every? #(= [:anti-transitive] (:reported %)) late))))
    (tu/clear-kb! (tu/test-kb))))

(deftest a-late-functional-mark-is-accounted-for-in-every-ordering
  ;; The second mark, over two fillers no merge can reconcile — `(functional P)` between
  ;; two *symbols* is co-reference and the KB derives an equality from it instead, so a
  ;; clash needs values the partition cannot hold (docs/equality.md).
  (let [{:keys [invariant readings]}
        (constraint-outcome! "late functional mark" :monotonic
                             ['(functional ageOfx) '(ageOfx Aa 3) '(ageOfx Aa 4)]
                             '(ageOfx ?x ?y))]
    (testing "the slot is answered exactly once, whichever of the three arrived last"
      (is (= 1 (:accounted invariant)))
      (is (zero? (:stuck invariant))))
    (one-door-each! readings)
    (tu/clear-kb! (tu/test-kb))))

(deftest a-late-mark-answers-the-way-a-late-disjointness-does
  ;; The precedent the choice above is made against, asserted rather than assumed: a late
  ;; `(disjoint A B)` over an already-clashing pair reports and leaves belief alone.  The
  ;; two must agree door for door, or the KB is treating "the declaration came last"
  ;; differently according to which declaration it is.
  (let [marked (constraint-outcome! "late asymmetric mark, per door" :monotonic
                                    ['(asymmetric asBeside) '(asBeside Aa Bb)
                                     '(asBeside Bb Aa)]
                                    '(asBeside ?x ?y))
        separated (constraint-outcome! "late disjointness, per door" :monotonic
                                       ['(disjoint tdogx tcatx) '(tdogx Rexx)
                                        '(tcatx Rexx)]
                                       '(?t Rexx))
        doors (fn [{:keys [readings]}]
                (frequencies (mapv #(-> % (select-keys [:refused :weighed :stuck])
                                        (assoc :reported (count (:reported %))))
                                   readings)))]
    (is (= (:invariant marked) (:invariant separated))
        "one account of the clash, whichever declaration arrived last")
    (is (= (doors marked) (doors separated))
        "and the same doors in the same proportions — only the entry kind differs")
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
    (is (= #{{:isa true}} (outcomes (permutations ops) observe))
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

(deftest ^:slow a-derived-context-edge-seeds-like-an-asserted-one
  ;; and a rule concluding the edge reaches the same belief an assert does, or the
  ;; fixpoint would depend on whether the spindle was written or inferred.
  ;;
  ;; Four orderings, not all 120, for the reason `two-independent-exceptions` above
  ;; takes a handful: an ordering here costs ~2s — deriving the edge recomputes the
  ;; genlCx closure and re-places what it reaches, where every other test in this
  ;; file runs an ordering in about a millisecond — so the exhaustive walk is four
  ;; minutes, which is more than the whole rest of the suite.  The handful pins the
  ;; positions that matter: the edge rule first and last, and the fact arriving before
  ;; and after the wiring that has to reach it.  A broader deterministic sample is the
  ;; `^:slow` test below, and `lein gate --all` runs it.
  (doseq [order [[0 1 2 3 4] [4 3 2 1 0] [2 4 3 1 0] [1 3 0 4 2]]]
    (let [ops (mapv derived-edge-ops order)
          kb  (tu/fresh)]
      (doseq [op ops] (op kb))
      (is (= {:derived true} (derived-edge-observe kb))
          (str order ": a derived edge has to seed what an asserted one seeds"))))
  (tu/clear-kb! (tu/test-kb)))

(deftest ^:slow orderings-of-a-derived-context-edge-agree
  ;; The broad form of the 4-ordering test above: a deterministic sample of orderings
  ;; (`ordering-sample`), not all 120.  Every ordering here recomputes the genlCx
  ;; closure and re-places what it reaches, so it costs ~2s — the exhaustive 120 is
  ;; ~5 minutes, more than the rest of the suite put together, for a cross-product
  ;; whose order-dependence would already surface in a spread of orderings.  The
  ;; sample walks the identity, the reverse and a fixed-seed spread between them; raise
  ;; `ordering-sample` or drop the cap for an exhaustive audit.
  (is (= {:derived true}
         (one-outcome! "derived visibility firing" derived-edge-ops derived-edge-observe
                       ordering-sample))
      "a derived edge has to seed what an asserted one seeds, over a sample of orderings")
  (tu/clear-kb! (tu/test-kb)))

;; ---- belief projection reads its answer from current state, in any order ----

(deftest belief-projection-is-order-independent
  ;; The modal projector answers `(believes Agent P)` by running `P` through the whole
  ;; registry in the agent's own context, so its answers must not depend on the order the
  ;; grant, the belief facts, and a genl edge a belief rests on arrived — nor on the order
  ;; two agents' contradictory beliefs landed: the two share no context, so the pair must
  ;; never surface as a contradiction under any ordering.  5 assertions, 120 orderings.
  (let [alice (v/context-of-agent 'Alice)
        bob   (v/context-of-agent 'Bob)
        ops [#(v/assert % '(modalPredicate believes) 'CxUniverse)  ; the grant
             #(v/assert % '(flies Tweety) alice)                   ; Alice believes it
             #(v/assert % '(not (flies Tweety)) bob)               ; Bob believes the opposite
             #(v/assert % '(genl finch7 bird7) alice)              ; a taxonomy edge in Alice's ctx
             #(v/assert % '(finch7 Jack) alice)]                   ; so Alice believes (bird7 Jack)
        observe (fn [kb]
                  {:alice-flies    (v/ask? kb '(believes Alice (flies Tweety)) 'CxUniverse)
                   :bob-notflies   (v/ask? kb '(believes Bob (not (flies Tweety))) 'CxUniverse)
                   :alice-notflies (v/ask? kb '(believes Alice (not (flies Tweety))) 'CxUniverse)
                   :alice-bird     (v/ask? kb '(believes Alice (bird7 Jack)) 'CxUniverse)
                   :contradictions (count (v/contradictions kb))})
        result (one-outcome! "belief projection" ops observe)]
    (testing "and the one outcome is the intended reading"
      (is (true? (:alice-flies result)))
      (is (true? (:bob-notflies result)))
      (is (false? (:alice-notflies result)) "no cross-agent leakage, in any order")
      (is (true? (:alice-bird result)) "the projection reaches the genl closure")
      (is (zero? (:contradictions result)) "isolated agents raise no contradiction")))
  (tu/clear-kb! (tu/test-kb)))

(deftest a-symmetric-antecedent-is-order-independent-at-either-position
  ;; A symmetric fact is stored in one orientation and *means* both, and the two ways a
  ;; rule reaches it disagreed about that: the join probes both argument orders, while
  ;; the trigger unified the arriving fact as written.  So the combination that needed
  ;; the mirror was enumerated by nobody when the symmetric fact arrived **second**, and
  ;; the same three sentences derived the conclusion or not depending on which was last.
  ;; 6 orderings, and the fourth reading below is the full join, which was always right.
  (let [ops     [#(v/assert % '(symmetric sibOf) 'CxUniverse {:strength :monotonic})
                 #(v/assert % '(implies (and (ownsPet ?o ?a) (sibOf ?a ?b)) (alsoOwns ?o ?b))
                            'CxUniverse {:direction :forward})
                 #(v/assert % '(ownsPet Bob Tib) 'CxUniverse)
                 #(v/assert % '(sibOf Rex Tib) 'CxUniverse)]
        observe (fn [kb]
                  {:mirrored (boolean (seq (v/sentexes-matching kb '(alsoOwns Bob Rex) 'CxUniverse)))
                   ;; `mapv`: the extent readers are lazy over live state, and this map
                   ;; outlives the KB the ordering walk built it from
                   :supports (mapv #(count (:support (v/why kb (:id %))))
                                   (v/sentexes-matching kb '(alsoOwns ?o ?b) 'CxUniverse))
                   :conflicts (count (v/conflicts kb))})
        result  (one-outcome! "symmetric antecedent" ops observe)]
    (testing "and the one outcome is the join's reading"
      (is (true? (:mirrored result))
          "the pair the mirror makes is derived whichever fact arrived second")
      (is (= [1] (:supports result))
          "one conclusion, justified once — the mirror of a fact is not a second premise")
      (is (zero? (:conflicts result))))
    (tu/clear-kb! (tu/test-kb))))

(deftest a-symmetric-fact-reaches-a-rule-stated-over-its-super-predicate
  ;; The mirror is the *fact's* own declaration, and the antecedent that has to see it
  ;; need not be written at the fact's own predicate: `(genl gsibOf gkinOf)` puts a
  ;; `gkinOf` antecedent above a `gsibOf` fact, so the pairs that antecedent reaches
  ;; move when `gsibOf` is declared symmetric.  Both halves of the reach have to fan the
  ;; sub-predicates — the trigger's mirror, and the re-join a late declaration owes — and
  ;; either one reading only the antecedent's own functor loses the conclusion in the
  ;; orderings that put the fact or the declaration last.  5 assertions, 120 orderings.
  ;;
  ;; The super-predicate carries facts of its own beside the sub's, which is the
  ;; arrangement a real hierarchy is in and the one that makes the conclusion **set** the
  ;; claim rather than its count: a mirror taken where the pair does not call for one, or
  ;; a super-predicate fact read as though it were symmetric, both read as an extra
  ;; conclusion rather than as nothing at all.  They arrive with the sub's fact as one op
  ;; — what the orderings are about is where the *declaration*, the edge and the rule fall
  ;; against the facts, not how the facts fall against each other.
  (let [ops     [#(v/assert % '(symmetric gsibOf) 'CxUniverse {:strength :monotonic})
                 #(v/assert % '(genl gsibOf gkinOf) 'CxUniverse {:strength :monotonic})
                 #(v/assert % '(implies (and (gownsPet ?o ?a) (gkinOf ?a ?b)) (gAlsoOwns ?o ?b))
                            'CxUniverse {:direction :forward})
                 #(v/assert % '(gownsPet Bob Tib) 'CxUniverse)
                 #(do (v/assert % '(gsibOf Rex Tib) 'CxUniverse)
                      (doseq [[a b] '[[Ann Bea] [Cal Dee] [Eve Fay] [Gil Hal] [Ida Jem]]]
                        (v/assert % (list 'gkinOf a b) 'CxUniverse)))]
        observe (fn [kb]
                  (let [cs (v/sentexes-matching kb '(gAlsoOwns ?o ?b) 'CxUniverse)]
                    {:conclusions (set (map :sentence cs))
                     ;; sorted: the extent readers promise the set, not the order
                     :supports    (vec (sort (map #(count (:support (v/why kb (:id %)))) cs)))
                     :conflicts   (count (v/conflicts kb))}))
        result  (one-outcome! "symmetric under a super-predicate" ops observe)]
    (testing "and the one outcome is the mirrored pair, derived once"
      (is (= '#{(gAlsoOwns Bob Rex)} (:conclusions result))
          "the sub-predicate's mirror reaches an antecedent stated above it")
      (is (= [1] (:supports result))
          "one conclusion, justified once — the mirror of a fact is not a second premise")
      (is (zero? (:conflicts result))))
    (tu/clear-kb! (tu/test-kb))))

(deftest a-symmetric-antecedent-mid-chain-is-order-independent
  ;; The 4-op case above the previous two has the symmetric literal at the rule's last
  ;; antecedent, where the trigger and the join are the only two readers.  Here it sits
  ;; **between** two others, so the mirror has to hold whichever way the completion runs:
  ;; the symmetric fact arriving last triggers at the middle position and both neighbours
  ;; are joined outward from the mirrored binding, while either neighbour arriving last
  ;; reaches the middle by a join from one side and the far one by a join from the other.
  ;; 5 assertions, 120 orderings, and only `(mSpans Bo Zed)` is entailed — a mirror
  ;; applied where the chain does not need one would show up as a second conclusion.
  (let [ops     [#(v/assert % '(symmetric mlinkOf) 'CxUniverse {:strength :monotonic})
                 #(v/assert % '(implies (and (mheadOf ?o ?a) (mlinkOf ?a ?b) (mtailOf ?b ?c))
                                        (mSpans ?o ?c))
                            'CxUniverse {:direction :forward})
                 #(v/assert % '(mheadOf Bo Tib) 'CxUniverse)
                 #(v/assert % '(mlinkOf Rex Tib) 'CxUniverse)
                 #(v/assert % '(mtailOf Rex Zed) 'CxUniverse)]
        observe (fn [kb]
                  (let [cs (v/sentexes-matching kb '(mSpans ?o ?c) 'CxUniverse)]
                    {:conclusions (set (map :sentence cs))
                     :supports    (vec (sort (map #(count (:support (v/why kb (:id %)))) cs)))
                     :conflicts   (count (v/conflicts kb))}))
        result  (one-outcome! "symmetric mid-chain" ops observe)]
    (testing "and the one outcome is the chain the mirror closes, derived once"
      (is (= '#{(mSpans Bo Zed)} (:conclusions result)))
      (is (= [1] (:supports result)))
      (is (zero? (:conflicts result))))
    (tu/clear-kb! (tu/test-kb))))

(deftest a-symmetric-fact-does-not-mirror-what-was-not-declared-symmetric
  ;; The mirror is the *fact's* own declaration, not its supertype's: `sibOf` being
  ;; symmetric says nothing about a `knowsOf` fact, and a rule over one must not read a
  ;; pair the KB never stated.
  (let [kb (tu/test-kb)]
    (tu/clear-kb! kb)
    (v/assert kb '(implies (likesOf ?a ?b) (fanOf ?a ?b)) 'CxUniverse {:direction :forward})
    (v/assert kb '(likesOf Ann Bea) 'CxUniverse)
    (is (= '[(fanOf Ann Bea)]
           (mapv :sentence (v/sentexes-matching kb '(fanOf ?a ?b) 'CxUniverse)))
        "no mirrored conclusion off an undeclared predicate")
    (tu/clear-kb! kb)))

(deftest a-symmetric-fact-mirrors-from-the-lead-position-too
  ;; The sibling of the test above, with the arrangement that hides the defect removed.
  ;; There, the super-predicate carries five facts of its own, which is enough to move the
  ;; planner off leading the join with the symmetric literal.  Here it carries none, so
  ;; `(gkinOf ?a ?b)` is the cheapest literal and leads — and a lead-position match is the
  ;; one place a symmetric fact's mirror was dropped, because both retrieval paths deduped
  ;; the mirror probe by **handle**: an all-variable pattern binds one stored fact twice
  ;; and differently, and the second binding was read as a repeat of the first.
  ;;
  ;; It failed forward *and* backward, which is what says the defect was in the matcher
  ;; rather than in chaining: 48 of these 120 orderings derived nothing, and `prove` of
  ;; the mirrored pair failed in exactly those.  Both readings are here for that reason.
  (let [ops     [#(v/assert % '(symmetric lsibOf) 'CxUniverse {:strength :monotonic})
                 #(v/assert % '(genl lsibOf lkinOf) 'CxUniverse {:strength :monotonic})
                 #(v/assert % '(implies (and (lownsPet ?o ?a) (lkinOf ?a ?b)) (lAlsoOwns ?o ?b))
                            'CxUniverse {:direction :forward})
                 #(v/assert % '(lownsPet Bob Tib) 'CxUniverse)
                 #(v/assert % '(lsibOf Rex Tib) 'CxUniverse)]
        observe (fn [kb]
                  {:conclusions (set (map :sentence (v/sentexes-matching
                                                     kb '(lAlsoOwns ?o ?b) 'CxUniverse)))
                   ;; the backward half of the same question, asked of the mirror
                   :proved      (boolean (seq (v/prove kb '(lkinOf Tib Rex))))
                   :conflicts   (count (v/conflicts kb))})
        result  (one-outcome! "symmetric in the lead position" ops observe)]
    (testing "and the one outcome is the mirrored pair, forward and backward"
      (is (= '#{(lAlsoOwns Bob Rex)} (:conclusions result)))
      (is (true? (:proved result))
          "the mirror answers a goal, not only a join")
      (is (zero? (:conflicts result))))
    (tu/clear-kb! (tu/test-kb))))

;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.abduce-test
  "Abduction: what would have to be true.

  `prove` answers whether a goal follows; `abduce` answers what it is *missing*, and
  mints that as a hypothesis.  Two things are the contract, and most of what is below
  tests one of them: an abduction whose result is ignored leaves the KB as it found it,
  and an answer that rests on an assumption says so.

  Everything else here is the **gate**.  An abducer that will hypothesize anything
  explains everything and is worth nothing, so a predicate is assumable only if it was
  granted, and a hypothesis must be ground, legally assertible, and uncontradicted where
  it lands."
  (:require [clojure.string :as str]
            [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.abduce :as abduce]
            [vaelii.impl.resolution :as res]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- a-context
  "Hang `ctx` under UniverseContext.  A `fresh` KB has no spindle, and a context wired
  to nothing sees nothing."
  [kb ctx]
  (v/assert kb (list 'genlContext ctx 'UniverseContext) 'UniverseContext))

(defn- grant
  "Declare `pred` assumable.  Nothing is abducible without this."
  [kb pred ctx]
  (v/assert kb (list 'abduciblePredicate pred) ctx))

(defn- a-rule
  "`(implies (and <antecedents>) <consequent>)`."
  [kb antecedents consequent ctx]
  (v/assert kb (list 'implies (cons 'and antecedents) consequent) ctx))

(defn- sentences [result] (set (map :sentence (:hypotheses result))))

;; ---- the headline --------------------------------------------------------

(tu/deftest-kb the-wabd-shape
  (tu/with-terms [wabGoal wabPremise N TheoryContext]
    (a-context kb TheoryContext)
    (grant kb wabPremise TheoryContext)
    (a-rule kb [(list wabPremise '?x)] (list wabGoal '?x) TheoryContext)
    (testing "the goal does not follow from what is stored"
      (is (not (v/provable? kb (list wabGoal N) TheoryContext))))
    (let [r (v/abduce kb (list wabGoal N) TheoryContext)]
      (testing "abduction finds the one thing that would make it follow"
        (is (= #{(list wabPremise N)} (sentences r))))
      (testing "and the goal is answerable under it"
        (is (seq (:solutions r))))
      (testing "the answer names its assumption rather than passing as a proof"
        (is (= 1 (count (:hypotheses r))))
        (is (= (:context r) (:context (first (:hypotheses r))))))
      (testing "the scratch context is torn down, so the handle is nil not dangling"
        (is (nil? (:handle (first (:hypotheses r)))))
        (is (nil? (v/handle-of kb (list wabPremise N) (:context r)))))
      (testing "and the goal is no more provable afterwards than before"
        (is (not (v/provable? kb (list wabGoal N) TheoryContext)))))))

;; ---- the gate ------------------------------------------------------------

(tu/deftest-kb an-ungranted-predicate-is-never-assumed
  (tu/with-terms [wabGoal wabPremise N TheoryContext]
    (a-context kb TheoryContext)
    (a-rule kb [(list wabPremise '?x)] (list wabGoal '?x) TheoryContext)
    (let [r (v/abduce kb (list wabGoal N) TheoryContext)]
      (testing "the same shape without the grant mints nothing"
        (is (empty? (:hypotheses r)))
        (is (empty? (:solutions r))))
      (testing "and says what it would not assume, so the caller can tell an
                ungranted predicate from an empty KB"
        (is (= [(list wabPremise N)] (:refused r)))))))

(tu/deftest-kb a-sentence-assert-would-refuse-is-not-hypothesized
  (tu/with-terms [wabGoal wabPremise N dog_ cat_ TheoryContext]
    (a-context kb TheoryContext)
    (v/assert kb (list 'genl dog_ 'thing) TheoryContext)
    (v/assert kb (list 'genl cat_ 'thing) TheoryContext)
    (v/assert kb (list 'disjoint dog_ cat_) TheoryContext)
    (v/assert kb (list cat_ N) TheoryContext)
    (v/assert kb (list 'argIsa wabPremise 1 dog_) TheoryContext)
    (grant kb wabPremise TheoryContext)
    (a-rule kb [(list wabPremise '?x)] (list wabGoal '?x) TheoryContext)
    (testing "the hypothesis would put a cat in a dog-only slot, so it is refused"
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list wabPremise N) TheoryContext))
          "and the same sentence really is unassertible"))
    (let [r (v/abduce kb (list wabGoal N) TheoryContext)]
      (is (empty? (:hypotheses r)))
      (is (= [(list wabPremise N)] (:refused r))))))

(tu/deftest-kb a-hypothesis-a-believed-negation-denies-is-not-minted
  (tu/with-terms [wabGoal wabPremise N TheoryContext]
    (a-context kb TheoryContext)
    (grant kb wabPremise TheoryContext)
    (a-rule kb [(list wabPremise '?x)] (list wabGoal '?x) TheoryContext)
    (v/assert kb (list 'not (list wabPremise N)) TheoryContext {:strength :monotonic})
    (let [r (v/abduce kb (list wabGoal N) TheoryContext)]
      (testing "a clash visible now is not an arbitration to run"
        (is (empty? (:hypotheses r)))
        (is (= [(list wabPremise N)] (:refused r)))))))

(tu/deftest-kb an-open-goal-hypothesizes-nothing
  (tu/with-terms [wabGoal wabPremise TheoryContext]
    (a-context kb TheoryContext)
    (grant kb wabPremise TheoryContext)
    (a-rule kb [(list wabPremise '?x)] (list wabGoal '?x) TheoryContext)
    (let [r (v/abduce kb (list wabGoal '?who) TheoryContext)]
      (testing "which individual would it be?  an open hypothesis is skolemization's
                question, so this refuses rather than inventing a name"
        (is (empty? (:hypotheses r)))
        (is (empty? (:solutions r))))
      (testing "and it is reported as the open literal the search actually ran out on —
                the rule's own variable, since the goal's is bound to it and neither is
                bound to a term"
        (is (= 1 (count (:refused r))))
        (let [[pred arg] (first (:refused r))]
          (is (= wabPremise pred))
          (is (str/starts-with? (name arg) "?")))))))

(tu/deftest-kb the-grant-is-read-from-the-asking-context
  (tu/with-terms [wabGoal wabPremise N TheoryContext SiblingContext]
    (a-context kb TheoryContext)
    (a-context kb SiblingContext)
    (a-rule kb [(list wabPremise '?x)] (list wabGoal '?x) TheoryContext)
    (grant kb wabPremise SiblingContext)
    (testing "a grant made in a context the asker cannot see does not reach it —
              abducibility is a policy of the context that gives it"
      (is (empty? (:hypotheses (v/abduce kb (list wabGoal N) TheoryContext)))))
    (v/assert kb (list 'genlContext TheoryContext SiblingContext) 'UniverseContext)
    (testing "once it can see the grantor, it may assume"
      (is (= #{(list wabPremise N)}
             (sentences (v/abduce kb (list wabGoal N) TheoryContext)))))))

;; ---- what a hypothesis is ------------------------------------------------

(tu/deftest-kb a-kept-hypothesis-is-an-ordinary-defeasible-premise
  (tu/with-terms [wabGoal wabPremise N TheoryContext]
    (a-context kb TheoryContext)
    (grant kb wabPremise TheoryContext)
    (a-rule kb [(list wabPremise '?x)] (list wabGoal '?x) TheoryContext)
    (let [r    (v/abduce kb (list wabGoal N) TheoryContext {:keep? true})
          actx (:context r)
          h    (:handle (first (:hypotheses r)))]
      (try
        (testing "it is a real, believed premise"
          (is (integer? h))
          (is (v/in? kb h))
          (is (v/premise? kb h)))
        (testing "at :default — which is the whole of the arbitration story"
          (is (= :default (v/defeat-class kb h))))
        (testing "its provenance says it was assumed, not asserted by anyone"
          (let [pv (v/provenance kb h)]
            (is (true? (:abduced pv)))
            (is (= (list wabGoal N) (:abduced-for pv)))
            (is (= :vaelii.impl.abduce/hypothesis (:creator pv)))))
        (testing "the rule fired over it, and placement put the conclusion inside the
                  scratch context — nothing arranged that"
          (let [c (v/handle-of kb (list wabGoal N) actx)]
            (is (integer? c))
            (is (v/in? kb c))))
        (testing "and nothing that existed before can see any of it"
          (is (nil? (v/handle-of kb (list wabPremise N) TheoryContext)))
          (is (empty? (v/sentexes-matching kb (list wabGoal N) TheoryContext))))
        (finally (v/abduce-discard! kb r))))))

(tu/deftest-kb a-monotonic-fact-defeats-a-hypothesis-through-the-ordinary-path
  (tu/with-terms [wabGoal wabPremise N TheoryContext]
    (a-context kb TheoryContext)
    (grant kb wabPremise TheoryContext)
    (a-rule kb [(list wabPremise '?x)] (list wabGoal '?x) TheoryContext)
    (let [r    (v/abduce kb (list wabGoal N) TheoryContext {:keep? true})
          actx (:context r)
          h    (:handle (first (:hypotheses r)))
          c    (v/handle-of kb (list wabGoal N) actx)]
      (try
        (is (v/in? kb h))
        (is (v/in? kb c))
        (let [no (v/assert kb (list 'not (list wabPremise N)) TheoryContext
                           {:strength :monotonic})]
          (testing "known-true content beats an assumption, with no abduction-specific
                    rule anywhere — the hypothesis is simply the weaker side"
            (is (not (v/in? kb h)))
            (is (= :defeated (:reason (v/why-not kb h)))))
          (testing "and what it licensed goes out with it"
            (is (not (v/in? kb c))))
          (testing "retract the fact and the assumption comes back"
            (v/retract! kb no)
            (is (v/in? kb h))))
        (finally (v/abduce-discard! kb r))))))

;; ---- isolation and cleanup -----------------------------------------------

(tu/deftest-kb an-ignored-abduction-leaves-the-kb-as-it-found-it
  (tu/with-terms [wabGoal wabPremise N TheoryContext]
    (a-context kb TheoryContext)
    (grant kb wabPremise TheoryContext)
    (a-rule kb [(list wabPremise '?x)] (list wabGoal '?x) TheoryContext)
    (let [sx-before   (tu/sentex-ids kb)
          jd-before   (tu/justification-ids kb)
          in-before   (v/believed kb sx-before)
          r           (v/abduce kb (list wabGoal N) TheoryContext)]
      (is (seq (:hypotheses r)) "the call did do something")
      (testing "and then undid all of it: the same records, the same justifications"
        (is (= sx-before (tu/sentex-ids kb)))
        (is (= jd-before (tu/justification-ids kb))))
      (testing "and the same beliefs"
        (is (= in-before (v/believed kb sx-before)))))))

(tu/deftest-kb discarding-takes-the-consequences-with-it
  (tu/with-terms [wabGoal wabPremise N TheoryContext]
    (a-context kb TheoryContext)
    (grant kb wabPremise TheoryContext)
    (a-rule kb [(list wabPremise '?x)] (list wabGoal '?x) TheoryContext)
    (let [sx-before (tu/sentex-ids kb)
          r         (v/abduce kb (list wabGoal N) TheoryContext {:keep? true})
          actx      (:context r)]
      (is (< (count sx-before) (count (tu/sentex-ids kb))))
      (is (integer? (v/handle-of kb (list wabGoal N) actx)) "a derived conclusion exists")
      (let [gone (v/abduce-discard! kb r)]
        (testing "the hypothesis and the conclusion it licensed both go"
          (is (<= 2 (:removed-sentexes gone)))
          (is (= sx-before (tu/sentex-ids kb))))
        (testing "and discarding twice is a no-op, not an error"
          (is (= {:removed-sentexes 0 :removed-justifications 0}
                 (v/abduce-discard! kb r))))))))

;; ---- the search ----------------------------------------------------------

(tu/deftest-kb a-second-round-reaches-what-the-first-could-not
  (tu/with-terms [wabGoal wabP wabQ N TheoryContext]
    (a-context kb TheoryContext)
    (grant kb wabP TheoryContext)
    (grant kb wabQ TheoryContext)
    (a-rule kb [(list wabP '?x) (list wabQ '?x)] (list wabGoal '?x) TheoryContext)
    (let [r (v/abduce kb (list wabGoal N) TheoryContext)]
      (testing "a conjunction is solved left to right, so the first round never reaches
                the second conjunct — assuming the first is what exposes it"
        (is (= #{(list wabP N) (list wabQ N)} (sentences r)))
        (is (seq (:solutions r)))
        (is (= :complete (:status r)))))))

(tu/deftest-kb the-hypothesis-set-is-irredundant
  (tu/with-terms [wabGoal wabP wabQ N TheoryContext]
    (a-context kb TheoryContext)
    (grant kb wabP TheoryContext)
    (grant kb wabQ TheoryContext)
    (a-rule kb [(list wabP '?x)] (list wabGoal '?x) TheoryContext)
    (a-rule kb [(list wabQ '?x)] (list wabGoal '?x) TheoryContext)
    (let [r (v/abduce kb (list wabGoal N) TheoryContext)]
      (testing "two independent routes both dead-end, so both are assumed — and then
                the one the answer does not need is dropped"
        (is (= 1 (count (:hypotheses r))))
        (is (contains? #{(list wabP N) (list wabQ N)} (first (sentences r))))
        (is (seq (:solutions r)))))))

(tu/deftest-kb a-goal-that-already-follows-assumes-nothing
  (tu/with-terms [wabGoal wabPremise N TheoryContext]
    (a-context kb TheoryContext)
    (grant kb wabPremise TheoryContext)
    (a-rule kb [(list wabPremise '?x)] (list wabGoal '?x) TheoryContext)
    (v/assert kb (list wabPremise N) TheoryContext)
    (let [r (v/abduce kb (list wabGoal N) TheoryContext)]
      (testing "an empty hypothesis set is the claim that nothing was assumed"
        (is (empty? (:hypotheses r)))
        (is (seq (:solutions r)))
        (is (= :complete (:status r)))))))

(tu/deftest-kb abducing-the-same-goal-twice-mints-no-duplicates
  (tu/with-terms [wabGoal wabPremise N TheoryContext]
    (a-context kb TheoryContext)
    (grant kb wabPremise TheoryContext)
    (a-rule kb [(list wabPremise '?x)] (list wabGoal '?x) TheoryContext)
    (let [r1 (v/abduce kb (list wabGoal N) TheoryContext)
          r2 (v/abduce kb (list wabGoal N) TheoryContext)]
      (is (= (sentences r1) (sentences r2)))
      (is (= 1 (count (:hypotheses r2))))
      (testing "each ran in its own scratch context, and neither left one behind"
        (is (not= (:context r1) (:context r2)))
        (is (zero? (v/context-size kb (:context r1))))
        (is (zero? (v/context-size kb (:context r2))))))))

;; ---- the caps ------------------------------------------------------------

(tu/deftest-kb the-hypothesis-cap-is-enforced-and-said-out-loud
  (tu/with-terms [wabGoal wabP wabQ wabR N TheoryContext]
    (a-context kb TheoryContext)
    (run! #(grant kb % TheoryContext) [wabP wabQ wabR])
    (a-rule kb [(list wabP '?x) (list wabQ '?x) (list wabR '?x)]
            (list wabGoal '?x) TheoryContext)
    (let [r (v/abduce kb (list wabGoal N) TheoryContext {:max-hypotheses 2})]
      (testing "it stops at the cap rather than assuming its way to an answer"
        (is (= 2 (count (:hypotheses r))))
        (is (empty? (:solutions r))))
      (testing "and says the cap is why, so nothing found is not read as nothing to find"
        (is (= :capped (:status r)))
        (is (empty? (:refused r))
            "the third antecedent is a candidate with no room, not something refused —
             the two are different answers and are reported separately")))
    (testing "with room, the same goal is answered"
      (let [r (v/abduce kb (list wabGoal N) TheoryContext)]
        (is (= 3 (count (:hypotheses r))))
        (is (seq (:solutions r)))
        (is (= :complete (:status r)))))))

(tu/deftest-kb a-dead-end-deeper-than-the-depth-cap-is-left-alone
  (tu/with-terms [wabGoal wabMid wabPremise N TheoryContext]
    (a-context kb TheoryContext)
    (grant kb wabPremise TheoryContext)
    (a-rule kb [(list wabMid '?x)] (list wabGoal '?x) TheoryContext)
    (a-rule kb [(list wabPremise '?x)] (list wabMid '?x) TheoryContext)
    (testing "two rule expansions deep, and the cap is one"
      (let [r (v/abduce kb (list wabGoal N) TheoryContext {:max-depth 1})]
        (is (empty? (:hypotheses r)))
        (is (= [(list wabPremise N)] (:refused r)))))
    (testing "the default reach finds it"
      (let [r (v/abduce kb (list wabGoal N) TheoryContext)]
        (is (= #{(list wabPremise N)} (sentences r)))
        (is (seq (:solutions r)))))))

;; ---- the shape of the call ------------------------------------------------

(tu/deftest-kb a-variable-context-is-refused-rather-than-guessed
  (tu/with-terms [wabGoal N]
    (testing "the hypotheses have to hang somewhere, and `?ctx` names no context"
      (is (thrown? clojure.lang.ExceptionInfo (v/abduce kb (list wabGoal N) '?ctx))))))

(tu/deftest-kb a-conjunctive-goal-abduces-across-its-conjuncts
  (tu/with-terms [wabP wabQ N TheoryContext]
    (a-context kb TheoryContext)
    (grant kb wabP TheoryContext)
    (grant kb wabQ TheoryContext)
    (let [r (v/abduce kb [(list wabP N) (list wabQ N)] TheoryContext)]
      (testing "a vector goal is a conjunction here as it is for `prove`"
        (is (= #{(list wabP N) (list wabQ N)} (sentences r)))
        (is (seq (:solutions r)))))))

(tu/deftest-kb the-context-defaults-to-universe
  (tu/with-terms [wabGoal wabPremise N]
    (grant kb wabPremise 'UniverseContext)
    (a-rule kb [(list wabPremise '?x)] (list wabGoal '?x) 'UniverseContext)
    (let [r (v/abduce kb (list wabGoal N))]
      (is (= #{(list wabPremise N)} (sentences r)))
      (is (seq (:solutions r))))))

;; ---- the gate, asked directly ---------------------------------------------
;; `abducible?` is the decision, deliberately separate from the search so that moving it
;; onto a proof-search hook is a call-site change.  Tested as the pure predicate it is,
;; and not only through the driver.

(tu/deftest-kb the-decision-is-a-predicate-over-a-sentence
  (tu/with-terms [wabPremise N TheoryContext]
    (a-context kb TheoryContext)
    (is (not (abduce/abducible? kb (list wabPremise N) TheoryContext))
        "ungranted")
    (grant kb wabPremise TheoryContext)
    (is (abduce/abducible? kb (list wabPremise N) TheoryContext))
    (testing "and it says no to everything the driver would never hand it anyway"
      (is (not (abduce/abducible? kb (list wabPremise '?x) TheoryContext)) "open")
      (is (not (abduce/abducible? kb (list 'not (list wabPremise N)) TheoryContext))
          "a negation's functor is `not`, which nothing grants")
      (is (not (abduce/abducible? kb N TheoryContext)) "not a literal at all")
      (is (not (abduce/abducible? kb (list (list wabPremise N) N) TheoryContext))
          "a compound in functor position names no predicate, so nothing grants it"))))

(tu/deftest-kb the-depth-bound-is-the-decision-function-s-own
  (tu/with-terms [wabPremise N TheoryContext]
    (a-context kb TheoryContext)
    (grant kb wabPremise TheoryContext)
    (let [g (list wabPremise N)]
      (is (some? (abduce/maybe-abduce kb g TheoryContext {:max-depth 2} 2)) "at the bound")
      (is (nil? (abduce/maybe-abduce kb g TheoryContext {:max-depth 2} 3)) "past it")
      (testing "and no bound is no bound — `run` always supplies one, but the seam is
                written for a proof-search hook that may not"
        (is (some? (abduce/maybe-abduce kb g TheoryContext {} 99)))))))

(tu/deftest-kb retracting-the-grant-withdraws-the-permission
  (tu/with-terms [wabGoal wabPremise N TheoryContext]
    (a-context kb TheoryContext)
    (let [g (grant kb wabPremise TheoryContext)]
      (a-rule kb [(list wabPremise '?x)] (list wabGoal '?x) TheoryContext)
      (is (seq (:hypotheses (v/abduce kb (list wabGoal N) TheoryContext))))
      (v/retract! kb g)
      (testing "the grant is a belief-following prop like any other declaration, so
                taking it back takes the permission with it"
        (is (empty? (:hypotheses (v/abduce kb (list wabGoal N) TheoryContext))))))))

(tu/deftest-kb a-negation-the-asker-cannot-see-does-not-block
  (tu/with-terms [wabGoal wabPremise N TheoryContext SiblingContext]
    (a-context kb TheoryContext)
    (a-context kb SiblingContext)
    (grant kb wabPremise TheoryContext)
    (a-rule kb [(list wabPremise '?x)] (list wabGoal '?x) TheoryContext)
    (v/assert kb (list 'not (list wabPremise N)) SiblingContext {:strength :monotonic})
    (testing "the gate reads `matches-visible`, so a denial stated somewhere the asker
              cannot see is no more binding on it than an assertion there would be"
      (is (= #{(list wabPremise N)}
             (sentences (v/abduce kb (list wabGoal N) TheoryContext)))))
    (v/assert kb (list 'genlContext TheoryContext SiblingContext) 'UniverseContext)
    (testing "wire the two together and the same denial now blocks"
      (is (empty? (:hypotheses (v/abduce kb (list wabGoal N) TheoryContext)))))))

;; ---- what a kept abduction looks like to the rest of the API ---------------

(tu/deftest-kb the-hypothesis-and-what-it-licensed-are-ordinary-to-why
  (tu/with-terms [wabGoal wabPremise N TheoryContext]
    (a-context kb TheoryContext)
    (grant kb wabPremise TheoryContext)
    (a-rule kb [(list wabPremise '?x)] (list wabGoal '?x) TheoryContext)
    (let [r    (v/abduce kb (list wabGoal N) TheoryContext {:keep? true})
          h    (:handle (first (:hypotheses r)))
          c    (v/handle-of kb (list wabGoal N) (:context r))]
      (try
        (testing "the hypothesis is a premise — assumed, so justified by nothing"
          (let [w (v/why kb h)]
            (is (true? (:premise? w)))
            (is (empty? (:support w)))))
        (testing "and the conclusion's proof names it, like any other derivation"
          (let [w (v/why kb c)]
            (is (false? (:premise? w)))
            (is (some (fn [s] (some #(= (list wabPremise N) (:sentence %)) (:because s)))
                      (:support w)))))
        (finally (v/abduce-discard! kb r))))))

(tu/deftest-kb the-edge-that-makes-the-scratch-context-is-not-itself-a-hypothesis
  (tu/with-terms [wabGoal wabPremise N TheoryContext]
    (a-context kb TheoryContext)
    (grant kb wabPremise TheoryContext)
    (a-rule kb [(list wabPremise '?x)] (list wabGoal '?x) TheoryContext)
    (let [r (v/abduce kb (list wabGoal N) TheoryContext {:keep? true})
          e (v/handle-of kb (list 'genlContext (:context r) TheoryContext) 'UniverseContext)]
      (try
        (testing "which context sees which is a fact about the scratch space; a
                  defeasible edge would let a clash among the hypotheses unhook the
                  context holding them"
          (is (integer? e))
          (is (= :monotonic (v/defeat-class kb e))))
        (finally (v/abduce-discard! kb r))))))

;; ---- isolation, at its hardest -------------------------------------------

(tu/deftest-kb a-hypothesis-cannot-block-a-base-rule-firing
  (tu/with-terms [wabTrigger wabConc wabBlock wabGoal wabPremise N TheoryContext]
    (a-context kb TheoryContext)
    ;; a base rule that states its own exception, and a base fact that fires it
    (v/assert kb (list 'exceptWhen (list wabBlock '?x)
                       (list 'implies (list 'and (list wabTrigger '?x))
                             (list wabConc '?x)))
              TheoryContext)
    (v/assert kb (list wabTrigger N) TheoryContext)
    (let [c (v/handle-of kb (list wabConc N) TheoryContext)]
      (is (integer? c) "the base conclusion is there before we start")
      ;; now abduce a goal whose hypothesis is the very literal that exception asks about
      (grant kb wabBlock TheoryContext)
      (a-rule kb [(list wabBlock '?x)] (list wabGoal '?x) TheoryContext)
      (let [r (v/abduce kb (list wabGoal N) TheoryContext {:keep? true})]
        (try
          (is (= #{(list wabBlock N)} (sentences r)) "the hypothesis really was minted")
          (testing "and the base firing is untouched: the exception is evaluated in the
                    conclusion's own placement context, which is above the scratch one and
                    cannot see into it.  This is what makes isolation exact rather than
                    nearly so — blocking is the one thing that would *sweep* a base
                    conclusion, and a hypothesis has no reach to do it"
            (is (= c (v/handle-of kb (list wabConc N) TheoryContext))
                "same handle, not re-derived")
            (is (v/in? kb c)))
          (finally (v/abduce-discard! kb r)))))))

(tu/deftest-kb a-throw-mid-search-still-tears-the-scratch-context-down
  (tu/with-terms [wabGoal wabPremise N TheoryContext]
    (a-context kb TheoryContext)
    (grant kb wabPremise TheoryContext)
    (a-rule kb [(list wabPremise '?x)] (list wabGoal '?x) TheoryContext)
    (let [sx-before (tu/sentex-ids kb)
          ctxs      (set (v/contexts kb))]
      (is (thrown? RuntimeException
                   (with-redefs [res/prove (fn [& _] (throw (RuntimeException. "boom")))]
                     (v/abduce kb (list wabGoal N) TheoryContext))))
      (testing "isolation is the contract, and an exception is when it is easiest to
                lose — the context is torn down on the way out of the throw"
        (is (= sx-before (tu/sentex-ids kb)))
        (is (= ctxs (set (v/contexts kb))))
        (is (empty? (filter #(str/starts-with? (name %) "Abduction") (v/contexts kb))))))))

(tu/deftest-kb an-abduce-cap-nothing-reads-is-refused
  ;; {:max-hypothesis 2} ran at the default 8, and a misspelt :keep? tore down the
  ;; scratch context whose handles the caller meant to commit.
  (tu/with-terms [pp Aa AbContext]
    (doseq [opts [{:max-hypothesis 2} {:keep true} {:max-dpeth 3}]]
      (let [e (try (v/abduce kb (list pp Aa) AbContext opts) nil
                   (catch clojure.lang.ExceptionInfo e (ex-data e)))]
        (is (= :unknown-option (:type e)) (pr-str opts))))))

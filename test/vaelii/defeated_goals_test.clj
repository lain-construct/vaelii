;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.defeated-goals-test
  "**The proving levels agree with belief.**

  Tweety is a penguin, penguins do not fly, and birds fly by default — so `(flies
  Tweety)` is stored, has a perfectly good derivation, and is *defeated*: the JTMS forced
  it OUT and kept its support for revival.  Ask the KB whether Tweety flies and the answer
  is no.

  The backward chainers filter *rules* by belief and *facts* by belief, and until an
  answer is one of those two they filter nothing — so opening the rule that concluded the
  defeated side and proving it again would answer yes, and `prove` / `query` would
  disagree with `ask` about the same KB.  What is pinned here is that they do not:

    * `prove`, `query` at a depth, `provable?` and `argue` all answer the believed side
      and only that one, on both query engines;
    * a rule whose antecedent is the defeated side does not fire on it either — the
      check is on the answers a subgoal produces, not a filter over the top-level ones;
    * `ask` agrees, since level 6 expands no rule and reads belief;
    * a datum that **revives** — the defeater retracted — is answered again, with nothing
      else having changed;
    * and none of it depends on when the defeater arrived."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.rules :as vr]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(def ^:private C 'CxUniverse)

(defn- default-rule
  "A `set/defaultRule`, whose firings confer `:default` — the wrapper is what makes a
  rule defeasible, where a bare one confers `:monotonic` and is capped by its weakest
  antecedent."
  [antes conseq]
  (list 'set/defaultRule (vr/rule-sentence antes conseq)))

(defn- flying-world
  "Birds fly by default; penguins do not; Tweety is a penguin and Robin a plain bird.
  So `(flies Tweety)` is derived, stored, and defeated by the monotonic `(not (flies
  Tweety))` the penguin rule concludes — while `(flies Robin)` stands."
  [kb {:keys [bird penguin flies Tweety Robin]}]
  (v/assert kb (list 'genl penguin bird) C)
  (v/assert kb (default-rule [(list bird '?x)] (list flies '?x)) C)
  (v/assert-rule kb [(list penguin '?x)] (list 'not (list flies '?x)) C)
  (v/assert kb (list penguin Tweety) C {:strength :monotonic})
  (v/assert kb (list bird Robin) C {:strength :monotonic}))

(defn- believed [kb pred]
  (set (map :sentence (v/sentexes-with-functor kb pred {:believed? true}))))

(defn- answers [rs] (set (map #(get % '?x) rs)))

;; ---- does Tweety fly? ----------------------------------------------------

(tu/deftest-kb the-defeated-side-is-stored-and-not-believed
  ;; The premise every test below rests on: this is a defeat, not an absence.
  (tu/with-terms [bird penguin flies Tweety Robin]
    (let [terms {:bird bird :penguin penguin :flies flies :Tweety Tweety :Robin Robin}]
      (flying-world kb terms)
      (is (contains? (set (map :sentence (v/sentexes-with-functor kb flies)))
                     (list flies Tweety))
          "the default fired and its conclusion is stored")
      (is (= #{(list 'not (list flies Tweety)) (list flies Robin)} (believed kb flies))
          "and belief has settled against it"))))

(tu/deftest-kb no-proving-level-answers-that-the-penguin-flies
  (tu/with-terms [bird penguin flies Tweety Robin airborne]
    (flying-world kb {:bird bird :penguin penguin :flies flies :Tweety Tweety :Robin Robin})
    (testing "`ask` reads belief"
      (is (not (v/ask? kb (list flies Tweety) C)))
      (is (v/ask? kb (list flies Robin) C)))
    (testing "`prove` opens the rule again and must reach the same answer"
      (is (empty? (v/prove kb [(list flies Tweety)] C)))
      (is (= #{Robin} (answers (v/prove kb [(list flies '?x)] C)))))
    (testing "`provable?` with it"
      (is (not (v/provable? kb (list flies Tweety) C)))
      (is (v/provable? kb (list flies Robin) C)))
    (testing "`query` at a depth — the node engine — reaches it too"
      (is (empty? (v/query kb [(list flies Tweety)] C {:max-depth 3})))
      (is (= #{Robin} (answers (v/query kb [(list flies '?x)] C {:max-depth 3})))))
    (testing "and `argue` at a depth calls the defeated side false rather than contradicted"
      (is (= :false (:verdict (v/argue kb (list flies Tweety) C {:max-depth 3})))))
    (testing "a rule reading the defeated side does not fire on it either — the check is on
              what a subgoal answers, not on the top-level answers alone"
      (v/assert-rule kb [(list flies '?x)] (list airborne '?x) C)
      (is (= #{Robin} (answers (v/query kb [(list airborne '?x)] C {:max-depth 4})))))))

(tu/deftest-kb the-node-engine-and-the-dfs-agree-about-the-defeated-side
  ;; The parity claim written where it is about this: a tactician orders goals and does
  ;; not choose answers, and neither does a defeat.
  (tu/with-terms [bird penguin flies Tweety Robin]
    (flying-world kb {:bird bird :penguin penguin :flies flies :Tweety Tweety :Robin Robin})
    (doseq [engine [:dfs :inference :hybrid]]
      (binding [v/*query-engine* engine]
        (is (= #{Robin} (answers (v/query kb [(list flies '?x)] C {:max-depth 3})))
            (str "the " engine " engine answered the defeated side"))))))

;; ---- and when it stops being defeated ------------------------------------

(tu/deftest-kb retracting-the-defeater-makes-the-question-answerable-again
  ;; A defeat is a claim about the current state, so lifting it has to give the answer
  ;; back — otherwise this filter would be a deletion.  The defeater is a *separate*
  ;; assertion here, so retracting it leaves everything the default rested on in place.
  (tu/with-terms [bird flies Tweety]
    (v/assert kb (default-rule [(list bird '?x)] (list flies '?x)) C)
    (v/assert kb (list bird Tweety) C {:strength :monotonic})
    (let [defeater (v/assert kb (list 'not (list flies Tweety)) C {:strength :monotonic})]
      (is (empty? (v/prove kb [(list flies Tweety)] C)) "defeated, so not proved")
      (is (empty? (v/query kb [(list flies Tweety)] C {:max-depth 3})))
      (v/retract! kb defeater)
      (testing "with the defeater gone the default is believed again, and proved again"
        (is (contains? (believed kb flies) (list flies Tweety)))
        (is (seq (v/prove kb [(list flies Tweety)] C)))
        (is (seq (v/query kb [(list flies Tweety)] C {:max-depth 3})))))))

(tu/deftest-kb the-answer-does-not-depend-on-when-the-defeater-arrived
  (tu/with-terms [bird flies Tweety]
    (testing "defeater last"
      (v/assert kb (default-rule [(list bird '?x)] (list flies '?x)) C)
      (v/assert kb (list bird Tweety) C {:strength :monotonic})
      (v/assert kb (list 'not (list flies Tweety)) C {:strength :monotonic})
      (is (empty? (v/prove kb [(list flies Tweety)] C)))
      (is (empty? (v/query kb [(list flies Tweety)] C {:max-depth 3})))))
  (tu/with-terms [bird2 flies2 Tweety2]
    (testing "defeater first — same three sentences, same answer"
      (v/assert kb (list 'not (list flies2 Tweety2)) C {:strength :monotonic})
      (v/assert kb (list bird2 Tweety2) C {:strength :monotonic})
      (v/assert kb (default-rule [(list bird2 '?x)] (list flies2 '?x)) C)
      (is (empty? (v/prove kb [(list flies2 Tweety2)] C)))
      (is (empty? (v/query kb [(list flies2 Tweety2)] C {:max-depth 3}))))))

;; ---- what the filter must not reach --------------------------------------

(tu/deftest-kb a-defeat-in-a-context-this-reader-cannot-see-decides-nothing
  ;; A defeat is a claim about a stored sentex, and a reader that cannot see that sentex
  ;; is not the reader it was decided for.  Two sibling contexts: the clash is in one,
  ;; and the other's identical question is answered on its own facts.
  (tu/with-terms [bird flies Tweety CxClash CxCalm]
    (v/assert kb (list 'genlCx CxClash 'CxUniverse) C)
    (v/assert kb (list 'genlCx CxCalm 'CxUniverse) C)
    (v/assert kb (default-rule [(list bird '?x)] (list flies '?x)) 'CxUniverse)
    (v/assert kb (list bird Tweety) CxClash {:strength :monotonic})
    (v/assert kb (list bird Tweety) CxCalm  {:strength :monotonic})
    (v/assert kb (list 'not (list flies Tweety)) CxClash {:strength :monotonic})
    (testing "the clashing context does not answer the defeated side"
      (is (empty? (v/prove kb [(list flies Tweety)] CxClash))))
    (testing "and its sibling, which cannot see the clash, still does"
      (is (seq (v/prove kb [(list flies Tweety)] CxCalm))))))

;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.recover-independence-test
  "The **restart** axis of the engine's first invariant: one store, read two ways, gives
  one answer.

  `order_independence_test` asks whether the same knowledge in any order yields the same
  beliefs.  This asks the question a running process cannot: whether the KB that
  *derived* its state agrees with the KB that *rebuilt* it.  The two arrive at the
  taxonomy and the JTMS by different routes — the derivation path integrates each sentex
  as it lands, `recover` replays every stored sentex of a functor and then narrows to
  belief (docs/storage.md, \"Persistence & recovery\") — and nothing but a test compares
  them.  A cache the derivation path forgets to write is invisible until a restart writes
  it, and a cache `recover` writes from storage rather than from belief is invisible until
  a restart revives something the live KB had defeated.  Either way one store answers two
  ways, and the operator sees it as \"it worked yesterday\".

  Each test therefore reads the live KB, opens a **second KB value over the same stores**
  — whose taxonomy and JTMS start empty — recovers it, and demands the identical reading.
  Reading a map rather than a boolean, for `order_independence_test`'s reason: a
  restart that loses one of three caches still answers `true` to the one question a
  boolean asks.

  The scenarios are the ones where the two routes are known to have diverged: a member,
  an edge or a visibility `except` a **rule** concluded rather than an assert (nothing
  keys the derivation path on a functor the metatype *is*), and the two condition
  evaluations that are re-asked rather than stored, over a term whose spelling a merge
  retired."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- restarted
  "A process restart: a second KB value over the same stores, whose in-memory taxonomy
  and JTMS start empty and are rebuilt from the records alone.  `tu/test-kb` opens with
  `:recover? false`, so the rebuild is this call's and nothing else's."
  []
  (doto (tu/test-kb) (v/recover)))

(defn- one-reading!
  "Read `observe` off the live KB and off a restart of it, assert the two agree, and
  return the reading."
  [label kb observe]
  (let [live (observe kb)
        back (observe (restarted))]
    (is (= live back)
        (str label ": the restarted KB disagrees with the live one over one store — live "
             (pr-str live) ", recovered " (pr-str back)))
    live))

;; ---- a rule concluded it, and only an assert had ever been integrated ----

(tu/deftest-kb a-rule-derived-metatype-member-reads-the-same-after-a-restart
  ;; A metatype's members are cached in memory and nowhere stored — the only durable
  ;; trace is the `(M T)` sentexes — and the member arm keys on nothing a table can name,
  ;; the functor *being* the metatype.  `recover`'s member pass walks every stored `(M T)`
  ;; whatever put it there, so a derivation path that skipped the arm separated the pair
  ;; only once a restart had replayed it.
  (tu/with-terms [species dog_t cat_t seedOf]
    (v/assert kb (list 'disjoint_metatype species) 'CxUniverse)
    (v/assert kb (list species dog_t) 'CxUniverse)
    ;; `cat_t` joins the metatype by inference alone — nothing states `(species cat_t)`
    (v/assert kb (list 'implies (list seedOf '?x) (list species '?x)) 'CxUniverse)
    (v/assert kb (list seedOf cat_t) 'CxUniverse)
    (let [observe (fn [k] {:members  (tax/metatype-members (:taxonomy k) species)
                           :disjoint (v/disjoint? k dog_t cat_t)
                           :stored   (boolean (seq (v/sentexes-matching k (list species cat_t) '?c)))})
          reading (one-reading! "a rule-derived metatype member" kb observe)]
      (is (= {:members #{dog_t cat_t} :disjoint true :stored true} reading)
          "the derived membership separates the pair, and says so on both sides of a restart"))))

(tu/deftest-kb a-rule-derived-except-reads-the-same-after-a-restart
  ;; A visibility `except` is dispatched on the sentence's shape rather than out of the
  ;; special-predicate table, and the roster it writes is kept at the store primitive —
  ;; which `recover` replays and a derivation path can miss.  The rule fires first, so
  ;; there is a standing firing for the except to sweep: a cold KB computes rather than
  ;; recalls, and would hide the difference.
  (tu/with-terms [q p hide Aa Trigger CxSub]
    (v/assert kb (list 'genlCx CxSub 'CxWell) 'CxUniverse {:strength :monotonic})
    (let [h (v/assert kb (list q Aa) CxSub {:strength :monotonic})]
      (v/assert kb (list 'implies (list q '?x) (list p '?x)) CxSub {:strength :monotonic})
      (v/assert kb (list 'implies (list hide '?z) (list 'except (sx/sentex-handle h)))
                CxSub {:strength :monotonic})
      (v/assert kb (list hide Trigger) CxSub {:strength :monotonic})
      (let [observe (fn [k] {:target     (v/ask? k (list q Aa) CxSub)
                             :conclusion (boolean (seq (v/sentexes-matching k (list p Aa) CxSub)))
                             :except     (boolean (seq (v/sentexes-matching
                                                        k (list 'except (sx/sentex-handle h)) '?c)))})
            reading (one-reading! "a rule-derived visibility except" kb observe)]
        (is (= {:target false :conclusion false :except true} reading)
            "the derived except hides its target and sweeps what rested on it, either side
             of a restart")))))

(tu/deftest-kb a-rule-derived-genl-edge-reads-the-same-after-a-restart
  ;; The closure a `genl` edge feeds is derived state twice over — the edge is concluded
  ;; by a rule, and the membership answer is computed from the cached closure.  So a
  ;; restart has to re-read the concluded edge as an edge, not merely as a stored
  ;; sentence nothing consults.
  (tu/with-terms [subOf sub_t mid_t Ind]
    (v/assert kb (list 'implies (list subOf '?a '?b) (list 'genl '?a '?b)) 'CxUniverse)
    (v/assert kb (list subOf sub_t mid_t) 'CxUniverse)
    (v/assert kb (list sub_t Ind) 'CxUniverse)
    (let [observe (fn [k] {:isa   (v/isa? k Ind mid_t)
                           :genls (contains? (set (v/genls k sub_t)) mid_t)
                           :edge  (boolean (seq (v/sentexes-matching k (list 'genl sub_t mid_t) '?c)))})
          reading (one-reading! "a rule-derived genl edge" kb observe)]
      (is (= {:isa true :genls true :edge true} reading)
          "a concluded edge answers isa? like an asserted one, before and after a restart"))))

;; ---- a condition that is re-asked rather than stored --------------------

(tu/deftest-kb an-equality-merge-under-a-live-rule-reads-the-same-after-a-restart
  ;; The partition behind `rewriteOf` is a cache like the closures, and a rule standing
  ;; over the merged term is what makes losing it visible: the conclusion is stored at the
  ;; representative, and a restart that replayed the fact without the merge would answer
  ;; the retired spelling differently from the live KB that answered it through the class.
  (tu/with-terms [eqSeed eqSeen EPref EDep]
    (v/assert kb (list 'implies (list eqSeed '?x) (list eqSeen '?x)) 'CxUniverse)
    (v/assert kb (list eqSeed EDep) 'CxUniverse)
    (v/assert kb (list 'rewriteOf EPref EDep) 'CxUniverse {:strength :monotonic})
    (let [observe (fn [k] {:conclusions (set (map :sentence
                                                  (v/sentexes-matching k (list eqSeen '?x) '?c)))
                           :ask-pref    (v/ask? k (list eqSeen EPref) 'CxUniverse)
                           :ask-dep     (v/ask? k (list eqSeen EDep) 'CxUniverse)})
          reading (one-reading! "an equality merge under a live rule" kb observe)]
      (is (= 1 (count (:conclusions reading)))
          "one conclusion — the class is one term, not two")
      (is (= [true true] [(:ask-pref reading) (:ask-dep reading)])
          "and both spellings answer it, the retired one through its representative"))))

(tu/deftest-kb an-except-conjunct-over-a-merged-term-reads-the-same-after-a-restart
  ;; Nothing about an exception is stored, so it is re-evaluated — and after a restart it
  ;; is re-evaluated against a taxonomy nobody watched being built.  The conjunct names a
  ;; term the merge retired, so the block holds only where the partition was replayed and
  ;; the condition is asked under the representative.  The blocked conclusion is an
  ;; **absence**, which is the reading a restart can most easily turn into a presence.
  (tu/with-terms [xmark xseen xskip XBase XOne XTwo]
    (v/assert kb (list 'exceptWhen (list xskip XOne)
                       (list 'set/defaultRule
                             (list 'implies (list 'and (list xmark '?x)) (list xseen '?x))))
              'CxUniverse)
    (v/assert kb (list xmark XBase) 'CxUniverse)
    (v/assert kb (list 'rewriteOf XTwo XOne) 'CxUniverse)
    (v/assert kb (list xskip XTwo) 'CxUniverse)
    (let [observe (fn [k] {:seen (set (map :sentence (v/sentexes-matching k (list xseen '?x) '?c)))
                           :ask  (v/ask? k (list xseen XBase) 'CxUniverse)})
          reading (one-reading! "an exceptWhen conjunct over a merged term" kb observe)]
      (is (= {:seen #{} :ask false} reading)
          "the exception holds under the representative, and a restart does not release it")))
  (testing "and the same claim for the naf spelling of the condition"
    ;; `(unknown S)` is the polarity where the wrong answer draws a conclusion rather than
    ;; failing to withdraw one, so a restart that lost the partition would not merely fail
    ;; to block — it would believe something the live KB does not.
    (tu/with-terms [ymark yseen yskip YBase YOne YTwo]
      (v/assert kb (list 'set/defaultRule
                         (list 'implies (list 'and (list ymark '?x) (list 'unknown (list yskip YOne)))
                               (list yseen '?x)))
                'CxUniverse)
      (v/assert kb (list ymark YBase) 'CxUniverse)
      (v/assert kb (list 'rewriteOf YTwo YOne) 'CxUniverse)
      (v/assert kb (list yskip YTwo) 'CxUniverse)
      (let [observe (fn [k] {:seen (set (map :sentence (v/sentexes-matching k (list yseen '?x) '?c)))
                             :ask  (v/ask? k (list yseen YBase) 'CxUniverse)})
            reading (one-reading! "a naf condition over a merged term" kb observe)]
        (is (= {:seen #{} :ask false} reading)
            "a term with an answer under its representative is not absent, restarted either")))))

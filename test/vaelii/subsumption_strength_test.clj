;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.subsumption-strength-test
  "reasoning/26 — a subsumption should rest on its strongest path, not its shortest.

  When a firing reaches an antecedent of a different functor across the `genl` closure,
  the supporters of the edges it climbed become antecedents of the conclusion's
  justification, and their defeat classes cap it.  If two routes relate the two functors
  at different strengths — a short defeasible one and a longer monotonic one — the
  conclusion should hold at the *strongest* route's floor, not at whichever route has the
  fewest hops.  See docs/taxonomy.md, \"Strength of a subsumption path\"."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.kb :as kb]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(tu/deftest-kb a-conclusion-rests-on-the-strongest-route-not-the-shortest
  (let [ff (tu/tmp-type) mid (tu/tmp-type) af (tu/tmp-type)
        result (tu/tmp-pred) a (tu/tmp-ind)
        class-of (fn [] (some->> (v/sentexes-matching kb (list result a) 'CxU)
                                 (v/sort-by-content :context)
                                 first :id (v/defeat-class kb)))]
    ;; two routes ff ->* af: a one-hop default edge, and a two-hop monotonic chain
    (v/assert kb (list 'genl ff af) 'CxU {:strength :default})
    (v/assert kb (list 'genl ff mid) 'CxU {:strength :monotonic})
    (v/assert kb (list 'genl mid af) 'CxU {:strength :monotonic})
    ;; a bare rule (confers :monotonic) whose antecedent a sub-typed fact reaches
    (v/assert kb (list 'implies (list af '?x) (list result '?x)) 'CxU)
    (v/assert kb (list ff a) 'CxU {:strength :monotonic})
    (testing "the subsuming firing derived the conclusion at the monotonic floor"
      (is (some? (class-of)) "the firing fired")
      (is (= :monotonic (class-of))
          "it rests on the monotonic two-hop route, not the default one-hop"))
    (testing "remove the long route and it drops to :default, conclusion still believed"
      (v/retract! kb (v/handle-of kb (list 'genl mid af) 'CxU))
      (is (some? (class-of)) "still believed — the default route still reaches af")
      (is (= :default (class-of)) "now only the default one-hop route remains"))
    (testing "restore the long route and the floor climbs back"
      (v/assert kb (list 'genl mid af) 'CxU {:strength :monotonic})
      (is (= :monotonic (class-of)) "the widest route is recomputed on the edge change"))
    (testing "retracting the short route now changes nothing"
      (v/retract! kb (v/handle-of kb (list 'genl ff af) 'CxU))
      (is (= :monotonic (class-of))
          "the monotonic route was the witness all along; losing the default one is a no-op"))))

(tu/deftest-kb reach-strength-reads-the-widest-floor
  (let [ff (tu/tmp-type) mid (tu/tmp-type) af (tu/tmp-type)]
    (v/assert kb (list 'genl ff af) 'CxU {:strength :default})
    (v/assert kb (list 'genl ff mid) 'CxU {:strength :monotonic})
    (v/assert kb (list 'genl mid af) 'CxU {:strength :monotonic})
    (testing "the diagnostic read reports the strongest route's floor"
      (is (= :monotonic (kb/reach-strength kb :genl ff af nil))))
    (testing "nil for an unreachable pair, monotonic for reflexive"
      (is (nil? (kb/reach-strength kb :genl af ff nil)))
      (is (= :monotonic (kb/reach-strength kb :genl ff ff nil))
          "a term reaches itself on nothing, which is monotonically true"))))

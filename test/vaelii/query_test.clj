(ns vaelii.query-test
  "`query` — the front door — and its one dial.

  Everything here is about the *dial* and the *goal shape*, which is where the two ways
  to get this wrong live.  `query` takes the same two goal shapes `prove` takes (a
  sentence, or a vector of them that joins on shared variables) and reads one option,
  `:max-depth`, that says how far to expand rules.  The combinations therefore form a
  grid, and the tests below walk it: each goal shape at no depth, at a depth, and at a
  depth that came from a dynamic binding rather than from `opts`.

  What makes the grid worth walking rather than sampling is that a wrong cell does not
  throw.  A goal shape the depth-0 path cannot join, or a depth the resolution misses,
  produces an *empty answer* — indistinguishable, to a caller, from a KB that knows
  nothing.  So the assertions are mostly agreement assertions: the same knowledge read
  two ways has to come back the same, and `prove` is the second way."
  (:require [clojure.set :as set]
            [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.inference :as inference]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

;; ---- goal shapes: a conjunction is answerable without a depth -------------
;; A conjunction needs no rule to be a conjunction.  Both conjuncts below are stored
;; facts, so this asks nothing of the rule graph — and it is the reading `query`'s own
;; docstring calls the common case, most of a common-sense KB being facts and closures.

(tu/deftest-kb a-conjunctive-goal-answers-with-no-depth-at-all
  (tu/with-terms [parentOf dog Ann Bob Cid QContext]
    (v/assert kb (list parentOf Ann Bob) QContext)
    (v/assert kb (list parentOf Ann Cid) QContext)
    (v/assert kb (list dog Bob) QContext)
    (let [goal [(list parentOf Ann '?y) (list dog '?y)]]
      (testing "the shared variable joins — Cid is a child but not a dog"
        (is (= [{'?y Bob}] (vec (v/query kb goal QContext)))))
      (testing "and `prove`, the other reader that takes a conjunction, agrees"
        (is (= (set (v/prove kb goal QContext))
               (set (v/query kb goal QContext)))))
      (testing "`query?` reads the same conjunction rather than testing a vector"
        (is (v/query? kb goal QContext))
        (is (not (v/query? kb [(list parentOf Ann '?y) (list dog Ann)] QContext))
            "Ann is nobody's dog, so the join has no solution")))))

(tu/deftest-kb the-goal-shapes-agree-where-they-overlap
  (tu/with-terms [parentOf Ann Bob QContext]
    (v/assert kb (list parentOf Ann Bob) QContext)
    (testing "a one-element vector is the bare sentence"
      (is (= (vec (v/query kb (list parentOf Ann '?y) QContext))
             (vec (v/query kb [(list parentOf Ann '?y)] QContext)))))
    (testing "an empty conjunction proves trivially, exactly as `prove` says it does"
      (is (= [{}] (vec (v/query kb [] QContext))))
      (is (= (vec (v/prove kb [] QContext)) (vec (v/query kb [] QContext)))))
    (testing "a conjunct nothing answers empties the whole conjunction"
      (is (empty? (v/query kb [(list parentOf Ann '?y) (list parentOf '?y '?z)]
                           QContext))))))

(tu/deftest-kb a-conjunction-with-no-depth-joins-through-the-registry
  ;; The discriminating case for *which leaf* the depth-0 path uses.  `(genl a c)` here
  ;; is in the cached closure and in no stored sentex, so a conjunction that joins on it
  ;; is answered only by a leaf that is the whole prover registry — which is what `ask`
  ;; reaches for one literal, and what this must reach for several.
  (tu/with-terms [tag_a tag_b tag_c Thing QContext]
    (v/assert kb (list 'genl tag_a tag_b) QContext)
    (v/assert kb (list 'genl tag_b tag_c) QContext)
    (v/assert kb (list tag_a Thing) QContext)
    (testing "the transitive edge is derived, not stored"
      (is (empty? (v/sentexes-matching kb (list 'genl tag_a tag_c) QContext)))
      (is (v/ask? kb (list 'genl tag_a tag_c) QContext)))
    (testing "and a conjunction over it answers with no depth"
      (is (= [{'?x Thing}]
             (vec (v/query kb [(list 'genl tag_a tag_c) (list tag_a '?x)] QContext)))))))

;; ---- the dial: no depth expands no rule ---------------------------------

(tu/deftest-kb no-depth-anywhere-expands-no-rule
  (tu/with-terms [parentOf anc Ann Bob QContext]
    (v/assert kb (list parentOf Ann Bob) QContext)
    ;; backward, so no forward firing stores the conclusion and the only way to it is a
    ;; backchainer looking for it
    (v/assert-rule kb [(list parentOf '?x '?y)] (list anc '?x '?y) QContext
                   {:direction :backward})
    (let [goal (list anc Ann '?z)]
      (testing "with no depth the rule is not expanded, and that is the contract"
        (is (empty? (v/query kb goal QContext)))
        (is (not (v/query? kb goal QContext))))
      (testing "a depth reaches it"
        (is (= [{'?z Bob}] (vec (v/query kb goal QContext {:max-depth 1})))))
      (testing "and `prove`, which needs no depth, reaches it too"
        (is (= [{'?z Bob}] (vec (v/prove kb goal QContext))))))))

(tu/deftest-kb a-depth-may-come-from-a-dynamic-binding
  ;; The depth is a decision, and a caller makes it in one of three places.  Missing one
  ;; of them is invisible: the read just answers whatever needs no rule.
  (tu/with-terms [parentOf anc Ann Bob Cid QContext]
    (v/assert kb (list parentOf Ann Bob) QContext)
    (v/assert kb (list parentOf Bob Cid) QContext)
    (v/assert-rule kb [(list parentOf '?x '?z)] (list anc '?x '?z) QContext
                   {:direction :backward})
    (v/assert-rule kb [(list parentOf '?x '?y) (list anc '?y '?z)] (list anc '?x '?z)
                   QContext {:direction :backward})
    (let [goal (list anc Ann '?z)
          zs   #(set (map (fn [s] (get s '?z)) %))]
      (testing "`opts`"
        (is (= #{Bob Cid} (zs (v/query kb goal QContext {:max-depth 3})))))
      (testing "`*query-options*` :max-depth — where `prove` reads a depth from too"
        (is (= #{Bob Cid} (binding [v/*query-options* {:max-depth 3}]
                            (zs (v/query kb goal QContext))))))
      (testing "`inference/*max-depth*`"
        (is (= #{Bob Cid} (binding [inference/*max-depth* 3]
                            (zs (v/query kb goal QContext))))))
      (testing "`opts` wins over a dynamic one rather than being merged with it"
        (is (= #{Bob} (binding [v/*query-options* {:max-depth 3}]
                        (zs (v/query kb goal QContext {:max-depth 1}))))
            "depth 1 admits one hop, so the two-hop ancestor is out of reach"))
      (testing "a *query-options* naming only a strategy leaves the depth unset"
        (is (empty? (binding [v/*query-options* :depth-first]
                      (v/query kb goal QContext))))
        (is (= #{Bob Cid} (binding [v/*query-options* :depth-first]
                            (zs (v/query kb goal QContext {:max-depth 3})))))))))

(tu/deftest-kb a-bounded-query-answers-a-subset-of-what-prove-answers
  ;; The two engines terminate on different things — `query` on its bound, `prove` on the
  ;; data — so within the bound they must agree, and past it `prove` may know more.  A
  ;; disagreement in the other direction would mean the bounded engine inventing an
  ;; answer.
  (tu/with-terms [parentOf anc QContext]
    (let [n (fn [i] (symbol (str "TmpQChain" i)))]
      (doseq [i (range 5)] (v/assert kb (list parentOf (n i) (n (inc i))) QContext))
      (v/assert-rule kb [(list parentOf '?x '?z)] (list anc '?x '?z) QContext
                     {:direction :backward})
      (v/assert-rule kb [(list parentOf '?x '?y) (list anc '?y '?z)] (list anc '?x '?z)
                     QContext {:direction :backward})
      (let [goal    (list anc (n 0) '?z)
            proved  (set (v/prove kb goal QContext))
            bounded #(set (v/query kb goal QContext {:max-depth %}))]
        (testing "every depth answers a subset of the unbounded search"
          (doseq [d (range 1 7)]
            (is (empty? (set/difference (bounded d) proved))
                (str "depth " d " answered something `prove` did not"))))
        (testing "and a deep enough bound catches up with it exactly"
          (is (= proved (bounded 6))))
        (testing "while a shallow one is a strict subset"
          (is (< (count (bounded 1)) (count proved))))))))

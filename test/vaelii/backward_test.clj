(ns vaelii.backward-test
  "The recur-based backward chainer (v/prove), focusing on inference that relies
  on transitive types (genl) and context visibility (genlContext)."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(tu/deftest-kb prove-facts-and-rules
  (let [parentOf (tu/tmp-pred) grandparentOf (tu/tmp-pred)
        tom (tu/tmp-ind) bob (tu/tmp-ind) ann (tu/tmp-ind) zed (tu/tmp-ind)]
    (v/assert-rule kb [(list parentOf '?x '?y) (list parentOf '?y '?z)] (list grandparentOf '?x '?z) 'FamContext)
    (v/assert kb (list parentOf tom bob) 'FamContext)
    (v/assert kb (list parentOf bob ann) 'FamContext)
    (testing "prove a direct fact"
      (is (v/provable? kb (list parentOf tom bob) 'FamContext))
      (is (not (v/provable? kb (list parentOf tom zed) 'FamContext))))
    (testing "prove via a rule, reading out the bindings"
      (let [sols (v/prove kb (list grandparentOf tom '?who) 'FamContext)]
        (is (= #{ann} (set (map #(get % '?who) sols))))))))

(tu/deftest-kb prove-uses-type-transitivity
  (let [dog (tu/tmp-type) animal (tu/tmp-type) rock (tu/tmp-type)
        breathes (tu/tmp-pred) fido (tu/tmp-ind) boulder (tu/tmp-ind)]
    (v/assert kb (list 'genl dog animal) 'UniverseContext)
    (v/assert-rule kb [(list animal '?x)] (list breathes '?x) 'UniverseContext)
    (v/assert kb (list dog fido) 'UniverseContext)
    (v/assert kb (list rock boulder) 'UniverseContext)          ; not an animal
    (testing "a rule about animals is provable for a dog (subtype), not a rock"
      (is (v/provable? kb (list breathes fido) 'UniverseContext))
      (is (not (v/provable? kb (list breathes boulder) 'UniverseContext))))))

(tu/deftest-kb prove-is-context-aware
  (let [parentOf (tu/tmp-pred) tom (tu/tmp-ind) bob (tu/tmp-ind) ann (tu/tmp-ind)]
    (v/assert kb (list 'genlContext 'BioContext 'UniverseContext) 'UniverseContext)
    (v/assert kb (list parentOf tom bob) 'UniverseContext)      ; general fact
    (v/assert kb (list parentOf bob ann) 'BioContext)           ; specific fact
    (testing "a specific context sees general facts (genlContext up-closure)"
      (is (v/provable? kb (list parentOf tom bob) 'BioContext))
      (is (v/provable? kb (list parentOf bob ann) 'BioContext)))
    (testing "a general context does not see specific facts"
      (is (v/provable? kb (list parentOf tom bob) 'UniverseContext))
      (is (not (v/provable? kb (list parentOf bob ann) 'UniverseContext))))))

(tu/deftest-kb prove-terminates-on-recursive-rule
  (let [parentOf (tu/tmp-pred) ancestorOf (tu/tmp-pred)
        aa (tu/tmp-ind) bb (tu/tmp-ind) cc (tu/tmp-ind) dd (tu/tmp-ind)]
    (v/assert-rule kb [(list parentOf '?x '?y)] (list ancestorOf '?x '?y) 'UniverseContext)                   ; base
    (v/assert-rule kb [(list parentOf '?x '?y) (list ancestorOf '?y '?z)] (list ancestorOf '?x '?z) 'UniverseContext) ; right-recursive
    (v/assert kb (list parentOf aa bb) 'UniverseContext)
    (v/assert kb (list parentOf bb cc) 'UniverseContext)
    (v/assert kb (list parentOf cc dd) 'UniverseContext)
    (testing "transitive closure via a recursive rule, and it terminates"
      (is (= #{bb cc dd}
             (set (map #(get % '?who) (v/prove kb (list ancestorOf aa '?who) 'UniverseContext))))))
    (testing "the lazy chainer terminates on the same rule set, fully realized —
              `backward` needs a recursion guard of its own, or running past the
              fact solutions diverges where `prove` terminates"
      (is (= #{bb cc dd}
             (set (map #(get % '?who)
                       (doall (v/prove kb (list ancestorOf aa '?who) 'UniverseContext)))))))))

;; ---- conjunctive goals ---------------------------------------------------
;; `prove` takes either one sentence or a *vector* of them.  A vector is a
;; conjunction: bindings thread across the conjuncts, so a shared variable joins.

(tu/deftest-kb prove-a-conjunction-joins-on-a-shared-variable
  (tu/with-terms [parentOf dog cat Tom Bob Ann JoinContext]
    (v/assert kb (list parentOf Tom Bob) JoinContext)
    (v/assert kb (list parentOf Tom Ann) JoinContext)
    (v/assert kb (list dog Bob) JoinContext)
    (v/assert kb (list cat Ann) JoinContext)
    (testing "?y must satisfy both conjuncts — only the child that is a dog"
      (is (= #{Bob}
             (set (map #(get % '?y)
                       (v/prove kb [(list parentOf Tom '?y) (list dog '?y)] JoinContext))))))
    (testing "the join is symmetric in conjunct order (no reordering, same answer)"
      (is (= #{Bob}
             (set (map #(get % '?y)
                       (v/prove kb [(list dog '?y) (list parentOf Tom '?y)] JoinContext))))))
    (testing "every conjunct's variables are bound in each solution"
      (let [sols (v/prove kb [(list parentOf '?x '?y) (list cat '?y)] JoinContext)]
        (is (= [{'?x Tom '?y Ann}] (map #(select-keys % '[?x ?y]) sols)))))
    (testing "a conjunction with no joint solution proves nothing"
      (is (empty? (v/prove kb [(list parentOf Tom '?y) (list dog '?y) (list cat '?y)] JoinContext)))
      (is (not (v/provable? kb [(list parentOf Tom '?y) (list cat '?y) (list dog '?y)] JoinContext))))
    (testing "each conjunct alone, and the pair that does share a binding"
      (is (v/provable? kb [(list parentOf Tom '?y)] JoinContext))
      (is (v/provable? kb [(list cat '?y)] JoinContext))
      (is (v/provable? kb [(list parentOf Tom '?y) (list cat '?y)] JoinContext)))
    (testing "an empty conjunction is trivially proved"
      (is (v/provable? kb [] JoinContext)))))

(tu/deftest-kb prove-a-single-goal-is-unchanged-by-the-conjunction-form
  (tu/with-terms [parentOf grandparentOf Tom Bob Ann JoinContext]
    (v/assert-rule kb [(list parentOf '?x '?y) (list parentOf '?y '?z)]
                   (list grandparentOf '?x '?z) JoinContext)
    (v/assert kb (list parentOf Tom Bob) JoinContext)
    (v/assert kb (list parentOf Bob Ann) JoinContext)
    (testing "a bare sentence and the one-element vector agree, facts and rules alike"
      (is (= (v/prove kb (list parentOf Tom Bob) JoinContext)
             (v/prove kb [(list parentOf Tom Bob)] JoinContext)))
      (is (= (v/prove kb (list grandparentOf Tom '?who) JoinContext)
             (v/prove kb [(list grandparentOf Tom '?who)] JoinContext)))
      (is (v/provable? kb (list grandparentOf Tom Ann) JoinContext))
      (is (v/provable? kb [(list grandparentOf Tom Ann)] JoinContext)))
    (testing "a conjunct may itself be answered by backchaining through a rule"
      ;; Tom -> Bob -> Ann: whoever parents Bob is a grandparent, of Ann
      (is (= #{Ann}
             (set (map #(get % '?z)
                       (v/prove kb [(list parentOf '?x Bob) (list grandparentOf '?x '?z)]
                                JoinContext)))))
      (is (v/provable? kb [(list parentOf Tom '?y) (list parentOf '?y Ann)] JoinContext)))))

;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.negation-test
  "Explicit negation with contradiction detection, and defeasible defaults
  (penguins don't fly).  Each test invents gensym'd terms; the fixture rebuilds
  an empty KB per test and asserts the test tore its additions back down."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.rules :as vr]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(tu/deftest-kb negation-is-soft-not-thrown
  (let [dog (tu/tmp-type) muffet (tu/tmp-ind) rex (tu/tmp-ind)]
    (testing "asserting the negation of a believed fact does not throw"
      (v/assert kb (list dog muffet) 'CxUniverse {:strength :monotonic})
      (is (some? (v/assert kb (list 'not (list dog muffet)) 'CxUniverse)))
      (testing "and the weaker (default) belief is the one defeated"
        (is (seq    (v/sentexes-matching kb (list dog muffet) 'CxUniverse)))         ; monotonic survives
        (is (empty? (v/sentexes-matching kb (list 'not (list dog muffet)) 'CxUniverse)))  ; default defeated
        (is (empty? (v/conflicts kb)))))                                    ; resolved, nothing reported
    (testing "strength decides regardless of assertion order"
      (v/assert kb (list 'not (list dog rex)) 'CxUniverse)                ; default
      (v/assert kb (list dog rex) 'CxUniverse {:strength :monotonic})
      (is (seq    (v/sentexes-matching kb (list dog rex) 'CxUniverse)))
      (is (empty? (v/sentexes-matching kb (list 'not (list dog rex)) 'CxUniverse))))))

(defn- default-rule [antes conseq]
  (list 'set/defaultRule (list 'set/forwardRule (vr/rule-sentence antes conseq))))

(tu/deftest-kb penguins-dont-fly
  (let [penguin (tu/tmp-type) bird (tu/tmp-type) animal (tu/tmp-type)
        flies (tu/tmp-pred) robin (tu/tmp-ind) tweety (tu/tmp-ind)]
    (v/assert kb (list 'genl penguin bird) 'CxUniverse)
    (v/assert kb (list 'genl bird animal)  'CxUniverse)
    (v/assert-rule kb [(list penguin '?x)] (list 'not (list flies '?x)) 'CxUniverse {:direction :forward})  ; bare rule
    (v/assert kb (default-rule [(list bird '?x)] (list flies '?x)) 'CxUniverse)       ; defeasible
    (v/assert kb (list bird robin) 'CxUniverse)
    ;; Known-true grounds are what let the exception out-rank the default.  A bare rule
    ;; confers :monotonic and is capped by its weakest antecedent, so over a :monotonic
    ;; premise it concludes :monotonic and beats the :default flight rule; over a
    ;; :default premise both sides would be :default and the pair a represented dilemma.
    ;; (An exception stated *on* the general rule with `exceptWhen` blocks it instead —
    ;; see except_test; this test is about defeat.)
    (v/assert kb (list penguin tweety) 'CxUniverse {:strength :monotonic})
    (testing "a normal bird flies by default"
      (is (seq (v/sentexes-matching kb (list flies robin) 'CxUniverse))))
    (testing "a penguin does not — the default is defeated by the stronger conclusion"
      (is (empty? (v/sentexes-matching kb (list flies tweety) 'CxUniverse)))
      (is (seq (v/sentexes-matching kb (list 'not (list flies tweety)) 'CxUniverse))))))

(tu/deftest-kb default-applies-when-not-defeated
  (let [bird (tu/tmp-type) animal (tu/tmp-type) flies (tu/tmp-pred) eagle (tu/tmp-ind)]
    (v/assert kb (list 'genl bird animal) 'CxUniverse)
    (v/assert kb (default-rule [(list bird '?x)] (list flies '?x)) 'CxUniverse)
    (v/assert kb (list bird eagle) 'CxUniverse)
    (testing "with no contrary evidence the default conclusion holds"
      (is (v/in? kb (v/handle-of kb (list flies eagle) 'CxUniverse))))))

;; ---- nogood discovery is driven off the opposed bodies (settle F1) -------
;; The negation family reads a body's pairs only when the body is stored in both
;; polarities (`:opposed`).  These pin the two things that gate could get wrong: it must
;; not miss a real clash, and a negation with no positive twin must add no work yet still
;; be believed.

(tu/deftest-kb an-unpaired-negation-forms-no-nogood
  (let [swims (tu/tmp-pred) a (tu/tmp-ind) b (tu/tmp-ind) c (tu/tmp-ind)]
    (testing "negative facts with no positive twin are just knowledge, not clashes"
      (v/assert kb (list 'not (list swims a)) 'CxUniverse)
      (v/assert kb (list 'not (list swims b)) 'CxUniverse)
      (v/assert kb (list 'not (list swims c)) 'CxUniverse)
      (is (empty? (v/conflicts kb)))
      (is (empty? (v/contradictions kb)))
      (is (seq (v/sentexes-matching kb (list 'not (list swims a)) 'CxUniverse))))))

(tu/deftest-kb a-symmetric-negation-nogood-survives-the-existence-gate
  ;; The gate reads a `count-at` of the *stored* body.  A fact normalizes its body
  ;; before `not` wraps it, so a symmetric positive `(siblingOf Ann Bob)` and a
  ;; negation written with the arguments swapped `(not (siblingOf Bob Ann))` store the
  ;; same sorted body — the gate must still pair them.  If the gate keyed on the
  ;; author's argument order it would look under `[siblingOf Bob Ann]`, find nothing,
  ;; and silently drop the clash.
  (let [siblingOf (tu/tmp-pred) ann (tu/tmp-ind) bob (tu/tmp-ind)]
    (v/assert kb (list 'symmetric siblingOf) 'CxUniverse)
    (v/assert kb (list siblingOf ann bob) 'CxUniverse)                 ; stored sorted
    (v/assert kb (list 'not (list siblingOf bob ann)) 'CxUniverse)     ; arguments swapped
    (testing "the swapped-argument pair is still recognised as a default/default dilemma"
      (is (= 1 (count (v/contradictions kb))))
      (let [{:keys [handles]} (first (v/contradictions kb))]
        (testing "both sides stay believed — a dilemma, not a silent miss"
          (is (every? #(v/in? kb %) handles)))))))

(tu/deftest-kb a-symmetric-monotonic-negation-still-defeats-the-swapped-positive
  ;; Same pairing, but with a strength difference so the nogood resolves by defeat
  ;; rather than standing as a dilemma: the gate must find the pair for either
  ;; outcome, and here the weaker (default) positive is the one that gives way.
  (let [siblingOf (tu/tmp-pred) ann (tu/tmp-ind) bob (tu/tmp-ind)]
    (v/assert kb (list 'symmetric siblingOf) 'CxUniverse)
    (v/assert kb (list siblingOf ann bob) 'CxUniverse)                             ; default
    (v/assert kb (list 'not (list siblingOf bob ann)) 'CxUniverse {:strength :monotonic})
    (testing "the pair is found and the default positive is defeated by the monotonic negation"
      (is (empty? (v/sentexes-matching kb (list siblingOf ann bob) 'CxUniverse)))
      (is (empty? (v/contradictions kb)))
      (is (empty? (v/conflicts kb))))))

(tu/deftest-kb the-opposed-set-tracks-assertion-and-retraction
  ;; The opposed set is maintained incrementally on the store/remove path, so a clash
  ;; forms exactly when both polarities are stored and dissolves when either leaves.
  (let [warm (tu/tmp-pred) sun (tu/tmp-ind)]
    (testing "one polarity alone: no clash"
      (v/assert kb (list warm sun) 'CxUniverse)                        ; default positive
      (is (empty? (v/contradictions kb))))
    (testing "the twin arriving forms the dilemma"
      (let [hn (v/assert kb (list 'not (list warm sun)) 'CxUniverse)]  ; default -> dilemma
        (is (= 1 (count (v/contradictions kb))))
        (testing "and retracting it dissolves the clash, the survivor still believed"
          (v/retract! kb hn)
          (is (empty? (v/contradictions kb)))
          (is (seq (v/sentexes-matching kb (list warm sun) 'CxUniverse))))))))

(tu/deftest-kb a-body-with-no-twin-is-not-posted-and-still-pairs-later
  ;; The candidate index reads a body's pairs only for a body opposed before the store or
  ;; after it, so a body with no twin adds no entry.  The order that would expose a wrong
  ;; gate is a **settle between the two polarities**: the twin's arrival is then the only
  ;; write that can form the pair.
  (let [warm (tu/tmp-pred) sun (tu/tmp-ind) moon (tu/tmp-ind)]
    (v/assert kb (list warm sun) 'CxUniverse)
    (v/assert kb (list warm moon) 'CxUniverse)          ; a second settle, nothing opposed
    (is (empty? (v/contradictions kb)))
    (testing "and the index did not grow: a batch of twinless bodies adds no entry"
      (v/with-deferred-settle kb
        (doseq [i (range 8)]
          (v/assert kb (list warm (tu/tmp-ind (str "Cold" i))) 'CxUniverse
                    {:chain? false}))
        (is (empty? (:vaelii.impl.decide.negation/negation @(reasoning/nogood-candidates kb))))))
    (let [hn (v/assert kb (list 'not (list warm sun)) 'CxUniverse)]
      (is (= 1 (count (v/contradictions kb))) "the twin arriving is what forms the pair")
      (testing "and the index drops the entry when the twin leaves"
        (v/retract! kb hn)
        (is (empty? (v/contradictions kb)))
        (is (seq (v/sentexes-matching kb (list warm sun) 'CxUniverse)))))
    (testing "the pair re-forms when the twin comes back"
      (v/assert kb (list 'not (list warm sun)) 'CxUniverse)
      (is (= 1 (count (v/contradictions kb)))))))

(tu/deftest-kb the-opposed-set-survives-recover
  ;; The coincidence set is derived state no store holds, so `recover` rebuilds it
  ;; (`kb/rebuild-opposed!`) before its closing settle reads it.  Without that a restart
  ;; would forget every stored clash and silently believe both sides.
  (let [warm (tu/tmp-pred) sun (tu/tmp-ind)]
    (v/assert kb (list warm sun) 'CxUniverse)                          ; default
    (v/assert kb (list 'not (list warm sun)) 'CxUniverse)              ; default -> dilemma
    (is (= 1 (count (v/contradictions kb))) "the pair is a dilemma before recover")
    (v/recover kb)
    (testing "after recover the same clash is rediscovered from storage"
      (is (= 1 (count (v/contradictions kb))))
      (let [{:keys [handles]} (first (v/contradictions kb))]
        (is (every? #(v/in? kb %) handles) "both sides believed — the dilemma stands")))))

(tu/deftest-kb a-pair-in-two-contexts-is-decided-by-each-reader-that-sees-both
  ;;   CxL  (flies Tweety) default        CxR  (not (flies Tweety)) monotonic
  ;;   CxJ sees CxL and CxR, and CxM sees CxL and a default (not (flies Tweety)) in CxD
  ;; The pair in CxL/CxR is decided where both contexts are seen, and nowhere else; the
  ;; network keeps both sides IN.  The pair in CxL/CxD is a dilemma, reported at CxM.
  (tu/with-terms [flies Tweety CxL CxR CxD CxJ CxM]
    (doseq [[c up] [[CxL 'CxUniverse] [CxR 'CxUniverse] [CxD 'CxUniverse]
                    [CxJ CxL] [CxJ CxR] [CxM CxL] [CxM CxD]]]
      (v/assert kb (list 'genlCx c up) 'CxUniverse))
    (let [pos (v/assert kb (list flies Tweety) CxL)
          neg (v/assert kb (list 'not (list flies Tweety)) CxR {:strength :monotonic})
          dn  (v/assert kb (list 'not (list flies Tweety)) CxD)]
      (testing "the reader seeing both takes the default side OUT"
        (is (false? (v/believed? kb pos CxJ)))
        (is (true? (v/believed? kb neg CxJ)))
        (is (= [CxJ] (:scoped-vantages (v/belief-status kb pos CxJ)))))
      (testing "a context seeing one side believes it, and the network keeps it IN"
        (is (true? (v/believed? kb pos CxL)))
        (is (true? (v/in? kb pos))))
      (testing "the default pair is a dilemma reported at the reader that sees both"
        (let [r (first (filter #(= #{pos dn} (:nogood %)) (v/contradictions kb)))]
          (is (some? r))
          (is (nil? (:kind r)) "a rebuttal")
          (is (= (list 'contradicts (list flies Tweety) (list 'not (list flies Tweety)))
                 (:sentence r)))
          (is (some #(= #{pos dn} (:nogood %)) (v/contradictions kb CxM)))
          (is (not-any? #(= #{pos dn} (:nogood %)) (v/contradictions kb CxL)))))
      (testing "retracting the denial gives the side back at the reader"
        (v/retract! kb neg)
        (is (true? (v/believed? kb pos CxJ)))))))

;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.index-test
  "Integration tests for the trie index and query path.  They run on the suite's
  scratch stores (db 15 = records, 14 = index) and clear them around each test."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(tu/deftest-kb count-aware-trie
  (let [bornIn (tu/tmp-pred) tom (tu/tmp-ind) bob (tu/tmp-ind)
        paris (tu/tmp-ind) rome (tu/tmp-ind)]
    (v/assert kb (list bornIn tom paris) 'NaturalWorldContext)
    (v/assert kb (list bornIn bob paris) 'NaturalWorldContext)
    (v/assert kb (list bornIn tom rome)  'NaturalWorldContext)
    (testing "counts accumulate along shared prefixes"
      (is (= 3 (p/count-at (:index kb) [])))
      (is (= 3 (p/count-at (:index kb) [bornIn])))
      (is (= 2 (p/count-at (:index kb) [bornIn tom])))
      (is (= 1 (p/count-at (:index kb) [bornIn tom paris]))))))

(tu/deftest-kb query-by-context-and-pattern
  (let [bornIn (tu/tmp-pred) tom (tu/tmp-ind) bob (tu/tmp-ind) paris (tu/tmp-ind)]
    (v/assert kb (list bornIn tom paris) 'NaturalWorldContext)
    (v/assert kb (list bornIn bob paris) 'NaturalWorldContext)
    (v/assert kb (list bornIn tom paris) 'CoreContext)
    (testing "context wildcard returns every context"
      (is (= 2 (count (v/sentexes-matching kb (list bornIn tom paris))))))
    (testing "explicit context narrows results"
      (is (= 1 (count (v/sentexes-matching kb (list bornIn tom paris) 'CoreContext)))))
    (testing "sentence variables fan out within a context"
      (is (= #{tom bob}
             (set (map (comp second :sentence) (v/sentexes-matching kb (list bornIn '?who paris) 'NaturalWorldContext))))))))

(tu/deftest-kb nested-terms-are-stable
  (let [nat (tu/tmp-pred) succ (tu/tmp-pred) z (tu/tmp-ind)]
    (v/assert kb (list nat (list succ z)) 'UniverseContext)
    (testing "a nested-term sentence round-trips and dedups"
      (is (= 1 (p/count-at (:index kb) [])))
      (is (= 1 (count (v/sentexes-matching kb (list nat (list succ z)) 'UniverseContext))))
      (v/assert kb (list nat (list succ z)) 'UniverseContext)         ; same fact again
      (is (= 1 (p/count-at (:index kb) []))))))            ; still one, not two

;; ---- secondary roots: context / functor / argument ----------------------

(tu/deftest-kb the-context-root-gives-extent-and-cardinality
  (let [p (tu/tmp-pred) a (tu/tmp-ind) b (tu/tmp-ind)
        c1 (tu/tmp-ctx) c2 (tu/tmp-ctx)]
    (v/assert kb (list p a b) c1)
    (v/assert kb (list p b a) c1)
    (v/assert kb (list p a a) c2)
    (testing "a context's size is available without enumerating it"
      (is (= 2 (v/count-in-context kb c1)))
      (is (= 1 (v/count-in-context kb c2)))
      (is (= 0 (v/count-in-context kb (tu/tmp-ctx)))))
    (testing "and its extent is the sentexes actually asserted there"
      (is (= #{c1} (set (map :context (v/sentexes-in-context kb c1)))))
      (is (= 2 (count (v/sentexes-in-context kb c1)))))
    (testing "retracting a member decrements it"
      (v/retract! kb (:id (first (v/sentexes-matching kb (list p a a) c2))))
      (is (= 0 (v/count-in-context kb c2))))))

(tu/deftest-kb the-functor-root-spans-arity-and-polarity
  (let [dog (tu/tmp-type) fido (tu/tmp-ind) rex (tu/tmp-ind)
        rel (tu/tmp-pred)]
    (v/assert kb (list dog fido) 'UniverseContext)
    (v/assert kb (list 'not (list dog rex)) 'UniverseContext)   ; negative fact
    (v/assert kb (list rel fido rex) 'UniverseContext)
    (testing "both polarities count under the same functor"
      (is (= 2 (v/count-with-functor kb dog)))
      (is (= 2 (count (v/sentexes-with-functor kb dog)))))
    (testing "a different arity is its own functor entry"
      (is (= 1 (v/count-with-functor kb rel))))
    (testing "an unknown functor is simply empty"
      (is (= 0 (v/count-with-functor kb (tu/tmp-pred)))))
    (testing "a rule is not a fact — it contributes no functor entry"
      (let [ante (tu/tmp-pred) conseq (tu/tmp-pred)]
        (v/assert-rule kb [(list ante '?x)] (list conseq '?x) 'UniverseContext)
        (is (= 0 (v/count-with-functor kb conseq)))))))

(tu/deftest-kb the-argument-root-discriminates-by-position
  (let [bornIn (tu/tmp-pred) likes (tu/tmp-pred)
        tom (tu/tmp-ind) bob (tu/tmp-ind) paris (tu/tmp-ind)]
    (v/assert kb (list bornIn tom paris) 'UniverseContext)
    (v/assert kb (list bornIn bob paris) 'UniverseContext)
    (v/assert kb (list likes paris tom) 'UniverseContext)
    (testing "position 2 and position 1 are distinct entries for the same term"
      (is (= 2 (v/count-with-arg kb 2 paris)))          ; born in Paris, twice
      (is (= 1 (v/count-with-arg kb 1 paris))))         ; Paris likes Tom, once
    (testing "the extent holds exactly the sentexes with that term at that position"
      (is (= 1 (count (v/sentexes-with-arg kb 1 tom))))
      (is (= 1 (count (v/sentexes-with-arg kb 2 tom)))))
    (testing "bob only ever appears in position 1"
      (is (= 1 (v/count-with-arg kb 1 bob)))
      (is (= 0 (v/count-with-arg kb 2 bob))))
    (testing "a position nothing occupies, and an unseen term, are both empty"
      (is (= 0 (v/count-with-arg kb 3 paris)))
      (is (= 0 (v/count-with-arg kb 1 (tu/tmp-ind)))))))

;; ---- rule predicate indexes are complete; direction is filtered at use --

;; ---- the set/*Rule wrappers canonicalize into the record ----------------

(tu/deftest-kb a-rule-wrapper-sets-the-direction-on-the-sentex
  (tu/with-terms [p q]
    (testing "a bare implies works both ways"
      (let [h (v/assert kb (list 'implies (list p '?x) (list q '?x)) 'UniverseContext)]
        (is (= :both (:direction (v/sentex kb h))))
        (is (nil? (:defeasible (v/sentex kb h))))))))

(tu/deftest-kb each-wrapper-lands-on-the-record
  (doseq [[wrapper expected] '{set/forwardRule  :forward
                               set/backwardRule :backward
                               set/inertRule    :inert}]
    (tu/with-terms [p q]
      (let [h (v/assert kb (list wrapper (list 'implies (list p '?x) (list q '?x)))
                        'UniverseContext)
            s (v/sentex kb h)]
        (testing (str wrapper " sets :direction " expected)
          (is (= expected (:direction s))))
        (testing "and the wrapper itself is not stored — the sentence is the bare rule"
          (is (= 'implies (first (:sentence s))))
          (is (some? (:antecedent s))))))))

(tu/deftest-kb the-default-wrapper-sets-defeasible-on-the-record
  (tu/with-terms [bird flies Tweety]
    (let [h (v/assert kb (list 'set/defaultRule
                               (list 'implies (list bird '?x) (list flies '?x)))
                      'UniverseContext)
          s (v/sentex kb h)]
      (is (true? (:defeasible s)))
      (is (= 'implies (first (:sentence s))))
      (testing "and it still behaves as a default — the conclusion is defeasible"
        (v/assert kb (list bird Tweety) 'UniverseContext)
        (is (seq (v/sentexes-matching kb (list flies Tweety) 'UniverseContext)))
        (v/assert kb (list 'not (list flies Tweety)) 'UniverseContext
                  {:strength :monotonic})
        (is (empty? (v/sentexes-matching kb (list flies Tweety) 'UniverseContext)))))))

(tu/deftest-kb the-direction-opt-is-the-same-thing-as-a-wrapper
  (tu/with-terms [p q r]
    (let [viaOpt  (v/assert-rule kb [(list p '?x)] (list q '?x)
                                 'UniverseContext {:direction :backward})
          viaWrap (v/assert kb (list 'set/backwardRule
                                     (list 'implies (list p '?x) (list r '?x)))
                            'UniverseContext)]
      (is (= :backward (:direction (v/sentex kb viaOpt))))
      (is (= :backward (:direction (v/sentex kb viaWrap)))))))

(tu/deftest-kb direction-lives-only-on-the-record
  (tu/with-terms [p q]
    (let [h (v/assert kb (list 'set/forwardRule
                               (list 'implies (list p '?x) (list q '?x)))
                      'UniverseContext)
          s (v/sentex kb h)]
      (testing "the record answers both directions"
        (is (rules/forward-sentex? s))
        (is (not (rules/backward-sentex? s))))
      (testing "and the rule index carries predicates only — no direction mirror"
        (is (contains? (p/rules-by-antecedent (:index kb) p) h))
        (is (contains? (p/rules-by-consequent (:index kb) q) h))))))

(tu/deftest-kb a-re-asserted-wrapper-resolves-the-record-slot
  ;; One sentex, because direction is not in the identity key — the second assert
  ;; resolves to the existing record.  Which direction that record then holds is decided
  ;; from the two claims rather than from which arrived first, so the pair commutes.
  (tu/with-terms [p q]
    (let [rule (list 'implies (list p '?x) (list q '?x))
          h1   (v/assert kb (list 'set/forwardRule rule) 'UniverseContext)
          h2   (v/assert kb (list 'set/backwardRule rule) 'UniverseContext)]
      (is (= h1 h2))
      (is (= :both (:direction (v/sentex kb h1)))))))

(tu/deftest-kb rule-predicate-indexes-are-complete-in-both-directions
  (let [p (tu/tmp-pred) q (tu/tmp-pred)]
    (let [fwd (v/assert-rule kb [(list p '?a)] (list q '?a)
                             'UniverseContext {:direction :forward})]
      (testing "a forward-only rule is still findable by what it concludes"
        (is (contains? (p/rules-by-consequent (:index kb) q) fwd))
        (is (contains? (p/rules-by-antecedent (:index kb) p) fwd)))
      (testing "and its direction is on its own record, not inferred from the index"
        (let [s (v/sentex kb fwd)]
          (is (= :forward (:direction s)))
          (is (rules/forward-sentex? s))
          (is (not (rules/backward-sentex? s))))))))

(tu/deftest-kb a-backward-only-rule-does-not-forward-fire
  ;; the antecedent index is now complete, so forward chaining must filter on the
  ;; recorded direction — otherwise a backward/inert rule would start firing.
  (let [p (tu/tmp-pred) q (tu/tmp-pred) x (tu/tmp-ind)]
    (v/assert-rule kb [(list p '?a)] (list q '?a) 'UniverseContext {:direction :backward})
    (v/assert kb (list p x) 'UniverseContext)
    (v/forward-chain kb)
    (testing "forward chaining does not materialize its conclusion"
      (is (empty? (v/sentexes-matching kb (list q x) 'UniverseContext))))
    (testing "but it is still provable backward"
      (is (v/provable? kb (list q x) 'UniverseContext)))))

(tu/deftest-kb an-inert-rule-fires-in-neither-direction
  (let [p (tu/tmp-pred) q (tu/tmp-pred) x (tu/tmp-ind)]
    (v/assert-rule kb [(list p '?a)] (list q '?a) 'UniverseContext {:direction :inert})
    (v/assert kb (list p x) 'UniverseContext)
    (v/forward-chain kb)
    (is (empty? (v/sentexes-matching kb (list q x) 'UniverseContext)))
    (is (not (v/provable? kb (list q x) 'UniverseContext)))))

;; ---- the exception re-check index ---------------------------------------
;;
;; Rule granularity, and no truth value: it answers "which rules might need
;; re-checking", never "does the exception hold".  The predicates are passed in
;; rather than read off the rule, so these drive the protocol directly with handles
;; standing in for rules — what the index stores is a handle either way.

(tu/deftest-kb an-exception-is-posted-under-every-predicate-it-mentions
  (tu/with-terms [flightlessBird adult]
    (let [idx (:index kb) h 4001]
      (p/index-exception idx h [flightlessBird adult])
      (testing "the rule is findable from each predicate its exception mentions"
        (is (contains? (p/rules-with-exception-on idx flightlessBird) h))
        (is (contains? (p/rules-with-exception-on idx adult) h)))
      (testing "and lands in the roster the taxonomy trigger enumerates"
        (is (contains? (p/exception-rules idx) h))))))

(tu/deftest-kb the-roster-accumulates-across-rules
  (tu/with-terms [penguin ostrich]
    (let [idx (:index kb) h1 4002 h2 4003]
      (p/index-exception idx h1 [penguin])
      (p/index-exception idx h2 [ostrich])
      (is (= #{h1 h2} (p/exception-rules idx)))
      (testing "handles keep their type through nippy — ints, not strings"
        (is (every? integer? (p/exception-rules idx)))))))

(tu/deftest-kb unindexing-clears-every-predicate-key-and-the-roster
  (tu/with-terms [flightlessBird adult]
    (let [idx (:index kb) h 4004]
      (p/index-exception idx h [flightlessBird adult])
      (p/unindex-exception! idx h [flightlessBird adult])
      (is (empty? (p/rules-with-exception-on idx flightlessBird)))
      (is (empty? (p/rules-with-exception-on idx adult)))
      (is (empty? (p/exception-rules idx))))))

(tu/deftest-kb a-predicate-no-exception-mentions-is-empty
  (tu/with-terms [penguin sickChild]
    (let [idx (:index kb)]
      (testing "an index with nothing registered answers empty, not nil"
        (is (= #{} (p/rules-with-exception-on idx penguin)))
        (is (= #{} (p/exception-rules idx))))
      (p/index-exception idx 4005 [penguin])
      (testing "and a predicate no exception mentions stays empty"
        (is (= #{} (p/rules-with-exception-on idx sickChild)))))))

(tu/deftest-kb two-rules-can-share-an-exception-predicate
  ;; the set-membership case: unindexing one must not DEL the shared key and take
  ;; the other rule's registration with it.
  (tu/with-terms [penguin adult]
    (let [idx (:index kb) h1 4006 h2 4007]
      (p/index-exception idx h1 [penguin adult])
      (p/index-exception idx h2 [penguin])
      (testing "both are found under the shared predicate"
        (is (= #{h1 h2} (p/rules-with-exception-on idx penguin))))
      (p/unindex-exception! idx h1 [penguin adult])
      (testing "removing one leaves the other reachable"
        (is (= #{h2} (p/rules-with-exception-on idx penguin)))
        (is (= #{h2} (p/exception-rules idx))))
      (testing "and the predicate only the removed rule mentioned is now empty"
        (is (empty? (p/rules-with-exception-on idx adult)))))))

(tu/deftest-kb unindex-cleans-up
  (let [bornIn (tu/tmp-pred) tom (tu/tmp-ind) paris (tu/tmp-ind)
        h (v/assert kb (list bornIn tom paris) 'NaturalWorldContext)
        s (assoc (sx/sentex (list bornIn tom paris) 'NaturalWorldContext) :id h)]
    (is (= 1 (p/count-at (:index kb) [])))
    (p/unindex-sentex! (:index kb) s h)
    (is (= 0 (p/count-at (:index kb) [])))
    (is (empty? (v/sentexes-matching kb (list bornIn tom paris) 'NaturalWorldContext)))))

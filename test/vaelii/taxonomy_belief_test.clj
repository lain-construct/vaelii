(ns vaelii.taxonomy-belief-test
  "The taxonomy caches must agree with the KB about what it entails.

  The cached genl / genlContext closures are derived state — the source of truth is the
  set of *believed* sentexes asserting each edge. Four ways that agreement can
  break, each covered here: defeat leaving a stale edge, a derived edge never
  arriving, `recover` disagreeing with the running KB, and a shared edge dying with
  the first of its several asserting sentexes.

  The four flat caches — `disjoint`, disjoint metatypes + members, the predicate
  properties, and `inverse` — follow belief the same way: `refresh-beliefs`
  reconciles each `:cache-support` entry after every relabel. So a defeated
  `(disjoint A B)` stops constraining, a defeated `(functional P)` stops merging, and a
  defeated `(inverse P Q)` stops answering the swapped goal — each reviving when the
  defeater is retracted. The end-to-end half of that is at the foot of this file."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(tu/deftest-kb a-defeated-genl-leaves-the-closure
  (tu/with-terms [sub_t super_t Ind1 StoryContext]
    (v/assert kb (list 'genl sub_t super_t) StoryContext)
    (v/assert kb (list sub_t Ind1) StoryContext)
    (testing "while believed, the edge entails membership"
      (is (tax/genl? (:taxonomy kb) sub_t super_t))
      (is (v/isa? kb Ind1 super_t)))
    (v/assert kb (list 'not (list 'genl sub_t super_t)) StoryContext {:strength :monotonic})
    (testing "once defeated, the edge is gone from the closure"
      (is (empty? (v/sentexes-matching kb (list 'genl sub_t super_t) StoryContext)))
      (is (not (tax/genl? (:taxonomy kb) sub_t super_t))))
    (testing "so isa? cannot answer through it any more"
      (is (not (v/isa? kb Ind1 super_t))))))

(tu/deftest-kb a-revived-genl-comes-back
  (tu/with-terms [sub_t super_t StoryContext]
    (v/assert kb (list 'genl sub_t super_t) StoryContext)
    (let [neg (v/assert kb (list 'not (list 'genl sub_t super_t)) StoryContext
                        {:strength :monotonic})]
      (is (not (tax/genl? (:taxonomy kb) sub_t super_t)))
      (testing "retracting the defeater revives the edge, closure included"
        (v/retract! kb neg)
        (is (seq (v/sentexes-matching kb (list 'genl sub_t super_t) StoryContext)))
        (is (tax/genl? (:taxonomy kb) sub_t super_t))))))

(tu/deftest-kb a-defeat-in-one-of-two-supporting-contexts-withdraws-only-its-context
  ;; An edge asserted from two *disconnected* sibling contexts is one edge with two
  ;; supporters.  A negation asserted in one context forms a nogood with the
  ;; supporter there alone — the siblings share no descendant, so the other
  ;; supporter never pairs with it — and the edge must keep its liveness while
  ;; `edge-contexts` loses exactly the defeated side.  This is the end-to-end shape
  ;; of `refresh-relation`'s retarget arm; the raw-taxonomy version is
  ;; `a-context-only-belief-move-retargets-the-edge` in taxonomy_test.
  (tu/with-terms [sub_t super_t AContext BContext]
    (v/assert kb (list 'genl sub_t super_t) AContext)
    (v/assert kb (list 'genl sub_t super_t) BContext)
    (is (= #{AContext BContext}
           (tax/edge-contexts (:taxonomy kb) :genl [sub_t super_t])))
    (let [neg (v/assert kb (list 'not (list 'genl sub_t super_t)) BContext
                        {:strength :monotonic})]
      (testing "the edge survives on A's believed supporter, B's context leaves"
        (is (tax/genl? (:taxonomy kb) sub_t super_t))
        (is (= #{AContext}
               (tax/edge-contexts (:taxonomy kb) :genl [sub_t super_t]))))
      (testing "retracting the defeater brings B's context back"
        (v/retract! kb neg)
        (is (= #{AContext BContext}
               (tax/edge-contexts (:taxonomy kb) :genl [sub_t super_t])))))))

(tu/deftest-kb a-forward-derived-genl-reaches-the-taxonomy
  (tu/with-terms [marker foo_t bar_t Trigger1 StoryContext]
    (v/assert-rule kb [(list marker '?x)] (list 'genl foo_t bar_t) StoryContext {:chain? false})
    (v/assert kb (list marker Trigger1) StoryContext)
    (testing "the rule fired and the sentex is believed"
      (is (seq (v/sentexes-matching kb (list 'genl foo_t bar_t) StoryContext))))
    (testing "and the closure knows the edge — a derived genl is still a genl"
      (is (tax/genl? (:taxonomy kb) foo_t bar_t)))))

(tu/deftest-kb recover-agrees-with-the-running-kb
  (tu/with-terms [marker foo_t bar_t Trigger1 StoryContext]
    (v/assert-rule kb [(list marker '?x)] (list 'genl foo_t bar_t) StoryContext {:chain? false})
    (v/assert kb (list marker Trigger1) StoryContext)
    (let [before (tax/genl? (:taxonomy kb) foo_t bar_t)]
      (v/recover kb)
      (testing "a restart does not change what the KB entails"
        (is (= before (tax/genl? (:taxonomy kb) foo_t bar_t)))))))

(tu/deftest-kb recover-drops-an-edge-whose-sentex-is-gone
  (tu/with-terms [sub_t super_t StoryContext]
    (let [h (v/assert kb (list 'genl sub_t super_t) StoryContext)]
      (is (tax/genl? (:taxonomy kb) sub_t super_t))
      (v/retract! kb h)
      (testing "recover rebuilds from the store rather than merging into the cache"
        (v/recover kb)
        (is (not (tax/genl? (:taxonomy kb) sub_t super_t)))))))

(tu/deftest-kb an-edge-asserted-in-two-contexts-survives-one-retraction
  (tu/with-terms [sub_t super_t AContext BContext]
    (v/assert kb (list 'genlContext AContext 'UniverseContext) 'UniverseContext)
    (v/assert kb (list 'genlContext BContext 'UniverseContext) 'UniverseContext)
    (let [ha (v/assert kb (list 'genl sub_t super_t) AContext)]
      (v/assert kb (list 'genl sub_t super_t) BContext)
      (testing "two sentexes, one edge"
        (is (tax/genl? (:taxonomy kb) sub_t super_t)))
      (v/retract! kb ha)
      (testing "BContext still asserts it, so the edge stands"
        (is (seq (v/sentexes-matching kb (list 'genl sub_t super_t) BContext)))
        (is (tax/genl? (:taxonomy kb) sub_t super_t))))))

(tu/deftest-kb a-defeated-genlContext-stops-making-facts-visible
  (tu/with-terms [parentOf Tom Bob SubContext SuperContext]
    (v/assert kb (list 'genlContext SubContext SuperContext) 'UniverseContext)
    (v/assert kb (list parentOf Tom Bob) SuperContext)
    (testing "the inherited fact is visible from the sub-context"
      (is (seq (v/ask kb (list parentOf Tom '?y) SubContext))))
    (v/assert kb (list 'not (list 'genlContext SubContext SuperContext)) 'UniverseContext
              {:strength :monotonic})
    (testing "defeating the context edge withdraws the inheritance"
      (is (not (tax/sees? (:taxonomy kb) SubContext SuperContext)))
      (is (empty? (v/ask kb (list parentOf Tom '?y) SubContext))))))

(tu/deftest-kb a-quiet-settle-does-not-resurrect-a-defeated-edge
  ;; `refresh-beliefs` runs only when a settle actually moved belief (defeat, revival,
  ;; or an exceptWhen block change).  A later, unrelated assert moves no belief about
  ;; this edge, so the reconcile is skipped — and the skip must not let the earlier
  ;; defeat's effect leak back.  It must also not stop a *new* edge (installed on the
  ;; assert path, not by refresh-beliefs) from taking effect in the same quiet settle.
  (tu/with-terms [sub_t super_t other_t StoryContext]
    (v/assert kb (list 'genl sub_t super_t) StoryContext)
    (v/assert kb (list 'not (list 'genl sub_t super_t)) StoryContext {:strength :monotonic})
    (is (not (tax/genl? (:taxonomy kb) sub_t super_t)))            ; defeated, out of the closure
    (testing "an unrelated assert (a belief-quiet settle) keeps the defeat in place"
      (v/assert kb (list 'genl other_t 'thing) StoryContext)
      (is (not (tax/genl? (:taxonomy kb) sub_t super_t))))
    (testing "and the new edge, installed on the assert path, is active regardless"
      (is (tax/genl? (:taxonomy kb) other_t 'thing)))))

(deftest refresh-beliefs-skips-a-relation-no-moved-supporter-touches   ; perf-review #11
  ;; refresh-beliefs takes the set of handles whose belief just moved.  A genl edge
  ;; whose supporter is not among them cannot have changed active-status, so the O(edges)
  ;; scan is skipped — proven here by a `believed?` that says the edge is disbelieved:
  ;; the edge survives while its supporter is out of `moved`, and drops the moment it is
  ;; in.  A pure taxonomy so nothing else is in play.
  (let [t (tax/create-taxonomy)]
    (tax/add-genl t 'dog 'animal 1)
    (is (tax/genl? t 'dog 'animal))
    (testing "supporter 1 is not in moved → the relation is skipped, edge survives"
      (tax/refresh-beliefs t (constantly false) #{2 3})
      (is (tax/genl? t 'dog 'animal)))
    (testing "supporter 1 in moved → reconcile runs, and belief says drop it"
      (tax/refresh-beliefs t (constantly false) #{1})
      (is (not (tax/genl? t 'dog 'animal))))
    (testing "moved=nil forces the full unconditional reconcile (recover / supersession)"
      (tax/add-genl t 'dog 'animal 1)
      (is (tax/genl? t 'dog 'animal))
      (tax/refresh-beliefs t (constantly false) nil)
      (is (not (tax/genl? t 'dog 'animal))))))

;; ---- the four flat caches follow belief end-to-end ----------------------
;; Same shape as the genl tests above, exercised through the KB: assert a default
;; declaration, defeat it with a monotonic `(not …)`, and watch the thing it enabled
;; stop happening — then retract the defeater and watch it come back.

(tu/deftest-kb a-defeated-disjoint-stops-constraining
  (tu/with-terms [dog cat Felix]
    ;; one context: the disjointness check is scoped, and this KB is fresh
    (let [_hd (v/assert kb (list 'disjoint dog cat) 'NaturalWorldContext {:strength :default})]
      (v/assert kb (list cat Felix) 'NaturalWorldContext)
      (testing "believed: the pair is disjoint and the conflicting membership is refused"
        (is (v/disjoint? kb dog cat))
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/assert kb (list dog Felix) 'NaturalWorldContext))))
      (let [hn (v/assert kb (list 'not (list 'disjoint dog cat)) 'NaturalWorldContext
                         {:strength :monotonic})]
        (testing "defeated: no longer disjoint, so the membership is accepted"
          (is (not (v/disjoint? kb dog cat)))
          (is (v/assert kb (list dog Felix) 'NaturalWorldContext)))
        (testing "retracting the defeater restores the constraint"
          ;; drop the now-admitted membership so the revived disjoint has no live clash
          (when-let [hf (:id (first (v/sentexes-matching kb (list dog Felix) 'NaturalWorldContext)))]
            (v/retract! kb hf))
          (v/retract! kb hn)
          (is (v/disjoint? kb dog cat)))))))

(tu/deftest-kb a-defeated-functional-stops-rejecting
  (tu/with-terms [ageOf Bob]
    (let [_hf (v/assert kb (list 'functional ageOf) 'UniverseContext {:strength :default})]
      (v/assert kb (list ageOf Bob 40) 'UniverseContext)
      (testing "believed: a second, unmergeable numeric value is refused"
        (is (v/has-prop? kb :functional ageOf))
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/assert kb (list ageOf Bob 41) 'UniverseContext))))
      (let [hn (v/assert kb (list 'not (list 'functional ageOf)) 'UniverseContext
                         {:strength :monotonic})]
        (testing "defeated: the declaration no longer constrains"
          (is (not (v/has-prop? kb :functional ageOf)))
          (is (v/assert kb (list ageOf Bob 41) 'UniverseContext)))
        (testing "retracting the defeater re-arms the constraint"
          (when-let [h41 (:id (first (v/sentexes-matching kb (list ageOf Bob 41) 'UniverseContext)))]
            (v/retract! kb h41))
          (v/retract! kb hn)
          (is (v/has-prop? kb :functional ageOf))
          (is (thrown? clojure.lang.ExceptionInfo
                       (v/assert kb (list ageOf Bob 41) 'UniverseContext))))))))

(tu/deftest-kb a-defeated-inverse-stops-answering-the-swapped-goal
  (tu/with-terms [parentOf childOf Tom Bob]
    (let [_hi (v/assert kb (list 'inverse parentOf childOf) 'UniverseContext {:strength :default})]
      (v/assert kb (list parentOf Tom Bob) 'UniverseContext)
      (testing "believed: the inverse goal is answerable"
        (is (= childOf (v/inverse-of kb parentOf)))
        (is (v/ask? kb (list childOf Bob Tom) 'UniverseContext)))
      (let [hn (v/assert kb (list 'not (list 'inverse parentOf childOf)) 'UniverseContext
                         {:strength :monotonic})]
        (testing "defeated: the inverse map is empty and the swapped goal fails"
          (is (nil? (v/inverse-of kb parentOf)))
          (is (nil? (v/inverse-of kb childOf)))
          (is (not (v/ask? kb (list childOf Bob Tom) 'UniverseContext))))
        (testing "retracting the defeater revives the inverse"
          (v/retract! kb hn)
          (is (= childOf (v/inverse-of kb parentOf)))
          (is (v/ask? kb (list childOf Bob Tom) 'UniverseContext)))))))

(tu/deftest-kb a-defeated-transitive-stops-composing
  (tu/with-terms [before A B C]
    (let [_ht (v/assert kb (list 'transitive before) 'UniverseContext {:strength :default})]
      (v/assert kb (list before A B) 'UniverseContext)
      (v/assert kb (list before B C) 'UniverseContext)
      (testing "believed: the transitive step composes A→B→C into A→C"
        (is (v/has-prop? kb :transitive before))
        (is (v/ask? kb (list before A C) 'UniverseContext)))
      (let [hn (v/assert kb (list 'not (list 'transitive before)) 'UniverseContext
                         {:strength :monotonic})]
        (testing "defeated: no composition, only the stored steps hold"
          (is (not (v/has-prop? kb :transitive before)))
          (is (not (v/ask? kb (list before A C) 'UniverseContext))))
        (testing "retracting the defeater restores composition"
          (v/retract! kb hn)
          (is (v/has-prop? kb :transitive before))
          (is (v/ask? kb (list before A C) 'UniverseContext)))))))

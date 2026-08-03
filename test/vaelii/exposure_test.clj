;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.exposure-test
  "The cross-context exposure pass: two memberships each admissible where stated,
  whose types some context can jointly see as disjoint, are a real contradiction —
  reported as a `:disjoint` entry in the violations ledger by `settle`, never by
  refusing a writer on grounds it cannot see.

  Three routes expose one clash — the membership arriving last, the separating
  declaration arriving last, the `genlContext` edge arriving last — and the pass
  runs at settle exactly so the answer is route-agnostic.  Each route gets a test;
  the shared lattice is two siblings under UniverseContext, with the joint viewer
  (when one exists) below both.  The membership-last route's acceptance test is
  `disjoint_test/a-general-context-may-be-given-what-a-specific-one-forbids`."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.settle :as settle]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- siblings!
  "Two sibling contexts under UniverseContext, two root types, one term holding one
  type in each sibling — admissible everywhere, since neither sibling sees the
  other."
  [kb {:keys [a b t1 t2 x]}]
  (v/assert kb (list 'genl t1 'thing) 'UniverseContext)
  (v/assert kb (list 'genl t2 'thing) 'UniverseContext)
  (v/assert kb (list 'genlContext a 'UniverseContext) 'UniverseContext)
  (v/assert kb (list 'genlContext b 'UniverseContext) 'UniverseContext)
  (v/assert kb (list t1 x) a)
  (v/assert kb (list t2 x) b))

(tu/deftest-kb siblings-with-no-joint-viewer-expose-nothing
  ;; the pin for the ∃-descendant reading: the memberships coexist, the declaration
  ;; is visible to both writers, and still no single context sees the whole clash —
  ;; so there is nothing to report and nobody to report it to.
  (tu/with-terms [AContext BContext left_t right_t Pip]
    (v/assert kb (list 'disjoint left_t right_t) 'UniverseContext)
    (siblings! kb {:a AContext :b BContext :t1 left_t :t2 right_t :x Pip})
    (is (empty? (v/violations kb)))
    (is (seq (v/sentexes-matching kb (list left_t Pip) AContext)))
    (is (seq (v/sentexes-matching kb (list right_t Pip) BContext)))))

(tu/deftest-kb a-genlContext-edge-arriving-last-exposes-the-clash
  ;; the visibility route: everything else stands, and wiring a joint viewer below
  ;; both siblings is what makes the clash visible — the edge's own settle files it.
  (tu/with-terms [AContext BContext WContext left_t right_t Pip]
    (v/assert kb (list 'disjoint left_t right_t) 'UniverseContext)
    (siblings! kb {:a AContext :b BContext :t1 left_t :t2 right_t :x Pip})
    (v/assert kb (list 'genlContext WContext AContext) 'UniverseContext)
    (is (empty? (v/violations kb)) "seeing one side is not seeing the clash")
    (v/assert kb (list 'genlContext WContext BContext) 'UniverseContext)
    (let [vs (v/violations kb)]
      (is (= [:disjoint] (mapv :violation vs)))
      (is (= #{WContext} (get-in (first vs) [:detail :visible-from])))
      (is (= Pip (get-in (first vs) [:detail :term]))))))

(tu/deftest-kb a-rebuild-exposes-nothing-because-nothing-newly-moved
  ;; The pass reports what a *change* newly made jointly visible.  A `recover` changes
  ;; nothing — it restores — and its region is every stored sentex, so leaving the pass
  ;; on turns a bounded incremental check into a full-KB audit nobody asked for: 27% of
  ;; an OpenCyc import.  The clash is still there and still findable; what the skip
  ;; costs nobody is re-filing it on every restart.
  (tu/with-terms [AContext BContext WContext left_t right_t Pip]
    (v/assert kb (list 'disjoint left_t right_t) 'UniverseContext)
    (siblings! kb {:a AContext :b BContext :t1 left_t :t2 right_t :x Pip})
    (v/assert kb (list 'genlContext WContext AContext) 'UniverseContext)
    (v/assert kb (list 'genlContext WContext BContext) 'UniverseContext)
    (is (= [:disjoint] (mapv :violation (v/violations kb)))
        "the change that exposed it reported it")
    (v/clear-violations! kb)
    (v/recover kb)
    (is (empty? (v/violations kb)) "and the rebuild does not report it again")
    (testing "while the KB still holds both sides, and an ordinary settle still reports"
      (is (seq (v/sentexes-matching kb (list left_t Pip) AContext)))
      (is (seq (v/sentexes-matching kb (list right_t Pip) BContext)))
      ;; a real change to the same lattice exposes again, so the gate is about
      ;; rebuilding and not about the clash having been seen once
      (tu/with-terms [VContext]
        (v/assert kb (list 'genlContext VContext AContext) 'UniverseContext)
        (v/assert kb (list 'genlContext VContext BContext) 'UniverseContext)
        (let [vs (v/violations kb)]
          (is (every? #(= :disjoint (:violation %)) vs))
          ;; the new viewer is named among those the clash is visible from — the pass
          ;; is off for a rebuild, not off.  (W's sighting is re-filed alongside it:
          ;; an exposure is an event, and the cone moved again.)
          (is (some #(contains? (get-in % [:detail :visible-from]) VContext) vs)))))))

(tu/deftest-kb the-standing-question-is-answerable-on-demand
  ;; `settle` reports what a change newly exposed; this reports what the KB holds now.
  ;; It is the same clash and the same entry shape, asked of the whole KB by a caller
  ;; who chose to — and it is what an imported KB has instead of a settle that ran
  ;; while the content was arriving.
  (tu/with-terms [AContext BContext WContext left_t right_t Pip]
    (v/assert kb (list 'disjoint left_t right_t) 'UniverseContext)
    (siblings! kb {:a AContext :b BContext :t1 left_t :t2 right_t :x Pip})
    (testing "before a joint viewer exists there is nothing to see, from either angle"
      (is (empty? (v/violations kb)))
      (is (empty? (v/exposed-clashes kb))))
    (v/assert kb (list 'genlContext WContext AContext) 'UniverseContext)
    (v/assert kb (list 'genlContext WContext BContext) 'UniverseContext)
    (let [filed (v/violations kb)
          asked (v/exposed-clashes kb)]
      (is (= [:disjoint] (mapv :violation asked)))
      (is (= (map :detail filed) (map :detail asked))
          "the same clash, the same entry — one filed as it arose, one asked for")
      (testing "and asking does not file, store, or move belief"
        (v/clear-violations! kb)
        (let [before (tu/content-count kb)]
          (is (seq (v/exposed-clashes kb)))
          (is (empty? (v/violations kb)))
          (is (= before (tu/content-count kb))))))
    (testing "it survives the rebuild that the settle pass deliberately sits out"
      (v/recover kb)
      (is (empty? (v/violations kb)) "the rebuild filed nothing")
      (is (= [:disjoint] (mapv :violation (v/exposed-clashes kb)))
          "and the clash is still there to be asked about"))
    (testing "and it goes when the clash does"
      (v/retract! kb (v/handle-of kb (list 'disjoint left_t right_t) 'UniverseContext))
      (is (empty? (v/exposed-clashes kb))))))

(tu/deftest-kb a-declaration-arriving-last-exposes-the-clash
  ;; the separation route: the memberships are jointly visible all along, and the
  ;; disjointness arriving is what makes them a clash.
  (tu/with-terms [AContext CContext t1 t2 Pip]
    (v/assert kb (list 'genl t1 'thing) 'UniverseContext)
    (v/assert kb (list 'genl t2 'thing) 'UniverseContext)
    (v/assert kb (list 'genlContext CContext 'UniverseContext) 'UniverseContext)
    (v/assert kb (list 'genlContext AContext CContext) 'UniverseContext)
    (v/assert kb (list t1 Pip) CContext)
    (v/assert kb (list t2 Pip) AContext)
    (is (empty? (v/violations kb)) "compatible until somebody separates them")
    (v/assert kb (list 'disjoint t1 t2) CContext)
    (let [vs (v/violations kb)]
      (is (= [:disjoint] (mapv :violation vs)))
      (is (= #{AContext} (get-in (first vs) [:detail :visible-from]))))))

(tu/deftest-kb a-genl-edge-arriving-last-exposes-the-clash
  ;; the closure route: the held types are not themselves separated — a subtype
  ;; edge arriving puts one of them under a separated type, and the instances below
  ;; its sub side are re-examined.
  (tu/with-terms [AContext CContext dog_t canine_t cat_t Rex]
    (v/assert kb (list 'genl canine_t 'thing) 'UniverseContext)
    (v/assert kb (list 'genl cat_t 'thing) 'UniverseContext)
    (v/assert kb (list 'genl dog_t 'thing) 'UniverseContext)
    (v/assert kb (list 'disjoint canine_t cat_t) 'UniverseContext)
    (v/assert kb (list 'genlContext CContext 'UniverseContext) 'UniverseContext)
    (v/assert kb (list 'genlContext AContext CContext) 'UniverseContext)
    (v/assert kb (list dog_t Rex) CContext)
    (v/assert kb (list cat_t Rex) AContext)
    (is (empty? (v/violations kb)) "a dog-cat is odd but nothing separates them yet")
    (v/assert kb (list 'genl dog_t canine_t) CContext)
    (let [vs (v/violations kb)]
      (is (= [:disjoint] (mapv :violation vs)))
      (is (= #{AContext} (get-in (first vs) [:detail :visible-from])))
      (is (= Rex (get-in (first vs) [:detail :term]))))))

(tu/deftest-kb exposure-is-an-event-append-only-and-refiled-on-revival
  ;; the ledger contract: retracting the ingredient that exposed a clash does not
  ;; withdraw the entry, and the ingredient returning files a new one.
  (tu/with-terms [AContext CContext t1 t2 Pip]
    (v/assert kb (list 'genl t1 'thing) 'UniverseContext)
    (v/assert kb (list 'genl t2 'thing) 'UniverseContext)
    (v/assert kb (list 'genlContext CContext 'UniverseContext) 'UniverseContext)
    (v/assert kb (list 'genlContext AContext CContext) 'UniverseContext)
    (v/assert kb (list 'disjoint t1 t2) 'UniverseContext)
    (v/assert kb (list t1 Pip) AContext)
    (let [h (v/assert kb (list t2 Pip) CContext)]
      (is (= 1 (count (v/violations kb))))
      (v/retract! kb h)
      (is (= 1 (count (v/violations kb))) "the entry outlives its ingredient")
      (v/assert kb (list t2 Pip) CContext)
      (is (= 2 (count (v/violations kb))) "each exposure is its own event")
      (testing "and the runs differ, so \"current\" stays decidable"
        (is (apply distinct? (map :run (v/violations kb))))))))

(tu/deftest-kb an-unrelated-settle-does-not-refile-a-standing-clash
  ;; locality: the pass reads the settle's moved region, so a clash whose
  ;; ingredients did not move is not re-examined, let alone re-filed.
  (tu/with-terms [AContext CContext t1 t2 other Pip Quo]
    (v/assert kb (list 'genl t1 'thing) 'UniverseContext)
    (v/assert kb (list 'genl t2 'thing) 'UniverseContext)
    (v/assert kb (list 'genlContext CContext 'UniverseContext) 'UniverseContext)
    (v/assert kb (list 'genlContext AContext CContext) 'UniverseContext)
    (v/assert kb (list 'disjoint t1 t2) 'UniverseContext)
    (v/assert kb (list t1 Pip) AContext)
    (v/assert kb (list t2 Pip) CContext)
    (is (= 1 (count (v/violations kb))))
    (v/assert kb (list other Quo) CContext)
    (v/assert kb (list other Pip) CContext)
    (is (= 1 (count (v/violations kb)))
        "an unrelated membership — even of the clash's own term — files nothing new:
         the pair it forms with the standing types is not disjoint")))

(tu/deftest-kb a-budgeted-sweep-truncates-out-loud
  ;; the extent-sweeping routes (declaration / metatype / edge arriving last) are
  ;; bounded per settle by *exposure-instance-budget*; a sweep cut short files
  ;; :exposure-truncated naming its trigger rather than silently reading as full
  ;; coverage.  The membership route is exact and unbudgeted.
  (binding [settle/*exposure-instance-budget* 1]
    (tu/with-terms [AContext CContext t1 t2 Pip Quo Rex]
      (v/assert kb (list 'genl t1 'thing) 'UniverseContext)
      (v/assert kb (list 'genl t2 'thing) 'UniverseContext)
      (v/assert kb (list 'genlContext CContext 'UniverseContext) 'UniverseContext)
      (v/assert kb (list 'genlContext AContext CContext) 'UniverseContext)
      (v/assert kb (list t1 Pip) CContext)
      (v/assert kb (list t2 Pip) AContext)
      (v/assert kb (list t1 Quo) CContext)
      (v/assert kb (list t2 Quo) AContext)
      (v/assert kb (list t1 Rex) CContext)
      ;; the declaration arrives last: five memberships below its types, budget one
      (v/assert kb (list 'disjoint t1 t2) CContext)
      (let [vs (v/violations kb)
            cut (filter #(= :exposure-truncated (:violation %)) vs)]
        (is (seq cut) "the cut is reported, not silent")
        (is (= 1 (count cut))
            "one entry for the pass — the budget is the pass's, so a per-trigger entry
             would say the same thing once per trigger that arithmetic ran out on")
        (is (= [(list 'disjoint t1 t2)] (get-in (first cut) [:detail :sample]))
            "and names what it did not sweep")
        (is (= 1 (get-in (first cut) [:detail :triggers]))
            "and how many went unswept")
        (is (<= (count (filter #(= :disjoint (:violation %)) vs)) 1)
            "at most the budgeted share of instances was examined")))))

(tu/deftest-kb many-cut-sweeps-file-one-entry-between-them
  ;; The corpus-load shape: a settle whose region holds many extent-sweeping triggers.
  ;; The first spends the budget and every one after it is cut short by arithmetic —
  ;; so the ledger gets one entry with a count, not one per trigger.  Left unfixed this
  ;; was 41,500 entries on an OpenCyc load, against a ledger that keeps 1,000.
  (binding [settle/*exposure-instance-budget* 1]
    (tu/with-terms [CContext t1 t2 Pip Quo]
      (v/assert kb (list 'genl t1 'thing) 'UniverseContext)
      (v/assert kb (list 'genl t2 'thing) 'UniverseContext)
      (v/assert kb (list 'genlContext CContext 'UniverseContext) 'UniverseContext)
      (v/assert kb (list t1 Pip) CContext)
      (v/assert kb (list t2 Quo) CContext)
      (v/assert kb (list 'disjoint t1 t2) CContext)
      (v/clear-violations! kb)
      ;; one settle, several sweeping triggers: two genl edges and a metatype
      (tu/with-terms [t3 t4]
        (v/with-deferred-settle kb
          (v/assert kb (list 'genl t3 t1) 'UniverseContext)
          (v/assert kb (list 'genl t4 t2) 'UniverseContext)
          (v/assert kb (list t3 Pip) CContext)
          (v/assert kb (list t4 Quo) CContext)))
      (let [cut (filter #(= :exposure-truncated (:violation %)) (v/violations kb))]
        (is (>= (count cut) 1) "the bound is still reported")
        (is (= 1 (count cut)) "once per settle, however many triggers it cut short")
        (is (<= (count (get-in (first cut) [:detail :sample])) 3)
            "with a sample rather than the whole list")))))

;;; ── what a declaration implicates ─────────────────────────────────────
;;
;; The budget above bounds the sweep; what the sweep spends it *on* is the candidate
;; rule, and the two together decide whether a bounded pass buys real coverage or
;; merely a bounded quantity of terms that were never going to convict.

(tu/deftest-kb a-separation-implicates-the-terms-below-both-sides-not-below-either
  ;; The extent below one side is not the candidate set: a clash needs a membership
  ;; from *each*, so `(disjoint t1 t2)` implicates the terms below t1 **and** t2.
  ;; Forty terms sit below t1 alone and one below both, against a budget of four —
  ;; so a sweep of everything below either side spends the budget ten times over on
  ;; the fillers and never reaches the clash, while the cheaper side is one term.
  (binding [settle/*exposure-instance-budget* 4]
    (tu/with-terms [AContext CContext t1 t2 Pip]
      (v/assert kb (list 'genl t1 'thing) 'UniverseContext)
      (v/assert kb (list 'genl t2 'thing) 'UniverseContext)
      (v/assert kb (list 'genlContext CContext 'UniverseContext) 'UniverseContext)
      (v/assert kb (list 'genlContext AContext CContext) 'UniverseContext)
      (dotimes [_ 40]
        (v/assert kb (list t1 (tu/tmp-ind "Filler")) CContext))
      (v/assert kb (list t1 Pip) CContext)
      (v/assert kb (list t2 Pip) AContext)
      (v/clear-violations! kb)
      (v/assert kb (list 'disjoint t1 t2) CContext)
      (let [vs (v/violations kb)]
        (is (= [Pip] (mapv #(get-in % [:detail :term])
                           (filter #(= :disjoint (:violation %)) vs)))
            "the one term holding both is found, though t1's extent is ten times the budget")
        (is (empty? (filter #(= :exposure-truncated (:violation %)) vs))
            "and nothing was cut short — the cheaper side is one term, not forty")))))

(tu/deftest-kb a-sweep-that-convicts-nobody-still-stops-at-the-bound
  ;; The budget bounds the **enumeration**, never the survivors.  Nothing here holds
  ;; both types, so the candidate rule rejects every term it is shown; budgeting what
  ;; survives instead would walk both extents to the end looking for a keeper and then
  ;; report full coverage, which is the one thing a bounded pass may not do.
  (binding [settle/*exposure-instance-budget* 2]
    (tu/with-terms [AContext CContext t1 t2]
      (v/assert kb (list 'genl t1 'thing) 'UniverseContext)
      (v/assert kb (list 'genl t2 'thing) 'UniverseContext)
      (v/assert kb (list 'genlContext CContext 'UniverseContext) 'UniverseContext)
      (v/assert kb (list 'genlContext AContext CContext) 'UniverseContext)
      (dotimes [_ 20] (v/assert kb (list t1 (tu/tmp-ind "Left")) CContext))
      (dotimes [_ 20] (v/assert kb (list t2 (tu/tmp-ind "Right")) AContext))
      (v/clear-violations! kb)
      (v/assert kb (list 'disjoint t1 t2) CContext)
      (let [vs (v/violations kb)]
        (is (empty? (filter #(= :disjoint (:violation %)) vs))
            "nobody holds both, so there is no clash to expose")
        (is (seq (filter #(= :exposure-truncated (:violation %)) vs))
            "and the pass says it stopped early rather than claiming it looked at all 20")))))

(tu/deftest-kb a-metatype-declaration-arriving-last-exposes-the-clash
  ;; `(disjointMetatype M)` is a *unary* sentence whose argument is a symbol — the
  ;; same shape as a type membership — so the membership arm claims it unless the
  ;; declarations are matched first, and the metatype gets filed as a term holding a
  ;; type while the clash its arrival creates goes unswept.
  (tu/with-terms [AContext CContext animalSpecies dog_t cat_t Rex]
    (v/assert kb (list 'genl dog_t 'thing) 'UniverseContext)
    (v/assert kb (list 'genl cat_t 'thing) 'UniverseContext)
    (v/assert kb (list 'genlContext CContext 'UniverseContext) 'UniverseContext)
    (v/assert kb (list 'genlContext AContext CContext) 'UniverseContext)
    (v/assert kb (list animalSpecies dog_t) 'UniverseContext)
    (v/assert kb (list animalSpecies cat_t) 'UniverseContext)
    (v/assert kb (list dog_t Rex) CContext)
    (v/assert kb (list cat_t Rex) AContext)
    (is (empty? (v/violations kb)) "the metatype separates nothing yet")
    (v/assert kb (list 'disjointMetatype animalSpecies) 'UniverseContext)
    (let [vs (filter #(= :disjoint (:violation %)) (v/violations kb))]
      (is (= [Rex] (mapv #(get-in % [:detail :term]) vs))
          "the members become pairwise disjoint, and the term holding two of them is a clash")
      (is (= #{AContext} (get-in (first vs) [:detail :visible-from]))))))

(tu/deftest-kb the-narrowed-sweep-finds-what-the-complete-question-finds
  ;; The candidate rule is a *narrowing*, so the claim that matters is that it narrows
  ;; to nothing real.  `exposed-clashes` uses no candidate rule and no budget — a term
  ;; is a candidate iff it holds two believed memberships — so it is the independent
  ;; oracle, and the two must agree clash for clash.
  ;;
  ;; The shape is the one that separates the rules: three separated pairs over terms
  ;; that mostly hold one side only, so a sweep below either side collects fillers while
  ;; the intersection collects the two that convict.  On OpenCyc the same comparison
  ;; over every declaration is 638 against 638, with both differences empty.
  (tu/with-terms [AContext CContext a1_t a2_t b1_t b2_t Pip Quo]
    (doseq [t [a1_t a2_t b1_t b2_t]]
      (v/assert kb (list 'genl t 'thing) 'UniverseContext))
    (v/assert kb (list 'genlContext CContext 'UniverseContext) 'UniverseContext)
    (v/assert kb (list 'genlContext AContext CContext) 'UniverseContext)
    (dotimes [_ 12] (v/assert kb (list a1_t (tu/tmp-ind "Filler")) CContext))
    (dotimes [_ 12] (v/assert kb (list b2_t (tu/tmp-ind "Filler")) CContext))
    (v/assert kb (list a1_t Pip) CContext)
    (v/assert kb (list b1_t Pip) AContext)
    (v/assert kb (list a2_t Quo) CContext)
    (v/assert kb (list b2_t Quo) AContext)
    (v/clear-violations! kb)
    (v/assert kb (list 'disjoint a1_t b1_t) 'UniverseContext)
    (v/assert kb (list 'disjoint a2_t b2_t) 'UniverseContext)
    (v/assert kb (list 'disjoint a1_t b2_t) 'UniverseContext)
    (let [filed (into #{} (comp (filter #(= :disjoint (:violation %))) (map :detail))
                      (v/violations kb))
          truth (into #{} (map :detail) (v/exposed-clashes kb))]
      (is (= #{Pip Quo} (into #{} (map :term) truth))
          "two terms hold a separated pair; the 24 fillers hold one side only")
      (is (= truth filed)
          "and the sweep that narrowed to them reports exactly what the complete question does"))))

(tu/deftest-kb a-separation-naming-a-non-symbol-implicates-nobody
  ;; A NART argument — OpenCyc declares thousands of separations against terms like
  ;; `(AbnormalFn chromosome)` — has an empty spec closure, so no membership sits below
  ;; it and no clash sits above it.  The reach is empty outright rather than falling out
  ;; of the sizing arithmetic, and in particular the *symbol* side's extent is not swept
  ;; on the strength of a side that can convict nobody.
  (binding [settle/*exposure-instance-budget* 3]
    (tu/with-terms [CContext real_t Pip]
      (v/assert kb (list 'genl real_t 'thing) 'UniverseContext)
      (v/assert kb (list 'genlContext CContext 'UniverseContext) 'UniverseContext)
      (dotimes [_ 20] (v/assert kb (list real_t (tu/tmp-ind "Filler")) CContext))
      (v/assert kb (list real_t Pip) CContext)
      (v/clear-violations! kb)
      (v/assert kb (list 'disjoint (list 'SomeFn real_t) real_t) 'UniverseContext)
      (let [vs (v/violations kb)]
        (is (empty? (filter #(= :disjoint (:violation %)) vs))
            "a compound can head no stored membership, so it is nobody's clash")
        (is (empty? (filter #(= :exposure-truncated (:violation %)) vs))
            "and the 20 instances below the symbol side are not swept for its sake")))))

(tu/deftest-kb the-nogood-path-narrows-the-same-way-the-exposure-pass-does
  ;; `declaration-implicates` and `declaration-reach` answer one question about one KB.
  ;; If they disagreed, a pair one reached and the other did not would be reported as
  ;; merely *visible* by the ledger or as *decided* by `contradictions` depending on
  ;; which route ran — so the arbitrating path gets the same narrowing, and the same
  ;; budget spent on enumeration rather than on terms that convict nobody.
  (binding [checks/*arbitrate-constraints?* true
            settle/*exposure-instance-budget* 4]
    (tu/with-kb [kb (tu/fresh)]
      (tu/with-terms [dog_t cat_t Rex]
        (v/assert kb (list 'genl dog_t 'thing) 'UniverseContext)
        (v/assert kb (list 'genl cat_t 'thing) 'UniverseContext)
        (dotimes [_ 40] (v/assert kb (list dog_t (tu/tmp-ind "Pup")) 'UniverseContext))
        (v/assert kb (list dog_t Rex) 'UniverseContext)
        (v/assert kb (list cat_t Rex) 'UniverseContext)
        (is (empty? (v/contradictions kb)) "nothing separates them yet")
        (v/assert kb (list 'disjoint dog_t cat_t) 'UniverseContext)
        (is (= [:disjoint] (mapv :kind (v/contradictions kb)))
            "the one term holding both is arbitrated, though dog_t's extent is ten times
             the budget — the cheaper side is cat_t's single instance")))))

(tu/deftest-kb a-metatype-member-implicates-only-the-holders-of-another-member
  ;; The member route, `(M T)` arriving: T's instances can now clash with instances of
  ;; M's *other* members, so a term below T holding nothing else of M is not a
  ;; candidate.  Twenty such terms sit below dog_t against a budget of three.
  (binding [settle/*exposure-instance-budget* 3]
    (tu/with-terms [AContext CContext animalSpecies dog_t cat_t Rex]
      (v/assert kb (list 'genl dog_t 'thing) 'UniverseContext)
      (v/assert kb (list 'genl cat_t 'thing) 'UniverseContext)
      (v/assert kb (list 'genlContext CContext 'UniverseContext) 'UniverseContext)
      (v/assert kb (list 'genlContext AContext CContext) 'UniverseContext)
      (v/assert kb (list 'disjointMetatype animalSpecies) 'UniverseContext)
      (v/assert kb (list animalSpecies cat_t) 'UniverseContext)
      (dotimes [_ 20] (v/assert kb (list dog_t (tu/tmp-ind "Pup")) CContext))
      (v/assert kb (list dog_t Rex) CContext)
      (v/assert kb (list cat_t Rex) AContext)
      (v/clear-violations! kb)
      (v/assert kb (list animalSpecies dog_t) 'UniverseContext)
      (let [vs (v/violations kb)]
        (is (= [Rex] (mapv #(get-in % [:detail :term])
                           (filter #(= :disjoint (:violation %)) vs)))
            "only the term that also holds a second member is a candidate")
        (is (empty? (filter #(= :exposure-truncated (:violation %)) vs))
            "and the cheaper side is walked — cat_t's one instance, not dog_t's 21")))))

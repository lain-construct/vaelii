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
            [vaelii.impl.rules :as vr]
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
  ;; A reified NAT argument — OpenCyc declares thousands of separations against terms like
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
    (tu/with-kb [kb]
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

(tu/deftest-kb a-budgeted-sweep-decides-the-same-pair-in-either-arrival-order
  ;; **Two** separations in one moved region, because one cannot show this: each `v/assert`
  ;; settles, so a single declaration makes the region one element and `content-order` over
  ;; it is a no-op.  Deferred into one settle with a budget covering one reach and not the
  ;; other, the trigger order decides which pair is arbitrated at all — and reversing the
  ;; write order must not move it.
  ;;
  ;; The budget is exactly one reach, so the second trigger arrives with nothing left: this
  ;; is also what covers the spent-budget branch, which files on the probe rather than on
  ;; the arithmetic.  Asserted on *which* separation was decided rather than on the `:kind`,
  ;; since every disjointness clash has the same kind and a different pair would read
  ;; identically.
  ;;
  ;; **Each arm invents its own terms**, and that is what makes the two comparable.  The
  ;; arms share one KB — `with-kb` binds the fixture's, and a `fresh` mid-test would clear
  ;; the store the net-neutrality check recorded its baseline against — so an arm reusing
  ;; the other's vocabulary would sweep a reach the first arm had already doubled, and read
  ;; as an arrival-order effect when it was a leftover.  Its own terms make the second
  ;; arm's reach the same size as the first's, whatever is still standing beside it.
  (binding [checks/*arbitrate-constraints?* true
            settle/*exposure-instance-budget* 11]
    (let [run (fn [backwards?]
                (tu/with-kb [k]
                  (tu/with-terms [aa_t bb_t cc_t dd_t Pip Quo]
                    (doseq [t [aa_t bb_t cc_t dd_t]]
                      (v/assert k (list 'genl t 'thing) 'UniverseContext))
                    (doseq [t [aa_t bb_t cc_t dd_t]]
                      (dotimes [_ 10] (v/assert k (list t (tu/tmp-ind "Pad")) 'UniverseContext)))
                    (v/assert k (list aa_t Pip) 'UniverseContext)
                    (v/assert k (list bb_t Pip) 'UniverseContext)
                    (v/assert k (list cc_t Quo) 'UniverseContext)
                    (v/assert k (list dd_t Quo) 'UniverseContext)
                    (v/clear-violations! k)
                    (v/with-deferred-settle k
                      (doseq [d (cond-> [(list 'disjoint aa_t bb_t) (list 'disjoint cc_t dd_t)]
                                  backwards? reverse)]
                        (v/assert k d 'UniverseContext)))
                    ;; normalized to *which* separation, since the two arms name different
                    ;; terms and the sentences are therefore never `=`
                    {:decided (into #{}
                                    (keep (fn [s]
                                            (let [ts (set (flatten s))]
                                              (cond (contains? ts aa_t) :head
                                                    (contains? ts cc_t) :tail))))
                                    (map :sentence (v/contradictions k)))
                     :cut     (->> (v/violations k)
                                   (filter #(= :arbitration-truncated (:violation %)))
                                   (mapv #(get-in % [:detail :triggers])))})))
          fwd (run false)
          rev (run true)]
      (testing "the content-first trigger gets the budget, whichever was written first"
        (is (contains? (:decided fwd) :head))
        (is (contains? (:decided rev) :head)
            "written second, and still the one the budget was spent on"))
      (testing "and the trigger it could not reach is reported rather than passed over"
        (is (seq (:cut fwd)))
        (is (seq (:cut rev))))
      ;; And the **tail** agrees too, which is the half a weaker reading misses.  The
      ;; budget is one reach, so exactly one of the two separations can be swept and the
      ;; other is cut — and *which* must be decided by `content-order` over the region
      ;; rather than by which was written first.  A reading that only checked the head
      ;; pair would pass while the tail moved with arrival order, which is the shape this
      ;; whole file is about (docs/nmtms.md).
      (is (= (:decided fwd) (:decided rev))
          "the same pairs decided, not merely the same head pair")
      (is (= (:cut fwd) (:cut rev))
          "and the same triggers reported unswept"))))

(tu/deftest-kb an-enumeration-that-exactly-fills-the-budget-is-not-a-cut
  ;; The whole reason the probe takes one past the budget.  A reach of exactly N terms was
  ;; swept in full, and filing it would inflate the number a reader acts on — which is the
  ;; failure `exposure-candidates` measured at 183,397 against a true 41,500.
  (binding [checks/*arbitrate-constraints?* true]
    (tu/with-terms [t1 t2 Pip]
      ;; built per run and nowhere else: `tu/fresh` clears the scratch space these share,
      ;; so a second copy in the enclosing KB is a second copy in *this* one
      (let [cut-at (fn [budget]
                     (tu/with-kb [k]
                       (doseq [t [t1 t2]] (v/assert k (list 'genl t 'thing) 'UniverseContext))
                       ;; t1's extent is exactly five and is the cheaper side, so it is
                       ;; what `two-sided-reach` enumerates
                       (dotimes [_ 4] (v/assert k (list t1 (tu/tmp-ind "Pad")) 'UniverseContext))
                       (v/assert k (list t1 Pip) 'UniverseContext)
                       (dotimes [_ 9] (v/assert k (list t2 (tu/tmp-ind "Other")) 'UniverseContext))
                       (v/assert k (list t2 Pip) 'UniverseContext)
                       (v/clear-violations! k)
                       (binding [settle/*exposure-instance-budget* budget]
                         (v/assert k (list 'disjoint t1 t2) 'UniverseContext))
                       {:cut     (seq (filter #(= :arbitration-truncated (:violation %))
                                              (v/violations k)))
                        :decided (seq (v/contradictions k))}))]
        (testing "exactly the extent: swept in full, so nothing is filed"
          (let [{:keys [cut decided]} (cut-at 5)]
            (is (nil? cut) "a reach of exactly the budget is not a cut")
            (is (seq decided) "and the pair inside it is decided")))
        (testing "one short: the same reach is a cut, which is what makes the line a line"
          (is (seq (:cut (cut-at 4)))))))))

;;; ── the deciding pass says when it was cut short too ──────────────────
;;
;; `expose-clashes!` files `:exposure-truncated` when the budget stops it, so bounded
;; work never reads as full coverage.  The arbitration sweep spends the same budget
;; before anything is *decided* rather than before anything is reported, which is the
;; half a reader most needs, so it files its own — and its own kind, because a reader
;; acts differently on "went unreported" than on "went undecided", and because
;; `functional` / `asymmetric` reach back here and nowhere else.

(tu/deftest-kb an-arbitration-sweep-cut-short-says-so
  (binding [checks/*arbitrate-constraints?* true
            settle/*exposure-instance-budget* 2]
    (tu/with-terms [t1 t2 Pip]
      (v/assert kb (list 'genl t1 'thing) 'UniverseContext)
      (v/assert kb (list 'genl t2 'thing) 'UniverseContext)
      (dotimes [_ 20] (v/assert kb (list t1 (tu/tmp-ind "Filler")) 'UniverseContext))
      (dotimes [_ 20] (v/assert kb (list t2 (tu/tmp-ind "Other")) 'UniverseContext))
      (v/assert kb (list t1 Pip) 'UniverseContext)
      (v/assert kb (list t2 Pip) 'UniverseContext)
      (v/clear-violations! kb)
      (v/assert kb (list 'disjoint t1 t2) 'UniverseContext)
      (let [cut (filter #(= :arbitration-truncated (:violation %)) (v/violations kb))]
        ;; One entry, and this settle takes one pass — so what the entry's `:triggers`
        ;; counts is not separated here from what the passes counted.  That is the test
        ;; below, over a settle that iterates.
        (is (= 1 (count cut))
            "one entry for the settle")
        (is (= 2 (get-in (first cut) [:detail :budget])))
        (is (<= (count (get-in (first cut) [:detail :sample])) 3)
            "a sample rather than the whole list")
        (is (re-find #"undecided" (get-in (first cut) [:detail :message]))
            "and it says what was left undone, not merely that a bound was hit")))))

(tu/deftest-kb a-settle-of-several-passes-files-one-trigger-per-declaration
  ;; What `report-arbitration-cut!`'s `distinct` is for, over a settle that can show it.
  ;;
  ;; The sweep runs once per settle **pass** — `constraint-nogoods` re-derives the
  ;; definitional clashes per pass, over a region that accumulates until `settle-finish`
  ;; clears it — so a declaration the budget cut short is noted again on every pass that
  ;; re-reaches it.  `:triggers` is a count a reader acts on ("how many declarations went
  ;; unswept"), so counting the notes instead of the declarations would report two
  ;; unswept declarations where there is one, and the number would move with a fixpoint
  ;; the reader has no way to see.
  ;;
  ;; A one-pass settle cannot separate the two, which is why the test above does not: it
  ;; files one note and reads one trigger whether or not anything dedups.  The
  ;; `exceptWhen` is what makes this settle iterate, and the **write order inside the
  ;; batch** is what makes the exception block rather than refuse: each assertion still
  ;; forward-chains as it lands, so the rule fires on a bird nothing yet excepts, and the
  ;; membership that excepts it arrives after the conclusion is believed.  The first pass
  ;; then moves the blocked set and a second runs to confirm.  (Both facts written before
  ;; the batch, or the excepting one written first, and the firing is refused at derive
  ;; time instead — nothing is blocked, the queue drains empty, and the settle converges
  ;; in a single pass.)  The whole batch is one `with-deferred-settle`, since the cut
  ;; sweep and the extra pass have to be the same settle.
  (binding [checks/*arbitrate-constraints?* true
            settle/*exposure-instance-budget* 2]
    (tu/with-terms [t1 t2 Pip bird penguin flies Opus]
      ;; the separation, with a reach the budget cannot finish
      (v/assert kb (list 'genl t1 'thing) 'UniverseContext)
      (v/assert kb (list 'genl t2 'thing) 'UniverseContext)
      (dotimes [_ 20] (v/assert kb (list t1 (tu/tmp-ind "Filler")) 'UniverseContext))
      (dotimes [_ 20] (v/assert kb (list t2 (tu/tmp-ind "Other")) 'UniverseContext))
      (v/assert kb (list t1 Pip) 'UniverseContext)
      (v/assert kb (list t2 Pip) 'UniverseContext)
      ;; ...and the excepted rule, over vocabulary the separation does not reach
      (v/assert kb (list 'exceptWhen (list penguin '?x)
                         (list 'set/defaultRule
                               (vr/rule-sentence [(list bird '?x)] (list flies '?x))))
                'UniverseContext)
      (v/clear-violations! kb)
      (v/with-deferred-settle kb
        (v/assert kb (list 'disjoint t1 t2) 'UniverseContext)
        (v/assert kb (list bird Opus) 'UniverseContext)
        (v/assert kb (list penguin Opus) 'UniverseContext))
      (let [cut (filter #(= :arbitration-truncated (:violation %)) (v/violations kb))]
        (is (<= 2 (:passes (v/settle-stats kb)))
            "the premise of the test: a settle of one pass sweeps once and dedups nothing")
        (is (= 1 (count cut)) "one entry for the settle")
        (is (= 1 (get-in (first cut) [:detail :triggers]))
            "one declaration went unswept — not one per pass that swept it short")
        (is (= 1 (count (get-in (first cut) [:detail :sample])))
            "and the sample names it once")
        (testing "the exception that made the settle iterate did its own job"
          (is (empty? (v/sentexes-matching kb (list flies Opus) 'UniverseContext))))))))

(tu/deftest-kb a-functional-declaration-swept-short-is-reported-by-nothing-else
  ;; `functional` implicates stored content on the deciding path and on no other, so a
  ;; reader watching only `:exposure-truncated` would never learn its sweep was cut.
  (binding [checks/*arbitrate-constraints?* true
            settle/*exposure-instance-budget* 2]
    (tu/with-terms [ownerOf]
      (v/assert kb (list 'binaryPredicate ownerOf) 'UniverseContext)
      (dotimes [_ 20]
        (v/assert kb (list ownerOf (tu/tmp-ind "Thing") (tu/tmp-ind "Who")) 'UniverseContext))
      (v/clear-violations! kb)
      (v/assert kb (list 'functional ownerOf) 'UniverseContext)
      (let [vs (v/violations kb)]
        (is (seq (filter #(= :arbitration-truncated (:violation %)) vs))
            "the deciding pass reports it")
        (is (empty? (filter #(= :exposure-truncated (:violation %)) vs))
            "and the exposure pass has no arm that would")))))

(tu/deftest-kb a-sweep-that-finished-reports-nothing
  (binding [checks/*arbitrate-constraints?* true
            settle/*exposure-instance-budget* 4096]
    (tu/with-terms [t1 t2 Pip]
      (v/assert kb (list 'genl t1 'thing) 'UniverseContext)
      (v/assert kb (list 'genl t2 'thing) 'UniverseContext)
      (v/assert kb (list t1 Pip) 'UniverseContext)
      (v/assert kb (list t2 Pip) 'UniverseContext)
      (v/clear-violations! kb)
      (v/assert kb (list 'disjoint t1 t2) 'UniverseContext)
      (is (empty? (filter #(= :arbitration-truncated (:violation %)) (v/violations kb)))
          "a bound nothing reached is not a truncation")
      (is (seq (v/contradictions kb)) "and the pair it did reach is decided"))))

(tu/deftest-kb a-rebuild-still-sweeps-but-files-no-cut
  ;; Two claims at two budgets, because one budget cannot show both.  The *report* is off
  ;; on a rebuild, like the exposure pass beside it: that settle's region is the whole KB,
  ;; so every declaration in it is cut the moment the budget is spent, and a notice per
  ;; recover would say nothing about the KB and everything about its size.
  ;;
  ;; The *sweep* is not gated the same way.  `recover` binds the flag around two settles
  ;; and the second one's region is only what re-recording the refusals moved — so a
  ;; declaration there still needs its sweep, and a KB that came up without it would
  ;; disagree with one that never restarted.
  (binding [checks/*arbitrate-constraints?* true]
    (let [build (fn [k t1 t2 Pip]
                  (v/assert k (list 'genl t1 'thing) 'UniverseContext)
                  (v/assert k (list 'genl t2 'thing) 'UniverseContext)
                  (dotimes [_ 20] (v/assert k (list t1 (tu/tmp-ind "Filler")) 'UniverseContext))
                  (dotimes [_ 20] (v/assert k (list t2 (tu/tmp-ind "Other")) 'UniverseContext))
                  (v/assert k (list t1 Pip) 'UniverseContext)
                  (v/assert k (list t2 Pip) 'UniverseContext)
                  (v/clear-violations! k))]
      (testing "a budget too small to finish files no notice, because it is a rebuild"
        (tu/with-terms [t1 t2 Pip]
          (tu/with-kb [k]
            (build k t1 t2 Pip)
            (binding [settle/*exposure-instance-budget* 2
                      settle/*rebuilding?* true]
              (v/assert k (list 'disjoint t1 t2) 'UniverseContext))
            (is (empty? (filter #(= :arbitration-truncated (:violation %)) (v/violations k)))
                "off, as it is for the exposure pass"))))
      (testing "and a budget that can finish still decides the pair, rebuilding or not —
                the sweep itself is not gated on the flag"
        (tu/with-terms [t1 t2 Pip]
          (tu/with-kb [k]
            (build k t1 t2 Pip)
            (binding [settle/*exposure-instance-budget* 4096
                      settle/*rebuilding?* true]
              (v/assert k (list 'disjoint t1 t2) 'UniverseContext))
            (is (= [:disjoint] (mapv :kind (v/contradictions k))))))))))

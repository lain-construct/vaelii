;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.settle-region-cost-test
  "What a settle costs, as call counts rather than durations, for `assert_cost_test`'s
  reason: a count is a property of the algorithm and a millisecond a property of the
  box (docs/nmtms.md, \"The runtime of a settle\").

  * The relabelled region is materialized `passes + 1` times: one delay per pass, and one
    at the finish, which `record-clashes!` forces even on a rebuild.
  * A `genl` or `genlCx` edge no standing clash depends on re-derives none of them.  The
    bound is zero, which cannot drift upward; a plain fact retracted beside each edge is
    the control, and `clash_oracle_test` / `negation_oracle_test` hold the answers.
  * A definitional clash is re-asked at its vantages only after a round that defeated.
  * The phase clock charges seven buckets, and a settle's total is the sum of its own.
  * A settle reads the standing merges and `except`s only where they moved: a batch of
    merges reads the region once per settle, an un-merge re-examines its own class, and
    resolution's flip check reads no `except` root when the region is smaller, and an
    assert the excepts' regions do not reach recomputes no reader's withdrawal."
  (:require [clojure.set :as set]
            [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.settle :as settle]
            [vaelii.impl.settle-phases :as phases]
            [vaelii.impl.special :as special]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(def ^:private n
  "Standing dilemmas per workload, so a per-pair term shows as a three-digit count."
  60)

;; ---- how many times the region is materialized ---------------------------

(defn- region-reads
  "`jtms/touched` calls made while `f` runs.  The read is what materializes the region, so
  the read is what is counted; `jtms/revived`'s one-arity reads through this var too."
  [f]
  (let [calls (atom 0)
        orig  jtms/touched]
    (with-redefs [jtms/touched (fn [& args] (swap! calls inc) (apply orig args))]
      (f))
    @calls))

(def ^:private one-pass-reads
  "Region materializations of a one-pass settle: the pass's delay and the finish's."
  2)

(deftest a-settle-materializes-its-region-once-per-pass-and-once-at-the-finish
  (let [kb (tu/isolated-fresh)]
    (try
      (tu/with-shipped-config
        ;; one write outside the count, so no reading below is a class-loading first call
        (v/assert kb '(srm_warm SrmWarm) 'CxUniverse {})
        (testing "a plain fact — nothing derived, nothing opposed, nothing merged"
          (is (= one-pass-reads (region-reads #(v/assert kb '(srm_plain SrmA) 'CxUniverse {})))))
        (testing "a forward rule firing"
          (v/assert-rule kb ['(srm_trig ?x)] '(srm_concl ?x) 'CxUniverse {:direction :forward})
          (is (= one-pass-reads (region-reads #(v/assert kb '(srm_trig SrmB) 'CxUniverse {}))))
          (is (v/ask? kb '(srm_concl SrmB) 'CxUniverse) "the firing must have placed"))
        (testing "and a retraction"
          (let [h (v/handle-of kb '(srm_plain SrmA) 'CxUniverse)]
            (is (= one-pass-reads (region-reads #(v/retract! kb h)))))))
      (finally (tu/clear-kb! kb)))))

(deftest a-batch-is-charged-per-settle-and-not-per-write
  (let [kb (tu/isolated-fresh)]
    (try
      (tu/with-shipped-config
        (v/assert kb '(srm_warm SrmWarm) 'CxUniverse {})
        (is (= one-pass-reads
               (region-reads #(v/with-deferred-settle kb
                                (dotimes [i 50]
                                  (v/assert kb (list 'srm_batch (symbol (str "SrmZ" i)))
                                            'CxUniverse {})))))))
      (finally (tu/clear-kb! kb)))))

(deftest a-defeat-costs-one-region-read-and-a-revival-costs-two
  ;; a defeat converges in the pass that discovers it, and a revival takes a second pass,
  ;; so the reading moves by one: the growth term is the pass, not the belief move
  (let [kb (tu/isolated-fresh)]
    (try
      (tu/with-shipped-config
        (v/assert kb '(srm_neg SrmX) 'CxUniverse {})
        (testing "the defeat converges in one pass"
          (is (= one-pass-reads
                 (region-reads #(v/assert kb '(not (srm_neg SrmX)) 'CxUniverse
                                          {:strength :monotonic}))))
          (is (not (v/ask? kb '(srm_neg SrmX) 'CxUniverse)) "the default must have lost"))
        (testing "the revival takes a second, and one more region read with it"
          (let [h (v/handle-of kb '(not (srm_neg SrmX)) 'CxUniverse)]
            (is (= (inc one-pass-reads) (region-reads #(v/retract! kb h)))))
          (is (v/ask? kb '(srm_neg SrmX) 'CxUniverse) "the default must be believed again")))
      (finally (tu/clear-kb! kb)))))

;; ---- the clash memo ------------------------------------------------------

(defn- clash-kb
  "n individuals each holding two separated types, so the KB carries n standing
  definitional dilemmas — plus the two victims: one `genl` edge with nothing above or
  below it, and one plain fact."
  [kb]
  (v/assert kb '(disjoint srca_t srcb_t) 'CxUniverse {:strength :monotonic})
  (dotimes [i n]
    (let [x (symbol (str "SRC" i))]
      (v/assert kb (list 'srca_t x) 'CxUniverse {})
      (v/assert kb (list 'srcb_t x) 'CxUniverse {})))
  (v/assert kb '(genl srcvictim_t srctop_t) 'CxUniverse {:strength :monotonic})
  (v/assert kb '(src_plain SrcTarget) 'CxUniverse {})
  kb)

(defn- arbitrable-calls
  "`checks/arbitrable-violations` calls made while `f` runs."
  [f]
  (let [calls (atom 0)
        orig  checks/arbitrable-violations]
    (with-redefs [checks/arbitrable-violations
                  (fn [& args] (swap! calls inc) (apply orig args))]
      (f))
    @calls))

(deftest a-genl-edge-elsewhere-re-derives-no-standing-clash
  (let [kb (tu/fresh)]
    (try
      (binding [checks/*arbitrate-constraints?* true]
        (clash-kb kb)
        (is (= n (count (v/contradictions kb)))
            "the standing set is standing, or the counts below are about an empty memo")
        (testing "retracting the lone genl edge asks the checks nothing"
          (let [h (v/handle-of kb '(genl srcvictim_t srctop_t) 'CxUniverse)]
            (is (zero? (arbitrable-calls #(v/retract! kb h))))))
        (testing "and asserting it back asks them nothing either"
          (is (zero? (arbitrable-calls
                      #(v/assert kb '(genl srcvictim_t srctop_t) 'CxUniverse
                                 {:strength :monotonic})))))
        (testing "the control: a plain fact leaving is already free"
          (let [h (v/handle-of kb '(src_plain SrcTarget) 'CxUniverse)]
            (is (zero? (arbitrable-calls #(v/retract! kb h))))))
        (is (= n (count (v/contradictions kb)))
            "and every standing dilemma is still reported"))
      (finally (tu/clear-kb! kb)))))

;; ---- the negation memo ---------------------------------------------------

(defn- negation-kb
  "n P/¬P dilemmas sharing no body, plus the two victims: one `genlCx` edge with nothing
  below it, and one plain fact.  No separation, so the clash memo is not asked."
  [kb]
  (dotimes [i n]
    (let [pr (symbol (str "srneg" i))
          x  (symbol (str "SRN" i))]
      (v/assert kb (list pr x) 'CxUniverse {})
      (v/assert kb (list 'not (list pr x)) 'CxUniverse {})))
  (v/assert kb '(genlCx CxSrVictim CxUniverse) 'CxUniverse {})
  (v/assert kb '(sr_plain SrTarget) 'CxUniverse {})
  kb)

(defn- rederived-bodies
  "Opposed bodies re-derived while `f` runs: `settle/body-nogoods` is the only
  re-derivation site."
  [f]
  (let [calls (atom 0)
        orig  @#'settle/body-nogoods]
    (with-redefs [settle/body-nogoods (fn [& args] (swap! calls inc) (apply orig args))]
      (f))
    @calls))

(deftest a-genlCx-edge-elsewhere-re-derives-no-standing-pairing
  (let [kb (tu/fresh)]
    (try
      (negation-kb kb)
      (is (= n (count (v/contradictions kb)))
          "the standing set is standing, or the counts below are about an empty memo")
      (testing "retracting the lone genlCx edge re-derives no body"
        (let [h (v/handle-of kb '(genlCx CxSrVictim CxUniverse)
                             'CxUniverse)]
          (is (zero? (rederived-bodies #(v/retract! kb h))))))
      (testing "and asserting it back re-derives none either"
        (is (zero? (rederived-bodies
                    #(v/assert kb '(genlCx CxSrVictim CxUniverse)
                               'CxUniverse {})))))
      (testing "the control: a plain fact leaving is already free"
        (let [h (v/handle-of kb '(sr_plain SrTarget) 'CxUniverse)]
          (is (zero? (rederived-bodies #(v/retract! kb h))))))
      (is (= n (count (v/contradictions kb)))
          "and every standing dilemma is still reported")
      (finally (tu/clear-kb! kb)))))

;; ---- the grounds re-ask --------------------------------------------------

(defn- reasked-clashes
  "`settle/reads-clash?` calls made while `f` runs."
  [f]
  (let [calls (atom 0)
        orig  @#'settle/reads-clash?]
    (with-redefs [settle/reads-clash? (fn [& args] (swap! calls inc) (apply orig args))]
      (f))
    @calls))

(deftest a-definitional-clash-is-re-asked-only-after-a-round-that-defeated
  (let [kb (tu/fresh)]
    (try
      (binding [checks/*arbitrate-constraints?* true]
        (v/assert kb '(disjoint srr_a srr_b) 'CxUniverse {:strength :monotonic})
        (v/assert kb '(srr_a SrrY) 'CxUniverse {})
        (testing "a settle whose one round defeats nothing re-asks nothing"
          (is (zero? (reasked-clashes #(v/assert kb '(srr_b SrrY) 'CxUniverse {}))))
          (is (= 1 (count (v/contradictions kb))) "the premise: a standing dilemma"))
        (testing "a round that defeated re-asks the clash still standing beside it"
          (v/assert kb '(srr_a SrrX) 'CxUniverse {:strength :monotonic})
          (v/assert-rule kb ['(srr_src ?z)] '(srr_b ?z) 'CxUniverse {:direction :forward})
          (is (pos? (reasked-clashes #(v/assert kb '(srr_src SrrX) 'CxUniverse {}))))
          (is (not (v/ask? kb '(srr_b SrrX) 'CxUniverse)) "the premise: round one defeated")))
      (finally (tu/clear-kb! kb)))))

;; ---- the phase clock -----------------------------------------------------

(deftest the-phase-clock-partitions-each-settle-into-its-buckets
  (let [kb (tu/fresh)]
    (try
      (phases/start)
      (v/assert kb '(srp_fact SrpA) 'CxUniverse {})
      (v/assert kb '(not (srp_fact SrpA)) 'CxUniverse {})
      (let [{:keys [run settles]} (phases/stop)]
        (is (= #{:belief :discovery :resolution :chaining :finish :glue :outside}
               (set (keys run))))
        (is (seq settles))
        (doseq [s settles]
          (is (= (:total s) (reduce + (vals (:nanos s)))))
          (is (pos? (:passes s)))))
      (finally (phases/stop) (tu/clear-kb! kb)))))

;; ---- the scans a settle runs over a standing population ---------------------

(defn- calls-to
  "Calls made to the var `v` while `f` runs, each call's arguments kept."
  [v f]
  (let [calls (atom [])
        orig  @v]
    (with-redefs-fn {v (fn [& args] (swap! calls conj args) (apply orig args))} f)
    @calls))

(defn- merge-kb
  "`kb` holding `n` standing `sameAs` merges, each displacing one fact of its own, asserted
  under one deferred settle.  Returns the displaced facts' handles."
  [kb n]
  (let [hs (volatile! [])]
    (v/with-deferred-settle kb
      (dotimes [i n]
        (vswap! hs conj (v/assert kb (list 'srmBorn (symbol (str "SrmHi" i)) 'SrmPlace)
                                  'CxUniverse {}))
        (v/assert kb (list 'sameAs (symbol (str "SrmAa" i)) (symbol (str "SrmHi" i)))
                  'CxUniverse {})))
    @hs))

(deftest a-batch-of-merges-reads-the-region-once-per-settle
  ;; the write path's supersession reconcile leaves the window to the batch's settle
  (let [kb (tu/isolated-fresh)]
    (try
      (tu/with-shipped-config
        (v/assert kb '(srm_warm SrmWarm) 'CxUniverse {})
        (let [reads (fn [tag n]
                      (region-reads
                       #(v/with-deferred-settle kb
                          (dotimes [i n]
                            (v/assert kb (list 'srmBorn (symbol (str "SrmZ" tag i)) 'SrmPlace)
                                      'CxUniverse {})
                            (v/assert kb (list 'sameAs (symbol (str "SrmC" tag i))
                                               (symbol (str "SrmZ" tag i)))
                                      'CxUniverse {})))))]
          ;; each merge displaces its fact: `SrmC…` sorts first and represents the class
          (is (= (reads "a" 1) (reads "b" 20)))))
      (finally (tu/clear-kb! kb)))))

(deftest an-un-merge-re-examines-the-class-it-split-and-no-standing-merge
  (let [kb (tu/isolated-fresh)]
    (try
      (tu/with-shipped-config
        (let [standing (set (merge-kb kb n))
              f        (v/assert kb '(srmBorn SrmVHi SrmPlace) 'CxUniverse {})
              e        (v/assert kb '(sameAs SrmVAa SrmVHi) 'CxUniverse {})
              examined (into #{} (map #(nth % 2))
                             (calls-to #'special/displacement #(v/retract! kb e)))]
          (is (contains? examined f) "the split class's own displaced fact is re-examined")
          (is (empty? (set/intersection standing examined)))
          (is (v/ask? kb '(srmBorn SrmVHi SrmPlace) 'CxUniverse)
              "the spelling the un-merge gave back is believed")))
      (finally (tu/clear-kb! kb)))))

(deftest a-settle-hands-the-belief-reconcile-no-supersession-it-did-not-move
  (let [kb (tu/isolated-fresh)]
    (try
      (tu/with-shipped-config
        (let [standing (set (merge-kb kb n))
              handed   (into #{} (comp (map second) cat)
                             (calls-to #'special/reconcile-belief-change
                                       #(v/assert kb '(srm_plain SrmUnrelated) 'CxUniverse {})))]
          (is (every? #(jtms/superseded? (reasoning/tms kb) %) standing))
          (is (empty? (set/intersection standing handed)))))
      (finally (tu/clear-kb! kb)))))

(deftest a-settle-over-standing-excepts-reads-no-except-root-when-its-region-is-smaller
  ;; resolution's flip check walks the smaller side (`settle/resolution-watch`)
  (let [kb (tu/isolated-fresh)]
    (try
      (tu/with-shipped-config
        (dotimes [i n]
          (let [h (v/assert kb (list 'srm_decoy (symbol (str "SrmD" i))) 'CxUniverse
                            {:strength :monotonic})]
            (v/assert kb (list 'except (sx/sentex-handle h)) 'CxUniverse {:strength :monotonic})))
        (is (empty? (filter #(= sx/except-functor (second %))
                            (calls-to #'reads/believed-with-functor
                                      #(v/assert kb '(srm_plain SrmAfterExcepts) 'CxUniverse {}))))))
      (finally (tu/clear-kb! kb)))))

(deftest an-assert-beside-standing-excepts-it-does-not-touch-recomputes-no-withdrawal
  ;; the settle keeps the `:withdrawn` entries its moves do not reach
  ;; (`res/reconcile-withdrawn!`); both the reader's withdrawal and the roster walk the
  ;; region with `grounded-in-region`
  (let [kb (tu/isolated-fresh)]
    (try
      (tu/with-shipped-config
        (dotimes [i n]
          (let [h (v/assert kb (list 'srm_decoy (symbol (str "SrmD" i))) 'CxUniverse
                            {:strength :monotonic})]
            (v/assert kb (list 'except (sx/sentex-handle h)) 'CxUniverse {:strength :monotonic})))
        (let [read-both #(do (res/supporter-filter-roster kb) (res/withdrawal kb 'CxUniverse))
              before    (read-both)]
          (is (= n (count (:out before))))
          (is (zero? (count (calls-to #'jtms/grounded-in-region
                                      #(do (v/assert kb '(srm_plain SrmBesideExcepts)
                                                     'CxUniverse {})
                                           (read-both))))))))
      (finally (tu/clear-kb! kb)))))

;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.clash-reading-cost-test
  "What a reading of the standing clashes costs, as counts.  Two claims, both exact
  integers rather than durations, for `assert_cost_test`'s reason — a call count is a
  property of the algorithm where a millisecond is a property of the box.  `lein perf`'s
  `standing-clash-reading` bounds the *ratio* over a growing standing set, and a ratio
  divides out a constant factor per report, so neither claim below is reachable from it.

  ## One: the reader arity builds the hidden predicate once per call

  `core/contradictions`'s reader arity keeps an entry only where the reader believes every
  member, and belief there is `res/excepted?` — `hidden-fn`, which reads the `except`
  roster and the reader's `genlCx` ancestor set to build a predicate, then answers a
  handle with a lookup.  Asked per member it builds that predicate `2 x reports` times per
  reading and throws each one away; asked once for the reading it builds one.  Pinned at
  **1** below, at two sizes, so the count is a property of the call and not of the KB.

  ## Two: a read builds no disagreement report

  A report reads a sentence and the supporting justifications of every side and sorts
  them on content, which is why `clashes/read-clashes` keeps each report it built while its
  inputs stand (`:read-reports`), the report for a nogood whose vantages took different
  members OUT among them.  Pinned below at **no build per read**: a reading after an
  unrelated settle finds the pair's report and builds nothing."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.clashes :as clashes]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.test-util :as tu]))

;; ---- one: the hidden predicate per reading -------------------------------

(defn- hidden-fn-builds
  "`res/hidden-fn` calls made while `f` runs.  Redefined rather than instrumented, because
  building the predicate is what costs and the engine carries no counter for it."
  [f]
  (let [calls (atom 0)
        orig  res/hidden-fn]
    (with-redefs [res/hidden-fn (fn [& args] (swap! calls inc) (apply orig args))]
      (f))
    @calls))

(def ^:private builds-per-reading
  "Hidden predicates a reader's `contradictions` builds: one for the reading."
  1)

(defn- dilemma-world!
  "n standing P/-P dilemmas in `cx`, plus one believed `except` over a decoy, so the
  reader's `hidden-fn` is a predicate rather than the nil an unexcepting KB answers."
  [kb cx n]
  (v/with-deferred-settle kb
    (let [decoy (v/assert kb '(crc_decoy CrcDecoy) cx {:strength :monotonic})]
      (v/assert kb (list 'except (list 'sentexHandle decoy)) cx {:strength :monotonic}))
    (dotimes [i n]
      (let [s (list (symbol (str "crc_p" i)) (symbol (str "CrcX" i)))]
        (v/assert kb s cx {})
        (v/assert kb (list 'not s) cx {})))))

(deftest a-reader-s-clash-reading-builds-one-hidden-predicate-whatever-it-reads
  (doseq [n [4 40]]
    (testing (str n " standing dilemmas")
      (let [kb (tu/isolated-fresh)]
        (try
          (tu/with-shipped-config
            (tu/with-terms [CxCrcHold CxCrcRead]
              (v/assert kb (list 'genlCx CxCrcHold 'CxUniverse) 'CxUniverse)
              (v/assert kb (list 'genlCx CxCrcRead CxCrcHold) 'CxUniverse)
              (dilemma-world! kb CxCrcHold n)
              ;; one reading outside the count, so the measured one is not a first call
              (v/contradictions kb CxCrcRead)
              (is (= n (count (v/contradictions kb CxCrcRead)))
                  "the reader must read every dilemma, or the count below measures nothing")
              (is (= builds-per-reading
                     (hidden-fn-builds #(v/contradictions kb CxCrcRead))))))
          (finally (tu/clear-kb! kb)))))))

;; ---- two: the disagreement reports per settle ----------------------------

(defn- clash-report-builds
  "`clashes/clash-report` calls made while `f` runs."
  [f]
  (let [calls (atom 0)
        orig  @#'clashes/clash-report]
    (with-redefs-fn {#'clashes/clash-report (fn [& args] (swap! calls inc) (apply orig args))}
      (fn [] (f)))
    @calls))

(defn- types! [kb & ts]
  (doseq [t ts] (v/assert kb (list 'genl t 'thing) 'CxUniverse)))

(deftest a-read-builds-no-disagreement-report
  ;;   CxUniverse
  ;;     +- CxCrcA      (crc_cat CrcRex) default, and monotonic through a rule
  ;;     +- CxCrcB      (crc_dog CrcRex) default, and monotonic through a rule
  ;;     +- CxCrcH1     (except (sentexHandle (crc_cat_src CrcRex)))
  ;;     +- CxCrcH2     (except (sentexHandle (crc_dog_src CrcRex)))
  ;;   CxCrcW1 - sees CxCrcA CxCrcB CxCrcH1, so it defeats cat
  ;;   CxCrcW2 - sees CxCrcA CxCrcB CxCrcH2, so it defeats dog
  ;;   CxCrcZ  - sees both vantages and both excepts, so it reads a tie
  (tu/with-neutral-kb [kb #(tu/fresh)]
    (tu/with-terms [CxCrcA CxCrcB CxCrcH1 CxCrcH2 CxCrcW1 CxCrcW2 CxCrcZ
                    crc_cat crc_dog crc_cat_src crc_dog_src CrcRex]
      (types! kb crc_cat crc_dog)
      (doseq [c [CxCrcA CxCrcB CxCrcH1 CxCrcH2]]
        (v/assert kb (list 'genlCx c 'CxUniverse) 'CxUniverse))
      (doseq [[vantage hide] [[CxCrcW1 CxCrcH1] [CxCrcW2 CxCrcH2]]
              up             [CxCrcA CxCrcB hide]]
        (v/assert kb (list 'genlCx vantage up) 'CxUniverse))
      (doseq [up [CxCrcW1 CxCrcW2]] (v/assert kb (list 'genlCx CxCrcZ up) 'CxUniverse))
      (v/assert kb (list crc_cat CrcRex) CxCrcA)
      (v/assert kb (list 'set/forwardRule (list 'implies (list crc_cat_src '?x)
                                                (list crc_cat '?x)))
                CxCrcA {:strength :monotonic})
      (let [cat-src (v/assert kb (list crc_cat_src CrcRex) CxCrcA {:strength :monotonic})]
        (v/assert kb (list crc_dog CrcRex) CxCrcB)
        (v/assert kb (list 'set/forwardRule (list 'implies (list crc_dog_src '?x)
                                                  (list crc_dog '?x)))
                  CxCrcB {:strength :monotonic})
        (let [dog-src (v/assert kb (list crc_dog_src CrcRex) CxCrcB {:strength :monotonic})]
          (v/assert kb (list 'except (list 'sentexHandle cat-src)) CxCrcH1
                    {:strength :monotonic})
          (v/assert kb (list 'except (list 'sentexHandle dog-src)) CxCrcH2
                    {:strength :monotonic})
          (v/assert kb (list 'disjoint crc_dog crc_cat) 'CxUniverse)))
      (testing "the disagreement is on the roster, or the counts below measure nothing"
        (is (= 1 (count (filter :vantages (v/contradictions kb))))))
      (testing "a reading after an unrelated settle finds the report and builds nothing"
        (v/assert kb '(crc_unrelated CrcU) 'CxUniverse {})
        (is (zero? (clash-report-builds #(v/contradictions kb CxCrcZ))))
        (is (zero? (clash-report-builds #(v/contradictions kb))))
        (is (zero? (clash-report-builds #(v/contradictions kb CxCrcW1))))
        (is (= 1 (count (filter :vantages (v/contradictions kb)))))))))

;; ---- three: the membership lookup builds no closure ----------------------

(defn- lookup-closure-reads
  "`[lookups closure-reads]` while `f` runs: `checks/membership-handles-led` calls, and the
  `tax/genls` / `tax/genls-global` calls made inside one."
  [f]
  (let [lookups (atom 0)
        reads   (atom 0)
        inside  (atom false)
        led     @#'checks/membership-handles-led
        counted (fn [orig] (fn [& args] (when @inside (swap! reads inc)) (apply orig args)))]
    (with-redefs-fn {#'checks/membership-handles-led
                     (fn [& args]
                       (swap! lookups inc)
                       (reset! inside true)
                       (try (apply led args) (finally (reset! inside false))))
                     #'tax/genls        (counted tax/genls)
                     #'tax/genls-global (counted tax/genls-global)}
      (fn [] (f)))
    [@lookups @reads]))

(deftest a-clash-s-membership-lookup-reads-no-supertype-closure
  ;; `checks/membership-handles` names the `(t x)` sentex a clash is with by testing every
  ;; type `x` holds against `t`, including types no clash is about.  A closure read there
  ;; builds the supertype closure of each, which on a large taxonomy is most of a settle;
  ;; `crc_deep` sits under a chain so its closure is one a read would build.
  (tu/with-neutral-kb [kb #(tu/fresh)]
    (tu/with-terms [crc_a crc_b crc_deep crc_mid crc_top CrcX]
      (types! kb crc_a crc_b crc_top)
      (v/assert kb (list 'genl crc_mid crc_top) 'CxUniverse)
      (v/assert kb (list 'genl crc_deep crc_mid) 'CxUniverse)
      (v/assert kb (list 'disjoint crc_a crc_b) 'CxUniverse {:strength :monotonic})
      (v/assert kb (list crc_deep CrcX) 'CxUniverse {})
      (v/assert kb (list crc_a CrcX) 'CxUniverse {})
      (doseq [lead [:auto :agnostic]]
        (testing (str "leading " lead)
          (binding [res/*lead-side* lead]
            (let [h                (atom nil)
                  [lookups reads]  (lookup-closure-reads
                                    #(reset! h (v/assert kb (list crc_b CrcX) 'CxUniverse {})))]
              (is (pos? lookups) "the clash looked its members up, or the count measures nothing")
              (is (zero? reads))
              (is (= 1 (count (v/contradictions kb))))
              (v/retract! kb @h))))))))

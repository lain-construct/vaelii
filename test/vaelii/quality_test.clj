;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.quality-test
  "`kb-quality` — the four readings about the knowledge rather than about the engine.

  Every reading is a claim about a KB whose answer is known by construction, because that
  is the only way a distribution can be checked: a rule that fires twice, one that never
  fires, one whose every conclusion is defeated and one retracted after firing all look the
  same from a firing count alone, and the whole point of the census is that they do not
  land in the same category.

  The one test here that is not about correctness is
  `a-densely-cyclic-rule-graph-condenses-instead-of-re-exploring-it`.  A rule graph is
  cyclic in the ordinary case, and the failure it guards against is not a wrong answer, it
  is a report that never returns."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.quality :as quality]
            [vaelii.impl.rules :as vr]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- default-rule [antes conseq]
  (list 'set/defaultRule (vr/rule-sentence antes conseq)))

(defn- handles [entries] (set (map :handle entries)))

;; ---- which rules never fire ----------------------------------------------

(tu/deftest-kb the-four-firing-outcomes-land-in-three-different-categories
  (tu/with-terms [bird ghost penguin sings hasWings glows flies hasBeak
                  Robin Tweety Waddles]
    (let [fires   (v/assert-rule kb [(list bird '?x)] (list hasWings '?x) 'UniverseContext)
          never   (v/assert-rule kb [(list ghost '?x)] (list glows '?x) 'UniverseContext)
          beaten  (v/assert kb (default-rule [(list penguin '?x)] (list flies '?x))
                            'UniverseContext)
          undone  (v/assert-rule kb [(list sings '?x)] (list hasBeak '?x) 'UniverseContext)
          sang    (v/assert kb (list sings Robin) 'UniverseContext)]
      (v/assert kb (list bird Robin) 'UniverseContext)
      (v/assert kb (list bird Tweety) 'UniverseContext)
      (v/assert kb (list penguin Waddles) 'UniverseContext)
      ;; known-true, so it out-ranks the default conclusion the rule just placed
      (v/assert kb (list 'not (list flies Waddles)) 'UniverseContext {:strength :monotonic})
      (v/retract! kb sang)
      (let [q (:rules (v/kb-quality kb))]
        (testing "a rule with two supported conclusions is live, and both firings count"
          (is (= 1 (:fired q)))
          (is (<= 2 (:firings q)))
          (is (not (contains? (handles (:never q)) fires))))
        (testing "a rule nothing matched never fired"
          (is (contains? (handles (:never q)) never)))
        (testing "a rule whose *support* was retracted also reads as never fired — the
                  census counts currently-supported firings, and firings-ever is a
                  different question nothing here answers"
          (is (contains? (handles (:never q)) undone)))
        (testing "a rule that fired and had every conclusion defeated is its own category,
                  and it is the interesting one: it runs and contributes nothing"
          (is (= #{beaten} (handles (:all-defeated q))))
          (is (= 1 (:all-defeated-count q))))
        (testing ":firings is every recorded firing, the defeated ones included — so it is
                  not the live rules' share of them, and the report must not read as though
                  it were"
          (is (= 3 (:firings q))
              "two from the live rule, one from the rule whose conclusion is defeated"))
        (testing "each listed rule reads as its author wrote it, not as it is stored"
          (is (= (list 'implies (list ghost '?x) (list glows '?x))
                 (:sentence (first (filter #(= never (:handle %)) (:never q))))))
          (is (= 'UniverseContext
                 (:context (first (filter #(= never (:handle %)) (:never q)))))))))))

(tu/deftest-kb every-rule-the-index-can-key-is-in-the-census
  ;; the claim the cost argument rests on: rules are enumerated from the rule index, not by
  ;; scanning the record store, and the two must agree on a KB whose rules are all keyable
  (tu/with-terms [a_type b_type c_type pOne pTwo pThree]
    (v/assert-rule kb [(list a_type '?x)] (list pOne '?x) 'UniverseContext)
    (v/assert-rule kb [(list b_type '?x)] (list pTwo '?x) 'UniverseContext)
    (v/assert-rule kb [(list a_type '?x) (list b_type '?x)] (list pThree '?x) 'UniverseContext)
    (v/assert kb (list 'genl c_type a_type) 'UniverseContext)
    (let [recs    (:records kb)
          scanned (into #{} (filter #(some-> (p/get-sentex recs %) vr/rule?))
                        (p/sentex-ids recs))]
      (is (pos? (count scanned)))
      (is (= (count scanned) (:total (:rules (v/kb-quality kb))))))))

;; ---- extent skew ---------------------------------------------------------

(deftest gini-is-zero-when-nothing-is-skewed-and-approaches-one-when-everything-is
  (let [gini #'quality/gini]
    (testing "the degenerate ends"
      (is (= 0.0 (gini [])))
      (is (= 0.0 (gini [0 0 0])) "no extent at all is not skew")
      (is (= 0.0 (gini [5 5 5 5])) "every predicate the same size"))
    (testing "one predicate holding everything is (n-1)/n — 1.0 only in the limit, so a
              small vocabulary cannot reach it and the number must not be read as if it did"
      (is (= 0.75 (gini [0 0 0 10])))
      (is (< 0.99 (gini (conj (vec (repeat 999 0)) 1000)))))
    (testing "hand-computed: sorted [1 2 3 4] gives (2*30 - 5*10) / (4*10)"
      (is (= 0.25 (gini [1 2 3 4]))))))

(tu/deftest-kb the-extents-are-stored-counts-bucketed-by-order-of-magnitude
  (tu/with-terms [manyOf fewOf onceOf Holder]
    (dotimes [i 120] (v/assert kb (list manyOf Holder (symbol (str "QT" i))) 'UniverseContext))
    (dotimes [i 12]  (v/assert kb (list fewOf Holder (symbol (str "QF" i))) 'UniverseContext))
    (v/assert kb (list onceOf Holder Holder) 'UniverseContext)
    (let [e (:extents (v/kb-quality kb))]
      (testing "one bucket per order of magnitude, and the count is what is stored"
        (is (= 1 (get (:buckets e) 2)) "120 sits in 10^2")
        (is (= 1 (get (:buckets e) 1)) "12 in 10^1")
        (is (= 1 (get (:buckets e) 0)) "1 in 10^0")
        (is (= 133 (:stored e))))
      (testing "the heaviest are named, heaviest first"
        (is (= [manyOf 120] (first (:heaviest e))))
        (is (= [fewOf 12] (second (:heaviest e)))))
      (testing "and the skew is a single number beside the buckets"
        (is (< 0.0 (:gini e) 1.0))))))

(tu/deftest-kb a-limit-caps-each-listed-set-and-the-report-says-it-did
  (tu/with-terms [a_type pOne pTwo pThree pFour]
    ;; four *distinct* consequents: four rules identical up to variable names would
    ;; canonicalize to one handle, which is a different property and not this one
    (doseq [pred [pOne pTwo pThree pFour]]
      (v/assert-rule kb [(list a_type '?x)] (list pred '?x) 'UniverseContext))
    (let [q (:rules (v/kb-quality kb {:limit 2}))]
      (is (= 4 (:never-count q)) "the count is of the whole set")
      (is (= 2 (count (:never q))) "the list is not")
      (is (true? (:truncated? q)))
      (is (false? (:truncated? (:rules (v/kb-quality kb {:limit 100}))))))))

(tu/deftest-kb the-capped-list-is-chosen-by-content-not-by-the-order-the-rules-arrived
  ;; A handle is assertion order.  Ranking the capped set on one would make the *listed*
  ;; rules a function of the order an author happened to write them in while the counts
  ;; beside them are not — two loads of the same knowledge reporting the same totals over
  ;; different examples, which is the reading a baseline is compared against.
  ;;
  ;; The discriminator: assert the rules in the **reverse** of the order their consequent
  ;; names sort in.  Ranked by handle the listed pair would be the two asserted first (the
  ;; two largest names); ranked by content it is the two smallest, whenever they arrived.
  (tu/with-terms [a_type]
    (let [preds  (mapv #(tu/fresh-term :predicate (str "pFixed" %))
                       ["Alpha" "Beta" "Gamma" "Delta"])
          sorted (vec (sort-by str preds))]
      (doseq [p (reverse sorted)]
        (v/assert-rule kb [(list a_type '?x)] (list p '?x) 'UniverseContext))
      (let [q       (:rules (v/kb-quality kb {:limit 2}))
            shown   (into #{} (map #(nth (:sentence %) 2)) (:never q))
            wanted  (into #{} (map #(list % '?x)) (take 2 sorted))]
        (is (= 4 (:never-count q)) "all four are in the count")
        (is (= wanted shown)
            (str "and the two listed are the content-smallest, which are the two asserted "
                 "*last* — a handle ranking would have shown the other pair"))))))

;; ---- chain depth over the rule graph -------------------------------------

(tu/deftest-kb chain-depth-is-per-rule-and-counts-the-transitive-cycle-as-one
  (tu/with-terms [a_type pMid pTop chained]
    ;; a transitive rule is a self-loop in the functor graph, which is the commonest cycle
    ;; there is — `genl`'s own transitivity has this shape
    (v/assert-rule kb [(list chained '?x '?y) (list chained '?y '?z)]
                   (list chained '?x '?z) 'UniverseContext)
    (v/assert-rule kb [(list a_type '?x)] (list pMid '?x) 'UniverseContext)
    (v/assert-rule kb [(list pMid '?x)] (list pTop '?x) 'UniverseContext)
    (let [c (:chains (v/kb-quality kb))]
      (is (= 3 (:rules c)))
      (is (<= 1 (:cyclic c)) "the self-loop is a cycle of one node, not an acyclic node")
      (testing "depth is the longest path to a leaf, per rule"
        (is (= 1 (get (:depths c) 0)) "the transitive rule's own component leads nowhere")
        (is (= 1 (get (:depths c) 1)))
        (is (= 1 (get (:depths c) 2))))
      (testing "and the fraction at or above each depth, which a single number loses"
        (is (< 0.66 (get (:at-least c) 1) 0.67) "two of the three rules")
        (is (< 0.33 (get (:at-least c) 2) 0.34) "one of them")))))

(deftest a-densely-cyclic-rule-graph-condenses-instead-of-re-exploring-it
  ;; The incident this guards against was not a wrong answer: memoizing the *path* rather
  ;; than the node re-explored the whole reachable subgraph along every one of them, which
  ;; on a densely cyclic rule set is exponential and pinned two threads for hours with no
  ;; termination.  So the assertion is a wall clock, and the bound is generous on purpose —
  ;; what it separates is milliseconds from never.
  (let [n      20000
        preds  (mapv #(symbol (str "cyc" %)) (range n))
        conseq (into {} (map (fn [i] [i (nth preds i)])) (range n))
        ante   (into {} (map (fn [i] [i #{(nth preds (mod (dec i) n))
                                          (nth preds (mod (- i 100) n))}]))
                     (range n))
        ;; one rule above the cycle, so a depth is computed *over* the condensation rather
        ;; than merely surviving it
        conseq (assoc conseq n 'cycTop)
        ante   (assoc ante n #{(nth preds 0)})
        t0     (System/nanoTime)
        c      (#'quality/chain-depth {:ante ante :conseq conseq} (fn [_] nil))
        ms     (/ (- (System/nanoTime) t0) 1e6)]
    (is (= 2 (:components c)) "4,000 mutually reachable functors are one component")
    (is (= n (:largest c)))
    (is (= 1 (:cyclic c)))
    (is (= {0 n, 1 1} (:depths c)))
    (is (< ms 10000) (str "the condensation took " (long ms) " ms"))))

;; ---- taxonomy coverage ---------------------------------------------------

(tu/deftest-kb taxonomy-coverage-is-two-numbers-and-the-gap-between-them-is-the-finding
  (tu/with-terms [root_type mid_type leaf_type island_a island_b lonely_type Ownerless]
    (v/assert kb (list 'genl leaf_type mid_type) 'UniverseContext)
    (v/assert kb (list 'genl mid_type root_type) 'UniverseContext)
    ;; two types with an edge between them and no path to the root: covered by the first
    ;; number, not by the second, which is the whole reason there are two
    (v/assert kb (list 'genl island_a island_b) 'UniverseContext)
    ;; a type-shaped name in the vocabulary that no edge mentions at all
    (v/assert kb (list lonely_type Ownerless) 'UniverseContext)
    (let [t (:taxonomy (v/kb-quality kb))]
      (is (= root_type (:root t)) "the root is found, not assumed — nothing here is `thing`")
      (is (= 5 (:edged t)) "the five types some genl edge names")
      (is (= 3 (:rooted t)) "reflexively: leaf, mid, and the root itself")
      (is (= 2 (:islands t)) "the island pair, and nothing else")
      (testing "the denominator is every type-shaped name in the vocabulary — the six here
                plus `genl` itself, because a bare lowercase word is a legal type name as
                well as a legal predicate and the index records no arity to tell them
                apart.  Which is exactly why the *gap* above is the finding rather than
                either fraction on its own"
        (is (= 7 (:names t)))))))

;; ---- the options, and the emitter ----------------------------------------

(tu/deftest-kb an-option-nothing-reads-and-a-bound-that-is-not-one-are-refused
  (testing "a misspelt bound reads as no bound at all, which for a cap means uncapped"
    (let [e (try (v/kb-quality kb {:limt 5}) (catch clojure.lang.ExceptionInfo e e))]
      (is (= :unknown-option (:type (ex-data e))))
      (is (str/includes? (.getMessage ^Exception e) ":limt"))))
  (testing "and a known key holding a value it cannot mean"
    (doseq [bad [0 -1 "5" 2.5]]
      (is (= :unknown-option (:type (ex-data (try (v/kb-quality kb {:limit bad})
                                                  (catch clojure.lang.ExceptionInfo e e)))))
          (str "refused: " (pr-str bad))))))

(tu/deftest-kb the-phases-are-reported-in-order-and-a-throw-from-one-stops-the-report
  (let [seen (atom [])]
    (v/kb-quality kb {:on-progress #(swap! seen conj (:phase %))})
    (is (= [:extents :rules :chains :taxonomy] (distinct @seen))))
  (testing "the callback throwing is how a long report is cancelled — the reading is of
            current state, so a half-finished one is discarded rather than repaired"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"enough"
                          (v/kb-quality kb {:on-progress (fn [_] (throw (ex-info "enough" {})))})))))

(deftest the-report-renders-the-map-and-reads-nothing-else
  ;; the emitter takes the map, not the KB, so a figure it prints is one the data holds —
  ;; hand-built here for exactly that reason
  (let [md (v/quality-report
            {:rules    {:total 3 :never [{:handle 7 :sentence '(implies (a ?x) (b ?x))
                                          :context 'SomeContext}]
                        :never-count 1 :all-defeated [] :all-defeated-count 0
                        :fired 2 :firings 9 :truncated? false}
             :extents  {:predicates 4 :with-extent 2 :stored 130 :gini 0.5
                        :buckets {0 1, 2 1} :heaviest [['manyOf 120] ['fewOf 10]]}
             :chains   {:functors 5 :components 4 :cyclic 1 :largest 2 :rules 3
                        :depths {0 2, 1 1} :at-least {1 0.3333}}
             :taxonomy {:names 6 :edged 5 :root 'root_type :rooted 3 :islands 2}})]
    (is (str/starts-with? md "# KB quality"))
    (is (str/includes? md "3 rules — **1 never fired** (33.3%)"))
    (is (str/includes? md "2 live; 9 recorded firings in all")
        "the firing total is stated as a total, not as the live rules' share of one")
    (is (str/includes? md "(implies (a ?x) (b ?x))"))
    (is (str/includes? md "Gini 0.5000"))
    (is (str/includes? md "| 10^2 | 1 |"))
    (is (str/includes? md "`manyOf` — 120"))
    (is (str/includes? md "1 cyclic, largest 2"))
    (is (str/includes? md "reach `root_type`"))
    (is (str/includes? md "Edged but not reaching the root: 2"))
    (is (not (str/includes? md "The lists are capped")) "nothing was capped")))

(tu/deftest-kb a-kb-with-no-genl-edge-anywhere-has-no-root-to-report-against
  ;; the empty end of the taxonomy reading: a root that is nil is *no root*, which is a
  ;; different statement from a root nothing reaches — and an empty code span is neither
  (let [t (:taxonomy (v/kb-quality kb))]
    (is (nil? (:root t)))
    (is (zero? (:edged t)))
    (let [md (v/quality-report (v/kb-quality kb))]
      (is (str/includes? md "No `genl` edge anywhere, so there is no root"))
      (is (not (str/includes? md "reach ``")) "and never an empty name in a code span"))))

(deftest a-map-that-is-not-a-report-is-refused-rather-than-rendered-as-zeros
  ;; a page of zeros and dashes is a report a caller who passed the wrong map cannot tell
  ;; from a report of an empty KB
  (doseq [bad [{} nil {:rules {}} {:rules {:total 1}}]]
    (let [e (try (v/quality-report bad) (catch clojure.lang.ExceptionInfo e e))]
      (is (= :not-a-report (:type (ex-data e))) (str "refused: " (pr-str bad))))))

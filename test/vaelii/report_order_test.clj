;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.report-order-test
  "The justification reports say the same thing in either arrival order.

  `supporting-justifications`, `dependent-justifications` and the proof tree `why`
  builds are read off id **sets** and off the antecedent vector a firing filled as the
  work happened — and a handle is allocated in assertion order, so each of them could
  report one body of knowledge two ways according to how it was loaded.  Belief is not
  at stake in any of it; these are reporting surfaces, and they are public ones.

  Every test loads one scenario twice, in opposite orders, and demands a single reading.
  Two orders is the whole method: a single load cannot tell a content order from the
  arrival order it happens to agree with, and an assertion that the list merely *has*
  two entries passes against either.

  The projections are **handle-free** on purpose.  Two loads of one scenario allocate
  different handles for the same sentences, so a handle in the comparison would differ
  for the one reason that is not the subject; what is compared is what each report
  *says*.  A cleared KB per arm (`with-cleared-kb`, `witness_order_test`'s reason: each
  arm wants a store of its own), with the terms minted once outside both so the two
  arms are about the same knowledge."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.rules :as vr]
            [vaelii.test-util :as tu]))

(defn- fwd [antes conseq]
  (list 'set/forwardRule (vr/rule-sentence antes conseq)))

(defn- said
  "What a handle says — `[sentence context]` — or a symbol informant unchanged."
  [kb h]
  (if (integer? h)
    (let [sx (v/sentex kb h)] [(:sentence sx) (:context sx)])
    h))

(defn- listing
  "A justification listing as content: each entry's informant, its antecedents in the
  order the record holds them, and what it concludes."
  [kb js]
  (mapv (fn [j] {:informant   (said kb (:informant j))
                 :antecedents (mapv #(said kb %) (:antecedents j))
                 :conclusion  (said kb (:consequence j))})
        js))

(defn- proof
  "A `why` tree as content: the sentence at each node, and under it the sentences its
  justification named, in the order the report puts them.  `:justification` and
  `:informant` are dropped — both are handles."
  [w]
  (cond-> (select-keys w [:sentence :context :believed? :premise? :cycle? :stored?])
    (:support w)
    (assoc :support (mapv (fn [s] {:rule (:rule s) :because (mapv proof (:because s))})
                          (:support w)))))

(defn- both-orders
  "Run `load!` on a cleared KB once per ordering, and read each back with `read`.
  `load!` takes the KB and one ordering and returns whatever `read` needs."
  [orderings load! read]
  (mapv (fn [order]
          (tu/with-cleared-kb [kb tu/fresh]
            (read kb (load! kb order))))
        orderings))

;; ---- dependent-justifications -------------------------------------------

(deftest dependent-justifications-lists-the-same-dependents-in-either-order
  ;; Two rules over one fact, so the fact carries two dependents and something has to
  ;; order them.  `jtms/dependents` is the same allocation-ordered id set as
  ;; `jtms/supports`, and the ids are minted as the rules fire — which is the order the
  ;; rules were written in.  This is the API a caller uses for impact analysis before a
  ;; retract, so "which of these two comes first" is a question about the knowledge.
  (tu/with-terms [bird flies nests Robin CxStory]
    (let [flies-rule (fwd [(list bird '?x)] (list flies '?x))
          nests-rule (fwd [(list bird '?x)] (list nests '?x))
          readings   (both-orders
                      [[flies-rule nests-rule] [nests-rule flies-rule]]
                      (fn [kb rules]
                        (doseq [r rules] (v/assert kb r CxStory))
                        (v/assert kb (list bird Robin) CxStory))
                      (fn [kb fact]
                        (listing kb (v/dependent-justifications kb fact))))]
      (is (= 2 (count (first readings)))
          "the fact is an antecedent of both firings")
      (is (apply = readings)
          "the dependents list in the order the rules happened to be written")
      (testing "and the conclusions are the two the rules draw"
        (is (= #{(list flies Robin) (list nests Robin)}
               (into #{} (map (comp first :conclusion)) (first readings))))))))

;; ---- supporting-justifications ------------------------------------------

(deftest supporting-justifications-orders-two-rules-by-what-they-say
  ;; Two rules concluding one fact.  The two justifications differ in their **informant**
  ;; before they differ in anything else, and an informant is a rule handle — so a key
  ;; that admitted the handle would decide the whole comparison on which rule was typed
  ;; first, on the call whose docstring promises content order.
  (tu/with-terms [bird feathered flies Robin CxStory]
    (let [bird-rule (fwd [(list bird '?x)] (list flies '?x))
          plum-rule (fwd [(list feathered '?x)] (list flies '?x))
          readings  (both-orders
                     [[bird-rule plum-rule] [plum-rule bird-rule]]
                     (fn [kb rules]
                       (doseq [r rules] (v/assert kb r CxStory))
                       (v/assert kb (list bird Robin) CxStory)
                       (v/assert kb (list feathered Robin) CxStory)
                       (v/handle-of kb (list flies Robin) CxStory))
                     (fn [kb concl]
                       (listing kb (v/supporting-justifications kb concl))))]
      (is (= 2 (count (first readings)))
          "one conclusion, two independent derivations of it")
      (is (apply = readings)
          "the derivations list in the order their rules were written"))))

;; ---- the antecedent vector inside one justification ---------------------

(deftest why-names-a-firings-antecedents-in-the-same-order-either-way
  ;; A two-antecedent rule is triggered by whichever of its facts arrives second, and the
  ;; trigger seeds the firing's handle vector (`chain/complete-antecedents`).  So the
  ;; stored antecedents read `[b2 b1 rule]` one way round and `[b1 b2 rule]` the other,
  ;; and `why`'s `:because` — a caller's proof tree — printed the two facts in whichever
  ;; order they were typed.
  (tu/with-terms [linksTo leadsTo reaches A B C CxStory]
    (let [f1       (list linksTo A B)
          f2       (list leadsTo B C)
          readings (both-orders
                    [[f1 f2] [f2 f1]]
                    (fn [kb facts]
                      (v/assert-rule kb [(list linksTo '?a '?m) (list leadsTo '?m '?b)]
                                     (list reaches '?a '?b) CxStory
                                     {:direction :forward})
                      (doseq [f facts] (v/assert kb f CxStory))
                      (v/handle-of kb (list reaches A C) CxStory))
                    (fn [kb concl] [(proof (v/why kb concl))
                                    (mapv #(mapv (fn [h] (said kb h)) (:antecedents %))
                                          (v/supporting-justifications kb concl))]))]
      (is (= (vec (sort nm/compare-form [f1 f2]))
             (mapv :sentence (:because (first (:support (first (first readings)))))))
          "the join's two facts, in the order they say rather than the order they came")
      (is (apply = readings)
          "the proof tree reads the same whichever fact triggered the firing")
      (testing "and the rule handle is ordered among them rather than pinned"
        (is (= 3 (count (first (second (first readings)))))
            "two facts and the rule that joined them")))))

;; ---- what the order costs ------------------------------------------------

(deftest a-listing-builds-its-content-key-once-per-justification
  ;; The order every test above demands is bought with `kb/justification-content-key`,
  ;; and one build is a `get-sentex` per antecedent plus the structural key it assembles.
  ;; `sort-by` calls its key fn from *inside* the comparator, so the price was about
  ;; 2·n·log₂n builds where n would do — and a rule handle is an antecedent of every
  ;; justification it licenses, so `dependent-justifications` on one lists that rule's
  ;; whole firing history and pays the multiple on all of it.  Counting the builds is the
  ;; only witness there can be: the answer was already right, only dear.
  (tu/with-terms [birdZ fliesZ CxStory]
    (tu/with-cleared-kb [kb tu/fresh]
      (let [robins (vec (repeatedly 24 #(tu/tmp-ind "Robin")))]
        (v/assert kb (fwd [(list birdZ '?x)] (list fliesZ '?x)) CxStory)
        (doseq [r robins] (v/assert kb (list birdZ r) CxStory))
        (let [concl (v/handle-of kb (list fliesZ (first robins)) CxStory)
              rule  (:informant (first (v/supporting-justifications kb concl)))
              count-keys
              (fn [f]
                (let [calls (atom 0)
                      build kb/justification-content-key]
                  (with-redefs [kb/justification-content-key
                                (fn [kb] (let [k (build kb)]
                                           (fn [j] (swap! calls inc) (k j))))]
                    [(f) @calls])))]
          (is (integer? rule) "the firing names the rule it fired, and by handle")
          (let [[js calls] (count-keys #(v/dependent-justifications kb rule))]
            (is (= (count robins) (count js))
                "the rule's dependents are its firings, one per fact")
            (is (= (count js) calls)
                "and the listing built one key per justification, not one per comparison"))
          (testing "the key it built is still the one the order is in"
            (let [k  (kb/justification-content-key kb)
                  ks (mapv k (v/dependent-justifications kb rule))]
              (is (= ks (vec (sort nm/compare-form ks)))
                  "non-decreasing in the content key")))
          (testing "the supports listing shares the sort, and skips it below two"
            ;; A derived fact usually rests on **one** justification, and there is no
            ;; order to impose on a singleton — so `in-content-order` short-circuits
            ;; below two and builds no key at all.  This is the hop a proof walk (`why`,
            ;; w10 retrieval) makes on every step, and the content key — a `get-sentex`
            ;; per antecedent — was pure overhead there.
            (let [[js calls] (count-keys #(v/supporting-justifications kb concl))]
              (is (= 1 (count js)))
              (is (zero? calls)
                  "a singleton listing builds no key — nothing to order"))))))))

(deftest a-functional-merge-names-its-two-facts-in-the-same-order-either-way
  ;; The other side of the same defect, off the derivation path: a `functional` merge is
  ;; justified by [the arriving fact, the standing fact, the declaration], and which
  ;; fact is "arriving" is the order they were written in.  The merged sentence itself
  ;; was already content-ordered; the antecedents behind it were not.
  (tu/with-terms [motherOf Tom CxFam]
    (let [[lo hi]  (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])
          f1       (list motherOf Tom lo)
          f2       (list motherOf Tom hi)
          readings (both-orders
                    [[f1 f2] [f2 f1]]
                    (fn [kb facts]
                      (v/assert kb (list 'functional motherOf) CxFam)
                      (doseq [f facts] (v/assert kb f CxFam))
                      (v/handle-of kb (list 'equals lo hi) CxFam))
                    (fn [kb eq]
                      [(some? eq) (listing kb (v/supporting-justifications kb eq))]))]
      (is (= [true true] (mapv first readings))
          "both orders derive the equality")
      (is (apply = readings)
          "the merge names its two facts and the declaration in one order"))))

;; ---- why-not's excepted argument ----------------------------------------

(deftest why-not-blames-the-same-excepted-rule-in-either-order
  ;; A blocked conclusion is never stored, so `why-not`'s sentence arity reconstructs the
  ;; firing backwards.  Two excepted rules can conclude one goal, and the rules are read
  ;; off `rules/direct-concluders` — the rule index's own set, which is handle order.  So
  ;; the reported `:rule` and `:exception` are a content choice or they are a fact about
  ;; which rule was written first.  Read back as **content**: the reported handles differ
  ;; between two loads for the one reason that is not the subject.
  (tu/with-terms [bird flies penguin injured Opus CxStory]
    (let [r1       (fwd [(list bird '?x)] (list flies '?x))
          r2       (fwd [(list penguin '?x)] (list flies '?x))
          readings (both-orders
                    [[r1 r2] [r2 r1]]
                    (fn [kb rules]
                      ;; the rules go in in the ordering's order, but each keeps its OWN
                      ;; exception — so the two arms hold one body of knowledge and differ
                      ;; in nothing but arrival.  Both exceptions hold of Opus, so both
                      ;; completions are candidates and something has to choose.
                      (let [h (into {} (map (fn [r] [r (first (flatten [(v/assert kb r CxStory)]))]))
                                    rules)]
                        (v/assert kb (list 'exceptWhen (list penguin '?x)
                                           (list 'sentexHandle (h r1)))
                                  CxStory)
                        (v/assert kb (list 'exceptWhen (list injured '?x)
                                           (list 'sentexHandle (h r2)))
                                  CxStory)
                        (v/assert kb (list bird Opus) CxStory)
                        (v/assert kb (list penguin Opus) CxStory)
                        (v/assert kb (list injured Opus) CxStory)))
                    (fn [kb _]
                      (let [reading (fn []
                                      (let [w (v/why-not kb (list flies Opus) CxStory)]
                                        [(:reason w)
                                         (:exception w)
                                         ;; the rule as its sentence, never as its handle
                                         (some-> (:rule w) (->> (v/sentex kb)) v/readable-sentence)
                                         (mapv #(said kb %) (:via w))]))]
                        ;; the second reading is taken under a caller's print bounds —
                        ;; the REPL's, typically.  Both rules render as
                        ;; `(implies (and ...) ...)` at length 2, so a printed key would
                        ;; collapse and drop the choice onto the rule index's own order
                        [(reading)
                         (binding [*print-length* 2 *print-level* 2] (reading))])))]
      (is (= :excepted (ffirst (first readings)))
          "the goal is blocked rather than merely unsupported")
      (doseq [[i arm] (map-indexed vector readings)]
        (is (apply = arm)
            (str "arm " i ": the key is structural, so an ambient *print-length* moves nothing")))
      (is (apply = readings)
          "and the completion blamed is the content-least one, in either arrival order"))))

;; ---- the one ordering key in this family that is read off the source ----

(deftest a-clash-reports-sides-are-keyed-on-content-alone
  ;; `clash-report` orders a report's two sides by `[sentence context]`, and those two
  ;; keys are **total**: sentence-plus-context is what identifies a sentex, so two sides
  ;; agreeing on both are one canonical sentex and one handle — not a pair at all. A third
  ;; key could therefore only ever be dead weight that reads as assertion order, on a
  ;; public reading (`contradictions`, `conflicts`).
  ;;
  ;; A scan rather than a behavioural arm, for `sort_by_content_key_test`'s reason: the
  ;; unreachable tie-break is invisible to every reading, so only the source says whether
  ;; it is there.
  (let [line (->> (str/split-lines (slurp "src/vaelii/impl/settle.clj"))
                  (filter #(str/includes? % "(sort-by (juxt :sentence :context"))
                  first)]
    (is (some? line) "clash-report still orders its sides by a juxt of content keys")
    (is (not (str/includes? line ":handle"))
        (str "a handle is in the side-ordering key, which is arrival order: " line))))

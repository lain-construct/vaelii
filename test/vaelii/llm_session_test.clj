;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.llm-session-test
  "The turn loop's failure modes: `vaelii.impl.llm.session` where the answer is *not* the
  one the happy path assumes.

  Three things a proposal must never do, one test group each.  It must not read a turn the
  host **cut at the token limit** as a finished one — on the selection path a missing row
  is a proposed retraction, so a transport artifact would reach a reviewer as a deliberate
  deletion.  It must not tell a reviewer a **sampled page** is the whole of what is stored.
  And it must not let a model's malformed answer **escape the loop** as an exception, which
  a deeply nested form does through an `Exception` catch.

  Plus the write step: `apply-proposal!` over a batch `vaelii.core/edit!` throws part-way
  through, which is a state the critic cannot rule out and the caller has to be told about.

  Everything here runs **offline against the stub** — no host, no model, no socket."
  (:require [clojure.edn :as edn]
            [clojure.string :as str]
            [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.core-context :as core-context]
            [vaelii.impl.llm.session :as session]
            [vaelii.impl.llm.stub :as stub]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh #(doto (tu/fresh) (core-context/load-into))))

;; ---- a small world, and answers a host cut off --------------------------

(defn- world
  "Two facts under fresh temporary terms, and the handles a test selects on.  Call it
  **once** per test — every call invents new terms."
  [kb]
  (let [dog  (tu/fresh-term :type :dog)
        cat  (tu/fresh-term :type :cat)
        muffet (tu/fresh-term :individual :Muffet)
        tom  (tu/fresh-term :individual :Tom)
        ctx  (tu/fresh-term :context :Story)]
    (v/assert kb (list 'genlCx ctx 'CxCore) 'CxUniverse)
    {:dog dog :cat cat :Muffet muffet :Tom tom :ctx ctx
     :h-dog (v/assert kb (list dog muffet) ctx)
     :h-cat (v/assert kb (list cat tom) ctx)}))

(defn- answer
  "A stub turn carrying `text` and stopping for `reason` — the shape a host hands back
  when it stopped generating for its own reasons rather than the model's."
  [reason text]
  {:stop-reason reason :model "vaelii-stub"
   :content [{:type :text :text text}] :usage {}})

;; ---- a cut-off turn is not a proposal -----------------------------------

(tu/deftest-kb a-truncated-selection-turn-is-reported-not-diffed
  ;; The finding this pins: `diff-batch` reads absence as intent, so a line set the host
  ;; cut in half proposes retracting the rows the model never reached.
  (let [{:keys [dog Muffet ctx h-dog h-cat]} (world kb)
        half (stub/lines-text [[(list dog Muffet) ctx]])   ; the first of the two selected
        cut  (stub/provider {:script [(answer "max_tokens" half)]})
        r    (session/propose-edit kb {:handles [h-dog h-cat] :message "be specific"
                                       :provider cut})]
    (is (= :truncated (:status r)))
    (is (= "max_tokens" (:stop-reason r)))
    (testing "and nothing was diffed — a prefix of a line set is not a proposal"
      (is (nil? (:batch r)))
      (is (nil? (:lines r)))
      (is (nil? (:summary r))))
    (testing "the turn is not repaired either: the model ran out of room, not out of skill"
      (is (= 1 (:turns r))))
    (testing "what it was shown is still reported, so a caller can re-ask with more room"
      (is (= 2 (count (:selection r)))))
    (testing "the very same text, finished, is the deletion this status exists to stop"
      (let [whole (stub/provider {:script [(answer "end_turn" half)]})
            r'    (session/propose-edit kb {:handles [h-dog h-cat] :message "be specific"
                                            :provider whole})]
        (is (= :ok (:status r')))
        (is (= [h-cat] (:remove (:batch r')))
            "read as a finished answer, the row that never arrived is retracted")))))

(tu/deftest-kb a-truncated-batch-turn-is-its-own-status
  (tu/with-terms [dog Muffet]
    (let [batch {:add [[(list dog Muffet) 'CxUniverse]] :remove [12345]}
          p (stub/provider {:script [(answer "max_tokens" (stub/batch-text batch))]})
          r (session/propose kb {:message "add Muffet" :provider p})]
      (is (= :truncated (:status r)))
      (is (nil? (:batch r)) "a batch out of a cut-off answer is a prefix of one")
      (is (= 1 (:turns r)) "and re-asking it would return the same prefix"))))

(tu/deftest-kb a-truncated-page-turn-keeps-its-assertions-and-says-it-was-cut
  ;; The page path only adds, so a short answer costs assertions rather than proposing a
  ;; retraction — the batch stands and the flag says it is a prefix.
  (tu/with-terms [a_penguin a_bird]
    (v/assert kb (list 'genl a_penguin a_bird) 'CxUniverse)
    (let [text (stub/assertions-text [(list 'genl a_penguin 'thing)])
          cut  (stub/provider {:script [(answer "max_tokens" text)]})
          r    (session/propose-page kb {:term a_penguin :context 'CxUniverse
                                         :provider cut :message "flesh it out"})]
      (is (= :ok (:status r)))
      (is (true? (:answer-truncated? r)))
      (is (= 1 (count (:add (:batch r)))) "what did arrive is still applicable"))
    (testing "and a whole turn says so too"
      (let [whole (stub/provider {:script [{:assertions [(list 'genl a_penguin 'thing)]}]})
            r     (session/propose-page kb {:term a_penguin :context 'CxUniverse
                                            :provider whole :message "flesh it out"})]
        (is (false? (:answer-truncated? r)))))))

;; ---- a sampled page says so to the caller, not only to the model --------

(tu/deftest-kb a-page-proposal-carries-the-sample-flags-the-prompt-heading-carries
  ;; `page/stored-lines` reports the cut as **metadata**, and the `select-keys` that
  ;; builds `:page` drops it — so the model is told it was shown a sample and, without
  ;; this, the reviewer reading the same 40 lines is not.
  (tu/with-terms [a_penguin likes]
    (doseq [who (repeatedly 12 #(tu/fresh-term :individual :Who))]
      (v/assert kb (list likes who a_penguin) 'CxUniverse))
    (let [p (stub/provider {:script [{:assertions [(list 'genl a_penguin 'thing)]}]})
          page-proposal (fn [popts]
                          (session/propose-page kb {:term a_penguin :context 'CxUniverse
                                                    :provider p :message "flesh it out"
                                                    :prompt-opts popts}))]
      (testing "cut by the line cap: how many there were, and the shown rows are fewer"
        (let [r (page-proposal {:max-lines 4})]
          (is (= 4 (count (:page r))))
          (is (> (:page-found r) 4) "the page is a sample, and the count says of what")
          (is (false? (:page-truncated? r)) "the scan saw all of them, so the count is exact")))
      (testing "cut by the scan bound too: the count found is a floor, and says so"
        (let [r (page-proposal {:max-lines 4 :max-scan 6})]
          (is (true? (:page-truncated? r)))
          (is (<= (:page-found r) 6))))
      (testing "shown whole, nothing claims otherwise"
        (let [r (page-proposal {:max-lines 1000})]
          (is (= (count (:page r)) (:page-found r)))
          (is (false? (:page-truncated? r))))))))

;; ---- untrusted EDN cannot leave through the stack ----------------------

(def ^:private deep-nesting
  "A form nested past what the reader's recursion has stack for.  Depth rather than size
  is what does it: `clojure.edn/read-string` descends one frame or more per level, so a
  form no larger than a paragraph of prose overflows where a megabyte of flat text does
  not — which is why length caps are not the answer and a `Throwable` catch is."
  400000)

(def ^:private deep-open (str/join (repeat deep-nesting "(")))
(def ^:private deep-form (str deep-open (str/join (repeat deep-nesting ")"))))

(tu/deftest-kb a-deeply-nested-answer-is-a-rejection-not-a-stack-overflow
  (testing "the premise: the reader itself does not survive the form"
    (is (thrown? Throwable (edn/read-string deep-open))))

  (testing "the whole-KB path answers with an error"
    (let [{:keys [error batch]} (session/parse-batch deep-open)]
      (is (some? error))
      (is (nil? batch) "and never an empty batch — a stack overflow carries no message,
                        and a nil marker would have read as a map with neither key"))
    (is (some? (:error (session/parse-batch deep-form)))))

  (testing "the selection path's lines, in both shapes it reads"
    (is (seq (:errors (session/parse-lines (str "[" deep-open)))))
    (is (seq (:errors (session/parse-lines
                       (str "{\"lines\": [{\"sentence\": \"" deep-open "\", \"context\": \"C\"}]}"))))))

  (testing "the page path's sentences"
    (is (nil? (session/read-sentence deep-open)))
    (is (seq (:errors (session/parse-assertions deep-open)))))

  (testing "the reading path's candidates"
    (is (seq (:errors (session/parse-candidates
                       (str "{\"candidates\": [{\"sentence\": \"" deep-open "\", \"segment\": 0}]}"))))))

  (testing "and end to end, it is a status rather than an exception out of the loop"
    (let [p (stub/provider {:script (repeat 3 (answer "end_turn" deep-open))})
          r (session/propose kb {:message "x" :provider p :max-repairs 1})]
      (is (= :unparseable (:status r))))))

;; ---- applying a batch the door refuses part-way through -----------------

(tu/deftest-kb a-batch-that-throws-part-way-is-settled-and-reported
  ;; `check-edit` grades each add against the KB **as it stands**, so two adds that are
  ;; jointly inconsistent both pass and the proposal is `:ok`.  `edit!` is not a
  ;; transaction, so the apply stores the first, throws on the second, and skips the
  ;; settle — which is the state this reports rather than raises.
  (tu/with-terms [a_dog a_cat Rex CxStory]
    (v/assert kb (list 'genlCx CxStory 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'disjoint a_dog a_cat) 'CxUniverse)
    (let [batch {:add [[(list a_dog Rex) CxStory]
                       [(list a_cat Rex) CxStory]]
                 :remove []}]
      (testing "the critic passes it — neither add contradicts the KB it was graded against"
        (is (empty? (session/check-batch kb batch))))
      (v/reset-settle-stats! kb)
      (let [r (session/apply-proposal! kb {:status :ok :batch batch})]
        (testing "what landed is reported instead of thrown"
          (is (= 1 (:applied r)))
          (is (= 1 (:failed-at r)))
          (is (nil? (:result r)))
          (is (= :disjoint (:type (:error r))))
          (is (instance? Throwable (:exception (:error r)))))
        (testing "and the store agrees with the count"
          (is (some? (v/handle-of kb (list a_dog Rex) CxStory)))
          (is (nil? (v/handle-of kb (list a_cat Rex) CxStory))))
        (testing "belief was settled by hand, which is what makes the prefix recoverable"
          (is (pos? (reduce + (vals (:histogram (v/settle-stats kb))))))
          (is (true? (v/in? kb (v/handle-of kb (list a_dog Rex) CxStory)))))))))

(tu/deftest-kb a-whole-batch-reports-the-same-shape-with-nothing-failed
  (tu/with-terms [a_dog Rex CxStory]
    (v/assert kb (list 'genlCx CxStory 'CxUniverse) 'CxUniverse)
    (let [batch {:add [[(list a_dog Rex) CxStory]] :remove []}
          r (session/apply-proposal! kb {:status :ok :batch batch})]
      (is (= 1 (:applied r)))
      (is (nil? (:failed-at r)))
      (is (nil? (:error r)))
      (is (= 1 (count (:added (:result r)))) "the edit result is still the whole of it")
      (is (some? (v/handle-of kb (list a_dog Rex) CxStory))))))

(tu/deftest-kb applying-still-refuses-a-proposal-the-critic-rejected
  ;; The precondition is a throw and stays one: nothing was written, so there is no
  ;; partial state to report and a caller that ignored the status must be stopped.
  (tu/with-terms [Muffet]
    (let [proposal {:status :invalid
                    :batch {:add [[(list 'BadFunctor Muffet) 'CxUniverse]] :remove []}}]
      (is (= :llm-not-applicable
             (try (session/apply-proposal! kb proposal)
                  (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))))))

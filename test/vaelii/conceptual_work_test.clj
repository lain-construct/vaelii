;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.conceptual-work-test
  "The content, carrier and claim vocabulary of CxTra: `conceptual_work` below
  `information`, `information_carrier` beside both tangible and intangible, `carries`
  from a carrier to its content, and `claims` from a content or a carrier to a sentex
  handle.  A carrier claims what its content claims, through the one forward rule over
  `carries` and `claims`.  A carrier's destruction concludes nothing about its content.
  Information claims nothing unless a `claims` sentence says so."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.sentex :as sx]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(def ^:private CPT 'CxTra)

(def ^:private kinds '[conceptual_work information_carrier information_or_carrier])

(defn- holds-ask  [s ctx]         (boolean (v/ask? tu/*kb* s ctx)))
(defn- holds-genl [sub super ctx] (boolean (v/genl? tu/*kb* sub super ctx)))
(defn- holds-isa  [x t ctx]       (boolean (v/isa? tu/*kb* x t ctx)))
(defn- has-claims [x ctx]         (boolean (seq (v/ask tu/*kb* (list 'claims x '?s) ctx))))
(defn- following? [p]             (boolean (v/has-prop? tu/*kb* :target-following p)))

(defn- desk!
  "A fresh context below CxWell and CxTra, the way a user's context opts in."
  [ctx]
  (v/assert tu/*kb* (list 'genlCx ctx 'CxWell) 'CxUniverse)
  (v/assert tu/*kb* (list 'genlCx ctx CPT) 'CxUniverse)
  ctx)

(defn- claimed!
  "Store `sentence` in `story`, a context the desk does not see, so the desk can name the
  sentence by handle without believing the sentence.  Returns the handle term."
  [story sentence]
  (v/assert tu/*kb* (list 'genlCx story 'CxUniverse) 'CxUniverse)
  (sx/sentex-handle (v/assert tu/*kb* sentence story)))

(tu/deftest-kb the-kinds-and-relations-are-declared-in-the-theory
  (doseq [k kinds]
    (is (= 1 (count (v/sentexes-matching kb (list 'comment k '?c) CPT)))
        (str k " carries one comment in the theory"))
    (is (seq (v/sentexes-matching kb (list 'positiveExampleComment k '?c) CPT))
        (str k " carries a positive example"))
    (is (seq (v/sentexes-matching kb (list 'negativeExampleComment k '?c) CPT))
        (str k " carries a negative example"))
    (is (holds-genl k 'thing CPT) (str k " reaches thing from the theory")))
  (doseq [p '[carries claims]]
    (is (holds-ask (list 'binary_predicate p) CPT) (str p " is binary in the theory"))
    (is (= 1 (count (v/sentexes-matching kb (list 'comment p '?c) CPT)))
        (str p " carries one comment in the theory")))
  (testing "a conceptual work is information, and information is the content, not the medium"
    (is (holds-genl 'conceptual_work 'information CPT))
    (is (holds-genl 'conceptual_work 'intangible CPT)))
  (testing "a carrier is neither tangible nor intangible by type"
    (is (not (holds-genl 'information_carrier 'tangible CPT)))
    (is (not (holds-genl 'information_carrier 'intangible CPT)))
    (is (= :orthogonal (v/subsumption-status tu/*kb* 'information_carrier 'tangible CPT)))
    (is (= :orthogonal (v/subsumption-status tu/*kb* 'information_carrier 'intangible CPT)))
    (is (= :orthogonal (v/subsumption-status tu/*kb* 'information_carrier 'information CPT))))
  (testing "claims admits content and carriers through the type over both"
    (is (holds-genl 'information 'information_or_carrier CPT))
    (is (holds-genl 'information_carrier 'information_or_carrier CPT))
    (is (holds-ask '(arg claims 1 information_or_carrier) CPT))
    (is (holds-ask '(arg carries 1 information_carrier) CPT))
    (is (holds-ask '(arg carries 2 information) CPT))
    (is (following? 'claims)))
  (testing "neither CxWell nor CxUniverse reads the vocabulary"
    (doseq [k kinds]
      (is (empty? (v/sentexes-matching kb (list 'comment k '?c) 'CxUniverse))))))

(tu/deftest-kb a-copy-claims-what-its-work-claims
  (tu/with-terms [CxDesk CxStory Article PaperCopy Moon madeOfCheese]
    (desk! CxDesk)
    (let [h (claimed! CxStory (list madeOfCheese Moon))]
      (tu/with-entailing
        (v/assert kb (list 'conceptual_work Article) CxDesk)
        (v/assert kb (list 'tangible PaperCopy) CxDesk)
        (v/assert kb (list 'carries PaperCopy Article) CxDesk)
        (v/assert kb (list 'claims Article h) CxDesk))
      (testing "the copy claims the sentence its work claims"
        (is (holds-ask (list 'claims PaperCopy h) CxDesk)))
      (testing "the desk does not believe the claimed sentence"
        (is (not (holds-ask (list madeOfCheese Moon) CxDesk))))
      (testing "the copy is a carrier and is not made content or a work by the rule"
        (is (holds-isa PaperCopy 'information_carrier CxDesk))
        (is (not (holds-isa PaperCopy 'information CxDesk)))
        (is (not (holds-isa PaperCopy 'conceptual_work CxDesk))))
      (testing "retracting the claimed sentence takes both claims with it"
        (v/retract! kb (second h))
        (is (not (holds-ask (list 'claims Article h) CxDesk)))
        (is (not (holds-ask (list 'claims PaperCopy h) CxDesk)))))))

(tu/deftest-kb a-tangible-and-an-intangible-carrier-are-both-accepted
  (tu/with-terms [CxDesk CxStory Article TextFile Chirp PaperCopy Moon madeOfCheese]
    (desk! CxDesk)
    (let [h (claimed! CxStory (list madeOfCheese Moon))]
      (tu/with-entailing
        (v/assert kb (list 'conceptual_work Article) CxDesk)
        (v/assert kb (list 'digital_artifact TextFile) CxDesk)
        (v/assert kb (list 'tangible PaperCopy) CxDesk)
        (v/assert kb (list 'event Chirp) CxDesk)
        (v/assert kb (list 'carries PaperCopy Article) CxDesk)
        (v/assert kb (list 'carries TextFile Article) CxDesk)
        (v/assert kb (list 'carries Chirp TextFile) CxDesk)
        (v/assert kb (list 'claims Article h) CxDesk))
      (testing "a tangible copy and an intangible chirp are both carriers"
        (is (holds-isa PaperCopy 'information_carrier CxDesk))
        (is (holds-isa Chirp 'information_carrier CxDesk))
        (is (holds-isa Chirp 'intangible CxDesk)))
      (testing "a file is content of the chirp and a carrier of the article"
        (is (holds-isa TextFile 'information CxDesk))
        (is (holds-isa TextFile 'information_carrier CxDesk)))
      (testing "the claim reaches the chirp through the file"
        (is (holds-ask (list 'claims TextFile h) CxDesk))
        (is (holds-ask (list 'claims Chirp h) CxDesk)))
      (testing "no clash is reported"
        (is (empty? (filter #(some #{Article TextFile Chirp PaperCopy}
                                   (flatten (map :sentence (:sides %))))
                            (concat (v/contradictions kb) (v/conflicts kb)))))))))

(tu/deftest-kb destroying-a-copy-does-not-destroy-the-work
  (tu/with-terms [CxDesk CxStory Article PaperCopy Burning Moon madeOfCheese]
    (desk! CxDesk)
    (let [h (claimed! CxStory (list madeOfCheese Moon))]
      (tu/with-entailing
        (v/assert kb (list 'conceptual_work Article) CxDesk)
        (v/assert kb (list 'tangible PaperCopy) CxDesk)
        (v/assert kb (list 'carries PaperCopy Article) CxDesk)
        (v/assert kb (list 'claims Article h) CxDesk)
        (v/assert kb (list 'event Burning) CxDesk)
        (v/assert kb (list 'destroyedInput Burning PaperCopy) CxDesk))
      (testing "the burned copy is a carrier of the work"
        (is (holds-isa PaperCopy 'information_carrier CxDesk)))
      (testing "the copy's end is bounded by the burning"
        (is (holds-ask (list 'instantNotAfter (list 'EndFn PaperCopy) (list 'EndFn Burning))
                       CxDesk)))
      (testing "nothing concludes the work destroyed or bounds its end"
        (is (not (holds-ask (list 'destroyedInput Burning Article) CxDesk)))
        (is (not (holds-ask (list 'instantNotAfter (list 'EndFn Article) (list 'EndFn Burning))
                            CxDesk))))
      (testing "the work still claims what it claimed"
        (is (holds-ask (list 'claims Article h) CxDesk))))))

(tu/deftest-kb dna-carries-information-and-claims-nothing
  (tu/with-terms [CxDesk DnaMolecules DnaContent Aliens Scram]
    (desk! CxDesk)
    (tu/with-entailing
      (v/assert kb (list 'tangible DnaMolecules) CxDesk)
      (v/assert kb (list 'carries DnaMolecules DnaContent) CxDesk)
      (v/assert kb (list 'carries Aliens Scram) CxDesk))
    (testing "the molecules are a carrier and their content is information"
      (is (holds-isa DnaMolecules 'information_carrier CxDesk))
      (is (holds-isa DnaContent 'information CxDesk))
      (is (not (holds-isa DnaContent 'conceptual_work CxDesk))))
    (testing "neither the content nor the carrier claims anything"
      (doseq [x [DnaContent DnaMolecules Scram Aliens]]
        (is (not (has-claims x CxDesk)) (str x " claims nothing"))))))

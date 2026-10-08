;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.social-extension-test
  "CxSocialExtension: nestingPartnerOf, chosenSiblingOf and the plurality terms,
  shipped as an opt-in extension of CxSocial below CxUniverse. CxWell does not
  see the theory, so the everyday contexts below CxWell derive none of it, and a
  user's own context opts in by placing itself under CxSocialExtension — which,
  placed under CxSocial, sees CxSocial's own relations too."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(def ^:private SOCX 'CxSocialExtension)

(defn- holds-ask  [s ctx]         (boolean (v/ask? tu/*kb* s ctx)))
(defn- holds-sees [k y]           (boolean (v/sees? tu/*kb* k y)))
(defn- holds-genl [sub super ctx] (boolean (v/genl? tu/*kb* sub super ctx)))

(tu/deftest-kb the-theory-is-opt-in-below-cxsocial
  (testing "the theory sees CxSocial, and through it CxUniverse"
    (is (holds-sees SOCX 'CxSocial))
    (is (holds-sees SOCX 'CxUniverse)))
  (testing "neither CxWell, CxSocial, nor the upper ontology sees the theory"
    (is (not (holds-sees 'CxWell SOCX)))
    (is (not (holds-sees 'CxSocial SOCX)))
    (is (not (holds-sees 'CxUniverse SOCX)))))

(tu/deftest-kb cxwell-concludes-none-of-the-extension
  (tu/with-terms [P1 P2 Unit]
    (v/assert kb (list 'human P1) 'CxWell)
    (v/assert kb (list 'human P2) 'CxWell)
    (v/assert kb (list 'romanticPartnerOf P1 P2) 'CxWell)
    (v/assert kb (list 'dwellsIn P1 Unit) 'CxWell)
    (v/assert kb (list 'dwellsIn P2 Unit) 'CxWell)
    (testing "CxSocial's own vocabulary still derives in CxWell"
      (is (holds-ask (list 'roommateOf P1 P2) 'CxWell)))
    (testing "the extension's nestingPartnerOf does not, though both antecedents hold"
      (is (not (holds-ask (list 'nestingPartnerOf P1 P2) 'CxWell))))))

(tu/deftest-kb a-user-context-under-the-extension-derives-nestingpartnerof
  (tu/with-terms [CxHome P1 P2 Unit]
    (v/assert kb (list 'genlCx CxHome 'CxWell) 'CxUniverse)
    (v/assert kb (list 'genlCx CxHome SOCX) 'CxUniverse)
    (v/assert kb (list 'human P1) CxHome)
    (v/assert kb (list 'human P2) CxHome)
    (v/assert kb (list 'romanticPartnerOf P1 P2) CxHome)
    (testing "romantic partners who are not yet roommates are not yet nesting partners (red)"
      (is (not (holds-ask (list 'nestingPartnerOf P1 P2) CxHome))))
    (v/assert kb (list 'dwellsIn P1 Unit) CxHome)
    (v/assert kb (list 'dwellsIn P2 Unit) CxHome)
    (testing "co-dwelling derives roommateOf, which with romanticPartnerOf derives nestingPartnerOf (green)"
      (is (holds-ask (list 'roommateOf P1 P2) CxHome))
      (is (holds-ask (list 'nestingPartnerOf P1 P2) CxHome)))
    (testing "a context that does not see the extension still concludes none of it"
      (doseq [ctx ['CxWell 'CxSocial 'CxUniverse]]
        (is (not (holds-ask (list 'nestingPartnerOf P1 P2) ctx)) (str "nestingPartnerOf in " ctx))))))

(tu/deftest-kb chosensiblingof-carries-no-genl-edge
  ;; No genl edge to relativeOf: both are CxSocial's own middle-spindle terms, and a
  ;; term two middle members touch must sit at or above the spindle's head
  ;; (starter_test/a-term-two-spindle-members-touch-is-defined-in-the-head).
  (is (not (holds-genl 'chosenSiblingOf 'relativeOf SOCX)))
  (is (not (holds-genl 'chosenSiblingOf 'siblingOf SOCX)))
  (is (not (holds-genl 'siblingOf 'chosenSiblingOf SOCX))))

(tu/deftest-kb headmateof-is-read-from-shared-alterof-and-not-knows
  (tu/with-terms [CxMind Sys A1 A2]
    (v/assert kb (list 'genlCx CxMind 'CxWell) 'CxUniverse)
    (v/assert kb (list 'genlCx CxMind SOCX) 'CxUniverse)
    (v/assert kb (list 'plural_system Sys) CxMind)
    (v/assert kb (list 'alter A1) CxMind)
    (v/assert kb (list 'alter A2) CxMind)
    (v/assert kb (list 'alterOf A1 Sys) CxMind)
    (testing "one alter of the system alone derives no headmateOf (red)"
      (is (not (holds-ask (list 'headmateOf A1 A2) CxMind))))
    (v/assert kb (list 'alterOf A2 Sys) CxMind)
    (testing "two different alters of the same system derive headmateOf (green)"
      (is (holds-ask (list 'headmateOf A1 A2) CxMind))
      (is (not (holds-ask (list 'knows A1 A2) CxMind))
          "headmateOf does not genl knows"))))

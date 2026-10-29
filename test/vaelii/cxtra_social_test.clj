;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.cxtra-social-test
  "The relationship and plural-identity vocabulary of CxTra: nestingPartnerOf,
  chosenSiblingOf, founderOf and the plurality terms, each narrower than a CxSocial
  relation.  CxTra sees CxSocial as well as CxUniverse, and CxWell does not see CxTra,
  so the everyday contexts below CxWell derive none of it, and a user's own context
  opts in by placing itself under CxTra, which carries CxSocial's own relations to it."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(def ^:private SOCX 'CxTra)


(tu/deftest-kb cxtra-is-opt-in-and-sees-cxsocial
  (testing "the theory sees CxSocial, and through it CxUniverse"
    (is (tu/holds-sees SOCX 'CxSocial))
    (is (tu/holds-sees SOCX 'CxUniverse)))
  (testing "neither CxWell, CxSocial, nor the upper ontology sees the theory"
    (is (not (tu/holds-sees 'CxWell SOCX)))
    (is (not (tu/holds-sees 'CxSocial SOCX)))
    (is (not (tu/holds-sees 'CxUniverse SOCX)))))

(tu/deftest-kb cxwell-concludes-none-of-the-extension
  (tu/with-terms [P1 P2 Unit]
    (v/assert kb (list 'human P1) 'CxWell)
    (v/assert kb (list 'human P2) 'CxWell)
    (v/assert kb (list 'romanticPartnerOf P1 P2) 'CxWell)
    (v/assert kb (list 'dwellsIn P1 Unit) 'CxWell)
    (v/assert kb (list 'dwellsIn P2 Unit) 'CxWell)
    (testing "CxSocial's own vocabulary still derives in CxWell"
      (is (tu/holds-ask (list 'roommateOf P1 P2) 'CxWell)))
    (testing "the extension's nestingPartnerOf does not, though both antecedents hold"
      (is (not (tu/holds-ask (list 'nestingPartnerOf P1 P2) 'CxWell))))))

(tu/deftest-kb a-user-context-under-the-extension-derives-nestingpartnerof
  (tu/with-terms [CxHome P1 P2 Unit]
    (v/assert kb (list 'genlCx CxHome 'CxWell) 'CxUniverse)
    (v/assert kb (list 'genlCx CxHome SOCX) 'CxUniverse)
    (v/assert kb (list 'human P1) CxHome)
    (v/assert kb (list 'human P2) CxHome)
    (v/assert kb (list 'romanticPartnerOf P1 P2) CxHome)
    (testing "romantic partners who are not yet roommates are not yet nesting partners (red)"
      (is (not (tu/holds-ask (list 'nestingPartnerOf P1 P2) CxHome))))
    (v/assert kb (list 'dwellsIn P1 Unit) CxHome)
    (v/assert kb (list 'dwellsIn P2 Unit) CxHome)
    (testing "co-dwelling derives roommateOf, which with romanticPartnerOf derives nestingPartnerOf (green)"
      (is (tu/holds-ask (list 'roommateOf P1 P2) CxHome))
      (is (tu/holds-ask (list 'nestingPartnerOf P1 P2) CxHome)))
    (testing "a context that does not see the extension still concludes none of it"
      (doseq [ctx ['CxWell 'CxSocial 'CxUniverse]]
        (is (not (tu/holds-ask (list 'nestingPartnerOf P1 P2) ctx)) (str "nestingPartnerOf in " ctx))))))

(tu/deftest-kb each-relation-specializes-what-it-is-a-kind-of
  (doseq [[sub super] '[[chosenSiblingOf relativeOf]
                        [nestingPartnerOf romanticPartnerOf]
                        [nestingPartnerOf roommateOf]
                        [founderOf originatorOf]]]
    (is (tu/holds-genl sub super SOCX))
    (is (not (tu/holds-genl sub super 'CxSocial))))
  (is (not (tu/holds-genl 'chosenSiblingOf 'siblingOf SOCX)))
  (is (not (tu/holds-genl 'siblingOf 'chosenSiblingOf SOCX))))

(tu/deftest-kb a-user-context-under-the-extension-concludes-from-each-relation
  (tu/with-terms [CxHome P1 P2 P3 P4]
    (v/assert kb (list 'genlCx CxHome SOCX) 'CxUniverse)
    (doseq [p [P1 P2 P3 P4]] (v/assert kb (list 'human p) CxHome))
    (v/assert kb (list 'chosenSiblingOf P1 P2) CxHome)
    (v/assert kb (list 'nestingPartnerOf P3 P4) CxHome)
    (is (tu/holds-ask (list 'relativeOf P1 P2) CxHome))
    (is (tu/holds-ask (list 'knows P1 P2) CxHome))
    (is (not (tu/holds-ask (list 'siblingOf P1 P2) CxHome)))
    (is (tu/holds-ask (list 'romanticPartnerOf P3 P4) CxHome))
    (is (tu/holds-ask (list 'roommateOf P3 P4) CxHome))))

(tu/deftest-kb the-plurality-terms-are-separated-under-person
  (doseq [k '[singlet plural_system alter]]
    (is (= 1 (count (v/sentexes-matching kb (list 'comment k '?c) SOCX))) (str k))
    (is (tu/holds-genl k 'person SOCX) (str k))
    (is (not (tu/holds-genl k 'person 'CxSocial)) (str k)))
  (is (v/disjoint? kb 'singlet 'plural_system SOCX))
  (is (v/disjoint? kb 'alter 'singlet SOCX))
  (is (v/disjoint? kb 'alter 'plural_system SOCX)))

(tu/deftest-kb two-alters-of-one-system-are-headmates-and-need-not-know-each-other
  (tu/with-terms [CxHome Sys A1 A2 Other]
    (v/assert kb (list 'genlCx CxHome SOCX) 'CxUniverse)
    (v/assert kb (list 'plural_system Sys) CxHome)
    (doseq [a [A1 A2 Other]] (v/assert kb (list 'alter a) CxHome))
    (v/assert kb (list 'alterOf A1 Sys) CxHome)
    (v/assert kb (list 'alterOf A2 Sys) CxHome)
    (is (tu/holds-ask (list 'headmateOf A1 A2) CxHome))
    (is (tu/holds-ask (list 'headmateOf A2 A1) CxHome))
    (is (not (tu/holds-ask (list 'headmateOf A1 A1) CxHome)) "an alter is not its own headmate")
    (is (not (tu/holds-ask (list 'headmateOf A1 Other) CxHome)))
    (testing "headmates are not concluded to know each other"
      (is (not (tu/holds-ask (list 'knows A1 A2) CxHome))))
    (testing "a context that does not see the extension concludes none of it"
      (is (not (tu/holds-ask (list 'headmateOf A1 A2) 'CxSocial))))))

(tu/deftest-kb a-founder-is-an-originator
  (tu/with-terms [CxHome Maker Made]
    (v/assert kb (list 'genlCx CxHome SOCX) 'CxUniverse)
    (v/assert kb (list 'human Maker) CxHome)
    (v/assert kb (list 'person Made) CxHome)
    (v/assert kb (list 'founderOf Maker Made) CxHome)
    (is (tu/holds-ask (list 'originatorOf Maker Made) CxHome))
    (is (tu/holds-ask (list 'relativeOf Maker Made) CxHome))))

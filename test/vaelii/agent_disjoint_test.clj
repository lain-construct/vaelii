;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.agent-disjoint-test
  "What can act and what cannot.  agent is what can intentionally initiate an event.  Each
  test names a kind stated disjoint from agent, reads the disjointness from the contexts
  that see both, and asserts a probe of the kind held to be an agent, which clashes.  The
  control holds that a person, an animal, an organization and a polity are still agents
  and that the starter KB states no contradiction."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(defn- separated-from-agent
  "Assert that `kind` is disjoint from agent in each of `ctxs`, and that a probe of
  `kind` held to be an agent in `ctx` is stored in a clash."
  [kb kind ctxs ctx probe]
  (doseq [c ctxs]
    (is (true? (v/disjoint? kb 'agent kind c)) (str "agent and " kind " in " c)))
  (v/assert kb (list kind probe) ctx)
  (let [clash? (tu/stored-in-clash? kb (list 'agent probe) ctx)]
    (is clash? (str "a " kind " held to be an agent clashes"))))

(tu/deftest-kb a-situation-is-no-agent
  (tu/with-terms [Thaw]
    (separated-from-agent kb 'situation '[CxCore CxAbstract CxUniverse] 'CxUniverse Thaw)
    (is (true? (v/disjoint? kb 'agent 'event 'CxUniverse)) "an event is a situation")))

(tu/deftest-kb a-substance-is-no-agent
  (tu/with-terms [Brine]
    (separated-from-agent kb 'substance '[CxAbstract CxUniverse] 'CxUniverse Brine)
    (is (true? (v/disjoint? kb 'agent 'metal 'CxUniverse)) "a metal is a substance")))

(tu/deftest-kb a-plant-is-no-agent
  (tu/with-terms [Bramblewick]
    (separated-from-agent kb 'plant '[CxOrganism CxUniverse] 'CxUniverse Bramblewick)
    (is (true? (v/disjoint? kb 'agent 'tree 'CxUniverse)) "a tree is a plant")))

(tu/deftest-kb a-body-part-is-no-agent
  (tu/with-terms [Antler]
    (separated-from-agent kb 'body_part '[CxAbstract CxUniverse] 'CxUniverse Antler)
    (is (true? (v/disjoint? kb 'agent 'wing 'CxUniverse)) "a wing is a body part")))

(tu/deftest-kb what-can-act-is-still-an-agent
  (doseq [[k ctx] '[[person CxUniverse] [animal CxUniverse] [organization CxUniverse]
                    [human CxUniverse] [polity CxGeographyNow]]]
    (is (true? (v/genl? kb k 'agent ctx)) (str k " genl agent"))
    (is (not (v/disjoint? kb 'agent k ctx)) (str k " is not separated from agent")))
  (testing "a member of each is concluded an agent"
    (tu/with-terms [Ottoline Brannoc Guild ArdenmarkRealm]
      (doseq [[k t ctx] [['human Ottoline 'CxUniverse] ['animal Brannoc 'CxUniverse]
                         ['organization Guild 'CxUniverse]
                         ['polity ArdenmarkRealm 'CxGeographyNow]]]
        (v/assert kb (list k t) ctx)
        (is (true? (v/ask? kb (list 'agent t) ctx)) (str "a " k " is an agent")))))
  (is (empty? (v/contradictions kb)) "the starter KB states no contradiction"))

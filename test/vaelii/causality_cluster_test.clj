;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.causality-cluster-test
  "The situation/causality cluster: situation, static_situation, event (the
  state-of-affairs hierarchy under temporal_thing), causal/acausal (whether a thing
  can occupy a cause slot), and causal_event/acausal_event defined via `intersection`.
  The tests hold that the cluster loads and that the `intersection`-defined kinds get
  their genls and membership from the CxCore intersection rules."
  (:require [clojure.test :refer [is use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

(defn- believes?
  [kb sentence ctx]
  (boolean (seq (v/sentexes-matching kb sentence ctx))))

;; ---- the state-of-affairs hierarchy loads --------------------------------

(tu/deftest-kb situation-hierarchy-holds
  (is (v/ask? kb (list 'genl 'static_situation 'situation) 'CxUniverse)
      "static_situation is a situation")
  (is (v/ask? kb (list 'genl 'event 'situation) 'CxUniverse)
      "event is a situation")
  (is (v/ask? kb (list 'genl 'event 'temporal_thing) 'CxUniverse)
      "event is a temporal_thing (transitively, via situation)"))

;; ---- causal / acausal partition of thing ---------------------------------

(tu/deftest-kb causal-and-acausal-are-kinds-of-thing
  (is (v/ask? kb (list 'genl 'causal 'thing) 'CxUniverse) "causal is a kind of thing")
  (is (v/ask? kb (list 'genl 'acausal 'thing) 'CxUniverse) "acausal is a kind of thing"))

;; ---- causal_event / acausal_event get their genls from intersection ------

(tu/deftest-kb intersection-defined-events-derive-their-genls
  (is (v/ask? kb (list 'genl 'causal_event 'causal) 'CxUniverse)
      "the intersection rule makes causal_event a causal")
  (is (v/ask? kb (list 'genl 'causal_event 'event) 'CxUniverse)
      "the intersection rule makes causal_event an event")
  (is (v/ask? kb (list 'genl 'acausal_event 'acausal) 'CxUniverse)
      "the intersection rule makes acausal_event an acausal")
  (is (v/ask? kb (list 'genl 'acausal_event 'event) 'CxUniverse)
      "the intersection rule makes acausal_event an event"))

;; ---- membership: a causal event is a causal_event ------------------------

(tu/deftest-kb a-causal-event-instance-is-a-causal-event
  (tu/with-terms [Occurrence]
    (v/assert kb (list 'causal 'Occurrence) 'CxUniverse)
    (v/assert kb (list 'event 'Occurrence) 'CxUniverse)
    (is (believes? kb (list 'causal_event 'Occurrence) 'CxUniverse)
        "something both causal and an event is concluded a causal_event")))

(tu/deftest-kb an-acausal-non-event-is-not-a-causal-event
  (tu/with-terms [Record]
    (v/assert kb (list 'acausal 'Record) 'CxUniverse)
    (is (not (believes? kb (list 'causal_event 'Record) 'CxUniverse))
        "an acausal thing that is not an event is not a causal_event")))

;; ---- the divisions are declared disjoint ---------------------------------

(tu/deftest-kb causal-and-acausal-are-disjoint
  (is (v/disjoint? kb 'causal 'acausal 'CxUniverse)
      "a thing either can occupy a cause slot or cannot — the two sides do not overlap"))

(tu/deftest-kb a-situation-is-static-or-changing-but-not-both
  (is (v/disjoint? kb 'static_situation 'event 'CxUniverse)
      "the specialization axis of situation is a partition"))

(tu/deftest-kb causal-event-and-acausal-event-inherit-the-disjointness
  ;; causal_event genl causal and acausal_event genl acausal (from the intersection
  ;; rules), and causal is disjoint from acausal — so the two event kinds are disjoint by
  ;; the genl closure of disjointness, with no separate declaration.
  (is (= :disjoint (v/subsumption-status kb 'causal_event 'acausal_event))
      "disjointness reaches the intersection-defined kinds through their genls"))

(tu/deftest-kb a-single-thing-cannot-be-both-causal-and-acausal
  (tu/with-terms [Thing]
    (v/assert kb (list 'causal 'Thing) 'CxUniverse)
    (is (some? (v/handle-of kb (list 'causal 'Thing) 'CxUniverse)) "the first membership holds")
    (is (thrown? clojure.lang.ExceptionInfo
                 (v/assert kb (list 'acausal 'Thing) 'CxUniverse))
        "asserting the disjoint membership is refused as a contradiction")))

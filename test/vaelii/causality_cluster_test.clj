;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.causality-cluster-test
  "The situation/causality cluster: situation, static_situation, event (the
  state-of-affairs hierarchy under temporal), causal/acausal (whether a thing
  can occupy a cause slot), and causal_event/acausal_event defined via `intersection`.
  The tests hold that the cluster loads and that the `intersection`-defined kinds get
  their genls and membership from the CxCore intersection rules."
  (:require [clojure.test :refer [is testing use-fixtures]]
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
  (is (v/ask? kb (list 'genl 'event 'temporal) 'CxUniverse)
      "event is a temporal (transitively, via situation)"))

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
    (is (tu/stored-in-clash? kb (list 'acausal 'Thing) 'CxUniverse)
        "the disjoint membership is stored as a contradiction the settle weighs")))

;; ---- what has mass can be a cause ----------------------------------------

(tu/deftest-kb a-tangible-is-causal
  ;; the rock dented the car: anything with mass can fill a cause slot
  (is (v/ask? kb (list 'genl 'tangible 'causal) 'CxUniverse)
      "tangible is a kind of causal")
  (tu/with-terms [Rock]
    (v/assert kb (list 'stone 'Rock) 'CxUniverse)
    (is (v/ask? kb (list 'causal 'Rock) 'CxUniverse)
        "a rock, a tangible through stone and substance, reads causal")))

(tu/deftest-kb a-tangible-cannot-be-acausal
  ;; tangible below causal, and causal disjoint from acausal: the genl closure of
  ;; disjointness separates tangible from acausal with no separate declaration
  (is (v/disjoint? kb 'tangible 'acausal 'CxUniverse)
      "nothing with mass is acausal")
  (is (= :disjoint (v/subsumption-status kb 'tangible 'acausal))
      "the audit reads the pair disjoint"))

;; ---- a body of people can be a cause --------------------------------------

(tu/deftest-kb an-organization-is-causal
  ;; a company hires; a court rules
  (is (v/ask? kb (list 'genl 'organization 'causal) 'CxUniverse)
      "organization is a kind of causal")
  (tu/with-terms [Acme]
    (v/assert kb (list 'organization 'Acme) 'CxUniverse)
    (is (v/ask? kb (list 'causal 'Acme) 'CxUniverse)
        "an organization reads causal")))

;; ---- doneBy / performedBy: an event's doer --------------------------------
;; performedBy specializes doneBy through a predicate genl edge, so every performing is a
;; doing and not the other way round.  The doer position is typed `thing`: a machine or
;; a process can bring an event about as well as a person can.

(tu/deftest-kb done-by-and-performed-by-are-declared-binary-instance-relations
  (doseq [p '[doneBy performedBy]]
    (testing (str p)
      (is (v/ask? kb (list 'binary_predicate p) 'CxUniverse))
      (is (v/ask? kb (list 'instance_relation_predicate p) 'CxUniverse))
      (is (v/ask? kb (list 'arg p 1 'event) 'CxUniverse) "the first position is the event")
      (is (v/ask? kb (list 'arg p 2 'thing) 'CxUniverse) "and the doer is any thing")))
  (is (v/ask? kb '(genl performedBy doneBy) 'CxUniverse)
      "performedBy specializes doneBy"))

(tu/deftest-kb every-performing-is-a-doing
  (tu/with-terms [Launch Operator Spill Pump]
    (v/assert kb (list 'performedBy Launch Operator) 'CxUniverse)
    (is (v/ask? kb (list 'doneBy Launch Operator) 'CxUniverse)
        "the genl edge carries a performedBy tuple up to doneBy")
    (v/assert kb (list 'doneBy Spill Pump) 'CxUniverse)
    (is (not (v/ask? kb (list 'performedBy Spill Pump) 'CxUniverse))
        "and a doing is not concluded a performing")))

(tu/deftest-kb the-event-position-is-typed-and-the-doer-position-admits-any-thing
  (tu/with-terms [Stillness Flood Pump Drizzle]
    (v/assert kb (list 'static_situation Stillness) 'CxUniverse)
    (v/assert kb (list 'machine Pump) 'CxUniverse)
    (let [ps (v/check kb (list 'doneBy Stillness Pump) 'CxUniverse)
          p  (first (filter #(= :arg-type (:type %)) ps))]
      (is (some? p) "a static situation is not an event, so it cannot be done")
      (is (= 1 (:position p)))
      (is (= 'event (:expected p))))
    (testing "the constraint reaches performedBy through the genl edge"
      (is (some #(= :arg-type (:type %))
                (v/check kb (list 'performedBy Stillness Pump) 'CxUniverse))))
    (v/assert kb (list 'event Flood) 'CxUniverse)
    (is (= [] (v/check kb (list 'doneBy Flood Pump) 'CxUniverse))
        "a machine can do an event")
    (v/assert kb (list 'event Drizzle) 'CxUniverse)
    (is (= [] (v/check kb (list 'doneBy Flood Drizzle) 'CxUniverse))
        "and so can another event")))

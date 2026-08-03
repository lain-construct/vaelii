;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.world-narrative
  "A story-understanding ontology — test-world data below the shipped schema (see
  vaelii.world).  A schema of narrative concepts (agents, actions,
  events, goals) and the relations that connect them (wants, does, brings, achieves,
  causes, beforeEvent), annotated with metadata so the generic provers do more than
  the plain fables can:

    * causal reasoning — `causes` is transitive, so a chain of small causes is read
      as one cause (the flattery ultimately causes the fox to get the cheese);
    * temporal reasoning — `beforeEvent` is transitive, so events order themselves
      along the chain; a *direct* link also reads backwards via its inverse
      `afterEvent` (a transitively-derived order does not, since the inverse prover
      inverts stored facts only);
    * goal reasoning — an agent that wants a goal and brings about an event that
      achieves it is deduced to *achieve its goal* (a joined forward rule); an agent
      is *responsible for* what its action directly causes;
    * argIsa type inference — an untyped individual's role is inferred from the
      relation slot it fills (`CheeseFalls` is never typed, yet `ask?` finds it an
      event, because `causes` constrains both its arguments to be events).

  It is worked on one new story (the Fox and the Crow) and retrofitted onto an
  existing fable (the Tortoise and the Hare) to show the schema generalizes.  The
  schema lives in StoriesContext, seen by every fable."
  (:require [vaelii.core :as v]))

;; ---- the narrative schema -----------------------------------------------

(def type-hierarchy
  '[(genl agent        thing)
    (genl event        thing)
    (genl action       event)          ; an action is an event an agent performs
    (genl mental_state thing)
    (genl goal         mental_state)])

(def type-docs
  '[(comment agent        "A being that acts with intent — the doer of a story.")
    (comment event        "Something that happens in the story's world.")
    (comment action       "An event an agent deliberately performs.")
    (comment mental_state "An agent's inner state — a belief, a wish, a goal.")
    (comment goal         "A state of affairs an agent wants to bring about.")])

(def predicate-metadata
  ;; afterEvent is deliberately NOT declared transitive: it exists only to read a
  ;; direct beforeEvent link backwards (the inverse prover inverts stored facts), so
  ;; it has no base edges of its own for a transitive closure to compose.
  '[(transitive causes)                 ; a chain of causes is itself a cause
    (transitive beforeEvent)            ; temporal precedence composes
    (inverse    beforeEvent afterEvent)])

(def predicate-docs
  '[(comment wants         "(wants ?agent ?goal) means that ?agent desires ?goal.")
    (comment does          "(does ?agent ?action) means that ?agent performs ?action.")
    (comment brings        "(brings ?agent ?event) means that ?agent brings ?event about.")
    (comment achieves      "(achieves ?event ?goal) means that ?event realizes ?goal.")
    (comment causes        "(causes ?event1 ?event2) means that ?event1 brings ?event2 about. Transitive, so a chain of causes is itself a cause.")
    (comment beforeEvent   "(beforeEvent ?event1 ?event2) means that ?event1 happens before ?event2. Transitive, and the inverse of afterEvent.")
    (comment afterEvent    "(afterEvent ?event1 ?event2) means that ?event1 happens after ?event2. The inverse of beforeEvent, and deliberately not transitive: it has no base edges of its own, existing only to read a beforeEvent link backwards.")
    (comment achievesGoal  "(achievesGoal ?agent ?goal) means that ?agent got what it wanted. Derived, when the agent brings about an event that achieves the goal.")
    (comment responsibleFor "(responsibleFor ?agent ?event) means that ?agent's action directly caused ?event. Derived from does and causes.")])

(def predicate-constraints
  '[(argIsa wants   1 agent) (argIsa wants   2 goal)
    (argIsa does    1 agent) (argIsa does    2 action)
    (argIsa brings  1 agent) (argIsa brings  2 event)
    (argIsa achieves 1 event) (argIsa achieves 2 goal)
    (argIsa causes  1 event) (argIsa causes  2 event)
    (argIsa beforeEvent 1 event) (argIsa beforeEvent 2 event)
    (argIsa responsibleFor 1 agent) (argIsa responsibleFor 2 event)])

(def predicate-types
  '[(binaryPredicate wants)   (binaryPredicate does)        (binaryPredicate brings)
    (binaryPredicate achieves) (binaryPredicate causes)     (binaryPredicate beforeEvent)
    (binaryPredicate afterEvent) (binaryPredicate achievesGoal) (binaryPredicate responsibleFor)])

;; ---- worked story: the Fox and the Crow ---------------------------------

(def fox-and-crow
  "The fox flatters the crow; flattery makes the crow sing; singing drops the cheese;
  the fox gets it.  Types first (so the argIsa checks bind), then the facts."
  '[(agent FoxF) (agent CrowF)
    (goal HasCheese)
    (action Flatter1)
    (event CrowSings) (event FoxGetsCheese)      ; CheeseFalls is left untyped — its
                                                 ; eventhood is inferred from causes' argIsa
    (wants FoxF HasCheese)
    (does FoxF Flatter1)
    (causes Flatter1 CrowSings)          ; the causal chain, link by link
    (causes CrowSings CheeseFalls)
    (causes CheeseFalls FoxGetsCheese)
    (beforeEvent Flatter1 CrowSings)     ; the same links, temporally
    (beforeEvent CrowSings CheeseFalls)
    (beforeEvent CheeseFalls FoxGetsCheese)
    (brings FoxF FoxGetsCheese)
    (achieves FoxGetsCheese HasCheese)])

;; the Tortoise and the Hare, re-read with the same schema (its context already exists)
(def tortoise-goal
  '[(agent TortoiseA)
    (goal WinRace)
    (event TortoiseFinishes)
    (wants TortoiseA WinRace)
    (brings TortoiseA TortoiseFinishes)
    (achieves TortoiseFinishes WinRace)])

(defn- assert-all [kb ctx forms] (doseq [s forms] (v/assert kb s ctx)))

(defn load-into
  "Load the story-understanding ontology and its worked examples.  Requires the
  starter (and its stories) to be loaded first, so StoriesContext exists.  Returns kb."
  [kb]
  (v/assert kb '(genlContext FoxCrowContext StoriesContext) 'UniverseContext)
  (assert-all kb 'StoriesContext type-hierarchy)
  (assert-all kb 'StoriesContext type-docs)
  (assert-all kb 'StoriesContext predicate-metadata)
  (assert-all kb 'StoriesContext predicate-docs)
  (assert-all kb 'StoriesContext predicate-constraints)
  (assert-all kb 'StoriesContext predicate-types)
  (doseq [t '[agent event action mental_state goal]]     ; uphold the unaryPredicate invariant
    (v/assert kb (list 'unaryPredicate t) 'StoriesContext))
  ;; goal reasoning: wanting a goal + bringing about an event that achieves it ⇒ success
  (v/assert-rule kb '[(wants ?a ?g) (brings ?a ?e) (achieves ?e ?g)]
                 '(achievesGoal ?a ?g) 'StoriesContext)
  ;; agency: an agent is responsible for what its action directly causes
  (v/assert-rule kb '[(does ?a ?act) (causes ?act ?e)] '(responsibleFor ?a ?e) 'StoriesContext)
  (assert-all kb 'FoxCrowContext fox-and-crow)
  (v/assert kb '(comment FoxCrowContext
                         "The Fox and the Crow — moral: do not trust flatterers; the flattery serves the flatterer.")
            'StoriesContext)
  (assert-all kb 'TortoiseHareContext tortoise-goal)          ; the same schema on an existing fable
  kb)

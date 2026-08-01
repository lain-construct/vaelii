(ns vaelii.tsp-solve-test
  "Traveling salesman as a constraint solve — the grounding-rule → integrity-constraint
  path (`set/hardConstraint` + `do/label`) on a *permutation* problem instead of a
  colouring.

  A tour is an ordering of the cities into fixed positions `P1 … Pn` laid out in a
  cycle (`nextPos`, wrapping `Pn → P1`).  The choice is one tour position per city
  (`assumptionRule` head `(tourStop ?p ?c)`); three hard constraints turn the raw
  choices into a Hamiltonian tour:

    * **at-most-one city per position** — a `functional`-style clash over each fixed
      pair of cities sharing a position;
    * **at-least-one position per city** — a negated-choice constraint (`(not
      (tourStop P1 ?c)) … (not (tourStop Pn ?c))`), so every city is placed;
    * **no illegal step** — the tour may not move between two cities with no road: the
      constraint joins the road complement (`notRoad`) against the position choices at
      two consecutive slots (`nextPos`), a nogood over two *different* individuals that
      the direct-clash detectors cannot express.

  With `|cities| = |positions|`, at-most-one-per-position plus at-least-one-per-city
  forces an exact bijection (each city once, each position once), so a single
  `do/label … :sat` solve returns a valid Hamiltonian tour of the road graph — or
  UNSAT (nothing placed) when the graph has no Hamiltonian cycle.

  Enumeration needs an ASP backend, so the end-to-end tests are guarded on `asp?`."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.asp.solver :as solver]
            [vaelii.test-util :as tu]))

(def ^:private asp? (solver/available?))

;; ---- the road graphs -----------------------------------------------------
;; Five cities at five cyclic tour positions.  Roads are unordered pairs `#{a b}`.

(def ^:private cities    '[A B C D E])
(def ^:private positions '[P1 P2 P3 P4 P5])

;; A road graph that admits several Hamiltonian tours (the 5-cycle plus two chords).
(def ^:private roads
  #{#{'A 'B} #{'B 'C} #{'C 'D} #{'D 'E} #{'A 'E}   ; the outer 5-cycle
    #{'A 'C} #{'B 'D}})                             ; two chords → more than one tour

;; A 5-vertex path: a Hamiltonian *path* but no Hamiltonian *cycle* (no edge closes it).
(def ^:private path-roads
  #{#{'A 'B} #{'B 'C} #{'C 'D} #{'D 'E}})

;; ---- installing the program ----------------------------------------------

(defn- unordered-pairs [xs]
  (let [v (vec xs)]
    (for [i (range (count v)), j (range (inc i) (count v))] #{(v i) (v j)})))

(defn- cyclic-steps
  "Consecutive (Pa Pb) position pairs around the tour, wrapping the last back to the
  first — the slots the tour steps between."
  [positions]
  (map vector positions (concat (rest positions) [(first positions)])))

(defn- install-tsp!
  "The choice + permutation + no-illegal-step program over `cities` at `positions`
  (in cyclic order) for a `roads` graph, all in `ctx`."
  [kb ctx cities positions roads]
  (doseq [c cities] (v/assert kb (list 'city c) ctx {:strength :monotonic}))
  (doseq [p positions] (v/assert kb (list 'position p) ctx {:strength :monotonic}))
  (doseq [[a b] (cyclic-steps positions)]
    (v/assert kb (list 'nextPos a b) ctx {:strength :monotonic}))
  ;; the road complement, both directions — a step between them is forbidden
  (let [rset (set roads)]
    (doseq [pr (unordered-pairs cities)
            :when (not (rset pr))
            :let [[a b] (vec pr)]]
      (v/assert kb (list 'notRoad a b) ctx {:strength :monotonic})
      (v/assert kb (list 'notRoad b a) ctx {:strength :monotonic})))
  ;; choice: a tour position for each city (grounds |positions| × |cities| heads)
  (v/assert kb (list 'set/assumptionRule
                     (list 'implies (list 'and (list 'position '?p) (list 'city '?c))
                           (list 'tourStop '?p '?c)))
            ctx)
  ;; hard at-most-one city per position — one constraint per fixed city pair
  (doseq [pr (unordered-pairs cities) :let [[ca cb] (vec pr)]]
    (v/assert kb (list 'set/hardConstraint
                       (list 'implies (list 'and (list 'tourStop '?p ca) (list 'tourStop '?p cb))
                             (list 'twoCitiesAt '?p)))
              ctx))
  ;; hard at-least-one position per city — a negated-choice constraint over all positions
  (v/assert kb (list 'set/hardConstraint
                     (list 'implies
                           (apply list 'and (list 'city '?c)
                                  (map (fn [p] (list 'not (list 'tourStop p '?c))) positions))
                           (list 'unplaced '?c)))
            ctx)
  ;; hard no-illegal-step — consecutive tour slots must hold cities joined by a road
  (v/assert kb (list 'set/hardConstraint
                     (list 'implies
                           (list 'and (list 'nextPos '?pa '?pb) (list 'notRoad '?x '?y)
                                 (list 'tourStop '?pa '?x) (list 'tourStop '?pb '?y))
                           (list 'badStep '?x '?y)))
            ctx))

(defn- tour-of
  "position -> city, read from a `:sat` labeling's chosen-true `(tourStop pos city)` heads."
  [labeling]
  (into {} (map (fn [s] [(nth s 1) (nth s 2)])) (:true labeling)))

;; ---- a graph with a tour -------------------------------------------------

(deftest finds-a-hamiltonian-tour
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (install-tsp! kb 'TspContext cities positions roads)
      (let [r    (v/assert kb (list 'do/label 'TspContext 'TspPlanContext :sat) 'TspContext)
            lab  (first (:labelings r))
            tour (tour-of lab)]
        (testing ":sat returns one labeling and persists nothing"
          (is (= 1 (:count r)))
          (is (nil? (:context lab)))
          (is (not (contains? (set (v/contexts kb)) 'Tsp1Context))))
        (testing "the tour is a permutation: each position once, each city once"
          (is (= (set positions) (set (keys tour))))
          (is (= (set cities) (set (vals tour))) "every city visited exactly once")
          (is (= (count cities) (count (:true lab)))))
        (testing "every consecutive step of the tour follows a road"
          (doseq [[pa pb] (cyclic-steps positions)]
            (is (contains? roads #{(tour pa) (tour pb)})
                (str (tour pa) " -> " (tour pb) " must be a road"))))
        (testing "base belief is untouched — no tour position is believed"
          (is (empty? (v/sentexes-matching kb (list 'tourStop 'P1 'A) 'TspContext)))
          (is (zero? (count (v/contradictions kb)))))))))

;; ---- a graph with no tour ------------------------------------------------

(deftest a-path-graph-has-no-tour
  ;; A 5-vertex path has a Hamiltonian path but no Hamiltonian cycle: the cyclic tour
  ;; must return to its start and there is no road back.  The hard constraints make the
  ;; program UNSAT, so the solve places no city at all (like K4 leaving a node uncoloured).
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (install-tsp! kb 'NoTourContext cities positions path-roads)
      (let [r    (v/assert kb (list 'do/label 'NoTourContext 'NoTourPlanContext :sat) 'NoTourContext)
            tour (tour-of (first (:labelings r)))]
        (testing "no full permutation tour exists, and the all-hard UNSAT keeps nothing"
          (is (< (count tour) (count cities)))
          (is (empty? tour)))))))

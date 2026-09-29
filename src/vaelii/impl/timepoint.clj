;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.timepoint
  "The named points of a temporal thing, and the order the terms themselves fix among
  them — what the point network (`vaelii.impl.point`) adds to the instant facts it reads.

  Every temporal thing has six points, each a structural `unreifiable_function`
  application naming the thing it belongs to:

    (StartFn X)  (EndFn X)                        its start and end
    (EarliestStartFn X)  (LatestStartFn X)        where the start can fall
    (EarliestEndFn X)    (LatestEndFn X)          where the end can fall

  None of them is stored or minted.  A point becomes a node of the instant network when an
  instant fact or a goal mentions it, and a thing any of whose points is a node brings its
  start and end in with it, so a question about when a story's event ended is asked of
  the network even when nothing stated that end.

  `constraints-over` is the network's second reader (`qcn-kb`, `:over-nodes`): a function
  of the node set alone, answering the constraints the terms fix and nobody states.

  * **One thing's points.**  `ES ≤ S ≤ LS`, `EE ≤ E ≤ LE`, `S < E`, `ES ≤ EE` and
    `LS ≤ LE`, over whichever of them are nodes.  `S < E` gives every thing extent.
  * **A moment's points.**  An `(InstantFn …)` term and a point term name a moment, and
    each of a moment's six points is the moment itself.  The reader decides which
    arguments are moments by their spelling alone.  A symbol argument is a thing, even
    one a `time_point` membership calls a moment.  Dropping `S < E` when a membership
    arrived would loosen a pair, and a narrowing only narrows (docs/qcn.md).  So a symbol
    moment has no points, and stating that its start and end coincide with it is an
    inconsistency the network reports with those two facts as culprits.
  * **Calendar moments.**  An `(InstantFn …)` term, and a point of a calendar term — the
    start or end of `(YearFn 2008)` — is a moment the calendar places.  Those the network
    mentions are sorted by their fields and each is ordered against the next, so
    `(EndFn (YearFn 2008))` falls before `(InstantFn 2009 1 20 12 0 0)` with nothing
    stated.  A calendar term's bounds are sharp, so its earliest and latest start are its
    start, and likewise for its end.

  The constraints carry **no support**: what fixes them is the terms, and no retraction
  can move them.  An entailment that needs one of them still rests on the stated facts it
  also needed, which are the handles a justification names."
  (:require [clojure.set :as set]
            [vaelii.impl.datetime :as dt]
            [vaelii.impl.sentex :as sx]))

(def point-functions
  "Each point function, and which of a thing's bounds it names."
  '{StartFn         :start
    EndFn           :end
    EarliestStartFn :earliest-start
    LatestStartFn   :latest-start
    EarliestEndFn   :earliest-end
    LatestEndFn     :latest-end})

(defn- ground-term? [x]
  (if (sequential? x) (every? ground-term? x) (not (sx/variable? x))))

(defn point-term?
  "Is `x` a ground application of one of the six point functions?"
  [x]
  (and (seq? x) (= 2 (count x)) (contains? point-functions (first x))
       (ground-term? (second x))))

(defn node-term?
  "A term the point network takes as a node: an instant named by a symbol, a point of a
  thing, or a calendar moment."
  [x]
  (or (and (symbol? x) (not (sx/variable? x)))
      (point-term? x)
      (dt/instant-term? x)))

(defn thing-of
  "The thing a point term belongs to, or nil for any other term."
  [x]
  (when (point-term? x) (second x)))

(defn point
  "The term naming `which` point of `thing` — `:start`, `:end`, `:earliest-start` …"
  [which thing]
  (list (some (fn [[f w]] (when (= w which) f)) point-functions) thing))

(defn moment
  "The six calendar fields of the moment `x` names, or nil when the calendar does not
  place it: an `(InstantFn …)` term, or a point of a calendar term."
  [x]
  (or (dt/instant-fields x)
      (when-let [[s e] (some-> (thing-of x) dt/bounds)]
        (case (point-functions (first x))
          (:start :earliest-start :latest-start) s
          (:end :earliest-end :latest-end)       e))))

;; ---- the constraints the terms fix --------------------------------------

(def ^:private strict  [#{:before} #{:after}])
(def ^:private weak    [#{:before :equal} #{:after :equal}])
(def ^:private same    [#{:equal} #{:equal}])

(def ^:private universe #{:before :equal :after})

(defn- add-edge [net [a b [fwd bwd]]]
  (-> net
      (update [a b] (fnil set/intersection universe) fwd)
      (update [b a] (fnil set/intersection universe) bwd)))

(defn- thing-edges
  "The order among `x`'s points, over the ones in `present`."
  [x present]
  (let [[s e es ls ee le] (map #(point % x) [:start :end :earliest-start :latest-start
                                             :earliest-end :latest-end])]
    (cond-> [[s e strict]]
      (present es)                    (conj [es s weak])
      (present ls)                    (conj [s ls weak])
      (present ee)                    (conj [ee e weak])
      (present le)                    (conj [e le weak])
      (and (present es) (present ee)) (conj [es ee weak])
      (and (present ls) (present le)) (conj [ls le weak]))))

(defn- moment?
  "Does the term `x` name a moment by its spelling — an `(InstantFn …)` term or a point?"
  [x]
  (or (point-term? x) (dt/instant-term? x)))

(defn- moment-edges
  "Each point of the moment `m` in `present`, equal to `m`."
  [m present]
  (for [w (vals point-functions) :let [p (point w m)] :when (present p)] [p m same]))

(defn- calendar-edges
  "Each calendar moment in `present` ordered against the next one by its fields."
  [present]
  (->> (keep (fn [x] (when-let [m (moment x)] [m x])) present)
       (sort-by first)
       (partition 2 1)
       (map (fn [[[ma a] [mb b]]] [a b (if (= ma mb) same strict)]))))

(defn constraints-over
  "The constraints the point terms among `nodes` fix, as `{:net … :support {}}` in the
  point algebra's relations, or nil when they fix none.  Each thing any of whose points
  is a node brings its start and end in, and each moment any of whose points is a node
  brings itself in, transitively for a point of a point."
  [nodes]
  (let [nodes   (into (set nodes)
                      (mapcat #(take-while point-term? (iterate thing-of (thing-of %))))
                      nodes)
        {moments true things false}
        (group-by moment? (into #{} (comp (keep thing-of) (remove dt/bounds)) nodes))
        present (-> nodes
                    (into moments)
                    (into (mapcat #(vector (point :start %) (point :end %))) things))
        edges   (concat (mapcat #(thing-edges % present) things)
                        (mapcat #(moment-edges % present) moments)
                        (calendar-edges present))]
    (when (seq edges)
      {:net (reduce add-edge {} edges) :support {}})))

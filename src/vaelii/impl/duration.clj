;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.duration
  "Interval duration arithmetic — the quantitative half of `vaelii.impl.interval`, which
  is qualitative.  Allen's algebra says *that* two intervals overlap; this says *how
  long* for, in real units, and adds up the lengths of several.

  Two computed predicates, neither ever stored:

    (totalDuration (list I1 I2 …) D)   D is the sum of the components' lengths
    (overlapDuration I1 I2 D)          D is how long I1 and I2 overlap

  An interval's own duration is an ordinary stored fact, `(length I M)`, whose measure
  `M` is a NAUT — `(QuantityFn N Unit)` or `(QuantityIntervalFn Lo Hi Unit)`.  The index
  answers those; this prover only reads them, normalizes each through
  `provers/normalize-quantity` against the KB's `dimensionOf` / `conversionFactor` table,
  does the arithmetic on `[lo hi]` magnitude bounds, and renders the result back as a
  measure.

  **Bounds throughout, not points.** A stored length may itself be an interval measure,
  and an overlap is often only bounded rather than known, so every computation carries
  `[lo hi]` and the render decides the shape: `lo` and `hi` within tolerance give a point
  `(QuantityFn …)`, anything wider gives `(QuantityIntervalFn lo hi …)`.  That is what
  keeps the answer honest — an over-approximation renders as an interval and says so,
  rather than as a point that would claim more than the KB knows.

  **The result is rendered in the dimension's base unit**, which is read back out of the
  same `conversionFactor` table the normalization used — `(conversionFactor U Base F)`
  names the base, and a unit that declares no factor is its own base.  So no separate
  declaration says which unit to render in, and none can disagree with the one the
  arithmetic actually happened in.  Every unit of a dimension converts to a single base
  (the direct-to-base contract), so which component the base is read from cannot change
  the answer.  A caller who wants another unit asks the *check* form instead — a ground
  `D` is compared after normalization, so `(totalDuration (list A B) (QuantityFn 2.5
  Hour))` is answered whatever unit the components were stated in.

  **Bind or check**, like `EvaluateProver`: a variable `D` is bound to the rendered
  measure; a ground `D` succeeds iff it names the same dimension and the same bounds
  within `provers/*quantity-tolerance*`, the same epsilon policy the measure comparisons
  use.  A magnitude is snapped to that same grid before rendering, so cross-unit
  normalization's last-bit noise never reaches the answer.

  **The metric network sharpens an overlap when there is one.**  The qualitative relation
  set alone cannot say how much of a partial overlap is shared, so it falls back to the
  sound `[0, min(len1, len2)]`.  When `vaelii.impl.stp` has numeric bounds on both
  intervals' endpoints it computes a real one instead, and the two are *intersected*: both
  are sound, so the tighter of them is.  A KB stating no `temporalDistance` gets exactly the
  qualitative answer, unchanged.

  The prover is **opt-in** — register it with `vaelii.core/add-prover`.  It needs no
  other prover registered: `overlapDuration` reads the qualitative relation set straight
  off `interval/possible-allen-relations` and the metric bound straight off
  `stp/overlap-window`, both functions of the believed facts rather than queries.  See
  docs/duration.md."
  (:require [clojure.set :as set]
            [vaelii.impl.interval :as iv]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.stp :as stp]))

;; ---- measures in and out -------------------------------------------------

(defn- approx=
  "Are two base magnitudes equal within the measure tolerance?  Normalization multiplies
  by a stored (usually floating-point) conversion factor, so exact `=` would make one
  sum unequal to itself written in another unit."
  [a b]
  (<= (abs (- a b)) provers/*quantity-tolerance*))

(defn- emit
  "Bind or check the answer slot `d` against the computed `[lo hi]` bounds of `dim`.
  A variable takes the rendered measure; a ground measure is normalized and must agree on
  dimension and on both bounds within tolerance; anything else answers nothing."
  [kb context [dim unit] lo hi d]
  (cond
    (sx/variable? d) [{d (provers/render-quantity lo hi unit)}]
    (provers/measure? d) (let [[dim* lo* hi*] (provers/normalize-quantity kb d context)]
                           (if (and (= dim dim*) (approx= lo lo*) (approx= hi hi*)) [{}] []))
    :else []))

;; ---- reading an interval's own length ------------------------------------

(defn- interval-length
  "The believed length of interval `i` as `[[dimension base-unit] lo hi]`, or nil.

  Nil when the KB states no length for `i` — and also when it states two that *disagree*
  once normalized, which is a contradiction no arithmetic should paper over.  Duplicates
  agree and collapse, as do the same duration written in two units, so only a genuine
  disagreement bails; and because the set is built from normalized values rather than
  from stored terms, the verdict cannot depend on the order the facts were read in."
  [kb i context]
  (let [ls (into #{}
                 (keep (fn [m]
                         (let [measure (get (second m) '?m)]
                           (when (provers/measure? measure)
                             (let [[dim lo hi] (provers/normalize-quantity kb measure context)]
                               [[dim (provers/base-unit-of kb (last measure) context)]
                                (provers/round-magnitude lo) (provers/round-magnitude hi)])))))
                 (res/matches-visible kb (list 'length i '?m) context))]
    (when (= 1 (count ls)) (first ls))))

;; ---- the two computations ------------------------------------------------

(defn- list-form?
  "Is `x` the `(list I1 I2 …)` term `totalDuration` takes its components as?"
  [x]
  (and (sequential? x) (seq x) (= 'list (first x))))

(defn- interval-term? [x] (and (symbol? x) (not (sx/variable? x))))

(defn- sum-bounds
  "The summed `[lo hi]` of several normalized lengths, or nil when they do not all share
  one dimension.  The **unit-consistency gate**: magnitudes only add up once they are in
  one unit, so mixed dimensions are refused outright rather than summed into a number
  that means nothing."
  [lengths]
  (let [dims (set (map first lengths))]
    (when (= 1 (count dims))
      [(first dims) (reduce + (map second lengths)) (reduce + (map #(nth % 2) lengths))])))

(defn overlap-bounds
  "How long two intervals overlap, given the Allen relations still possible between them
  and each one's own `[lo hi]` length.  Four cases, and the qualitative vocabulary of
  `vaelii.impl.interval` names three of them, so the two cannot drift apart:

  * **`temporallyDisjoint`** — every possible relation puts them apart, so the overlap is
    exactly zero.
  * **`subintervalOf`** — every possible relation puts the first inside the second, so
    the overlap is the whole of the first.
  * **`hasSubinterval`** — the mirror.
  * otherwise the sound over-approximation **`[0, min(len1, len2)]`**: they may not
    overlap at all, and can overlap by no more than the shorter of them. This is what an
    unconstrained pair gets, and it renders as an interval rather than a point, so the
    answer says how little is known instead of claiming a figure.

  Nil for an empty relation set — that is an inconsistent network, which is not a pair of
  intervals whose overlap has a length."
  [rels [lo1 hi1] [lo2 hi2]]
  (cond
    (empty? rels)                                              nil
    (set/subset? rels (iv/interval-denotation 'temporallyDisjoint)) [0 0]
    (set/subset? rels (iv/interval-denotation 'subintervalOf))      [lo1 hi1]
    (set/subset? rels (iv/interval-denotation 'hasSubinterval))     [lo2 hi2]
    :else                                                      [0 (min hi1 hi2)]))

(defn- solve-total
  "`(totalDuration (list I1 I2 …) D)` — read every component's length, require one
  dimension, sum the bounds, bind or check."
  [kb goal context]
  (let [[_ components d] goal
        intervals (rest components)]
    (when (and (seq intervals) (every? interval-term? intervals))
      (let [lengths (map #(interval-length kb % context) intervals)]
        (when (every? some? lengths)
          (when-let [[dim lo hi] (sum-bounds lengths)]
            (emit kb context dim lo hi d)))))))

(defn- intersect-bounds
  "The tighter of two sound bounds on one quantity — `[max of the los, min of the his]`.

  Nil when they do not meet: two sound bounds with nothing in common means the KB says two
  incompatible things about the same overlap, and there is no number to report.  Bounds that
  cross by no more than the tolerance are float noise from two different routes to the same
  figure, and collapse to a point rather than a contradiction."
  [[lo1 hi1] [lo2 hi2]]
  (let [lo (max lo1 lo2), hi (min hi1 hi2)]
    (cond
      (<= lo hi)      [lo hi]
      (approx= lo hi) [hi hi]
      :else           nil)))

(defn- sharpen-overlap
  "Tighten a qualitative overlap bound with what the metric temporal network pins down about
  the two intervals' endpoints.

  The metric answer is used only when it is in the **same dimension and base unit** as the
  lengths, since the two magnitudes must be commensurable before they can be intersected.
  A KB with no `temporalDistance` constraints — or none reaching these two intervals, or
  none whose network is satisfiable — gets the qualitative bound back untouched, which is
  the whole of the compatibility guarantee: the metric layer can only ever narrow.  An
  unsatisfiable metric network is reported through `(violations kb)` where it is closed, and
  narrows nothing; the qualitative answer does not rest on it and so still stands."
  [kb context dim i1 i2 bounds]
  (if-let [[wdim wlo whi] (stp/overlap-window kb context i1 i2)]
    (if (= dim wdim) (intersect-bounds bounds [wlo whi]) bounds)
    bounds))

(defn- solve-overlap
  "`(overlapDuration I1 I2 D)` — read both lengths, read the qualitative relation set off the
  interval network, map the two to `[lo hi]`, sharpen with the metric network, bind or
  check."
  [kb goal context]
  (let [[_ i1 i2 d] goal]
    (when (and (interval-term? i1) (interval-term? i2))
      (let [[dim1 lo1 hi1] (interval-length kb i1 context)
            [dim2 lo2 hi2] (interval-length kb i2 context)]
        (when (and dim1 dim2 (= dim1 dim2))
          (when-let [bounds (overlap-bounds (iv/possible-allen-relations kb context i1 i2)
                                            [lo1 hi1] [lo2 hi2])]
            (when-let [[lo hi] (sharpen-overlap kb context dim1 i1 i2 bounds)]
              (emit kb context dim1 lo hi d))))))))

;; ---- the prover ----------------------------------------------------------

(defn- answer-slot?
  "Can `d` be the answer argument — a variable to bind, or a ground measure to check?"
  [d]
  (or (sx/variable? d) (provers/measure? d)))

(defrecord DurationProver []
  provers/Prover
  (applicable? [_ _ goal _]
    (and (sequential? goal) (seq goal)
         (case (first goal)
           totalDuration   (and (= 3 (count goal))
                                (list-form? (nth goal 1))
                                (answer-slot? (nth goal 2)))
           overlapDuration (and (= 4 (count goal))
                                (interval-term? (nth goal 1))
                                (interval-term? (nth goal 2))
                                (answer-slot? (nth goal 3)))
           false)))
  ;; A computation, so at most one answer — and the estimate must not cost what it
  ;; estimates, which here would be the length reads plus a path-consistency pass.
  (est-bindings [_ _ _ _] 1)
  ;; A handful of belief-filtered reads and some arithmetic — a computation, not a search.
  (cost         [_ _ _ _] :compute)
  ;; Authoritative over the lengths it reads: a duration is never a stored fact, so the
  ;; arithmetic holds every answer there is.
  (completeness [_ _ _ _] 100)
  (solve [_ kb goal context]
    (case (first goal)
      totalDuration   (solve-total kb goal context)
      overlapDuration (solve-overlap kb goal context)
      nil)))

(defn duration-prover
  "The interval-duration arithmetic prover, to register with `vaelii.core/add-prover`."
  []
  (->DurationProver))

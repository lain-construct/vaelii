;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.stp
  "A **simple temporal problem** — the metric half of time, where the qualitative calculi
  say only which of two things came first.  A constraint is a bound on the *gap* between
  two instants,

    lo ≤ t(Q) − t(P) ≤ hi

  and a set of them is closed by all-pairs shortest paths over the distance graph they
  describe.  The closure answers the tightest gap the constraints entail between *any* two
  instants, including pairs nobody wrote a constraint for, and a **negative cycle** in that
  graph is the proof that no assignment of times satisfies them all.

  This is not a relation algebra and it is deliberately not forced through
  `vaelii.impl.qcn`: there is no finite set of jointly-exhaustive base relations here, and
  no composition table — the constraint on a pair is an interval of the reals, composition
  is addition and tightening is `min`.  So it is its own small algorithm, written the way
  `qcn` is written: **pure data in, pure data out**, knowing nothing about a KB, with the
  KB reading and the prover in their own marked section below.

  **Constraints are measures**, not bare numbers.  A stated one is the ordinary fact
  `(temporalDistance P Q M)` where `M` is a `(QuantityFn N Unit)` for an exact separation or
  a `(QuantityIntervalFn Lo Hi Unit)` for a bounded one, and a negative magnitude says Q
  falls before P.  Every magnitude normalizes through `provers/normalize-quantity` against
  the KB's `dimensionOf` / `conversionFactor` table, so the arithmetic happens in the
  dimension's base unit and an answer is rendered back in that same unit — exactly the
  contract `vaelii.impl.duration` follows, so a separation and a duration are written the
  same way and compare directly.  Constraints spanning more than one dimension are refused
  rather than mixed.

  **Bind or check**, like `EvaluateProver` and the duration arithmetic: an open measure is
  bound to the tightest separation entailed, and a ground one is *entailed* exactly when the
  derived bound is contained in it — a stated bound is a weaker claim than the derived one,
  so the derived one implies it.

  **The bridge to the interval algebra** is `(startOf I P)` / `(endOf I P)`, which name an
  interval's two bounding instants.  With them a metric fact and an Allen relation are about
  the same thing, and `allen-narrowing` reads the closure back as constraints on the
  *interval* relations: if the closure puts A's end strictly before B's start then A is
  `before` B, and so on for all thirteen.  It narrows and never widens — it returns relation
  sets for a caller to intersect into an interval network, and mutates nothing.

  `vaelii.impl.duration` is the other consumer: `overlap-window` bounds how long two
  intervals overlap from their endpoints alone, which is what turns an indefinite overlap
  into a real figure.

  The prover is **opt-in**: register it with `vaelii.core/add-prover`, and until then a KB
  stores and retrieves `temporalDistance` facts as ordinary facts without paying for the
  closure.  The vocabulary ships in `kb/upper/CxTime.txt` either way.  See
  docs/stp.md."
  (:require [taoensso.trove :as trove]
            [vaelii.impl.caches :as caches]
            [vaelii.impl.interval :as iv]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]))

;; =========================================================================
;; THE ALGORITHM — pure data in, pure data out.  No KB, no context, no belief.
;; =========================================================================

;; A **network** is `{[p q] → [lo hi]}`, meaning `lo ≤ t(q) − t(p) ≤ hi`, both directions
;; stored (`[q p]` holds `[-hi -lo]`); an unrecorded pair is unbounded.  So a network is a
;; *value*, which is what lets a caller memoize an expensive closure on its content — the
;; same discipline `qcn` follows.

(def unbounded
  "The constraint on a pair nothing is known about: the whole real line."
  [##-Inf ##Inf])

(defn constraint
  "The bound on `t(q) − t(p)` in `net`: exactly zero on the diagonal, the recorded interval,
  else unbounded.  The diagonal answers zero *whatever* is recorded there, because the only
  gap between an instant and itself is none."
  [net p q]
  (if (= p q) [0 0] (get net [p q] unbounded)))

(defn nodes
  "Every instant named by a constraint in `net`."
  [net]
  (into #{} (mapcat identity) (keys net)))

(defn narrow
  "Intersect the constraint on `[p q]` with `[lo hi]`, writing the converse bound on
  `[q p]` with it.  Intersection is `[max of the los, min of the his]` — commutative and
  associative, so a network is a function of the constraints alone and never of the order
  they were read in."
  [net p q lo hi]
  (let [[lo0 hi0] (get net [p q] unbounded)
        lo* (max lo0 lo)
        hi* (min hi0 hi)]
    (assoc net [p q] [lo* hi*] [q p] [(- hi*) (- lo*)])))

(defn- unsatisfiable-as-given?
  "Is one recorded constraint unsatisfiable *before* any closure?  Two ways, and both are
  the metric echo of what `qcn/unsatisfiable-as-given?` refuses.

  Its bounds are **crossed** — `lo > hi` asks for a gap that is at once too large and too
  small.  The closure does catch this, as the negative cycle p→q→p, but only when both
  nodes are passed to it, and passing every node is the caller's obligation; checking here
  makes the verdict on a single self-contradicting fact independent of what else is present.

  Or it is a **diagonal** constraint excluding zero: a claim that an instant falls some
  non-zero time from itself.  No path ever runs from a node to itself in one step, and
  `constraint` answers zero on the diagonal whatever is recorded, so such a claim would
  otherwise be silently dropped rather than reported.

  Both read to the **tolerance**, and it is the same `provers/*quantity-tolerance*` a
  measure comparison is held to: a crossing narrower than the epsilon is two spellings of
  one figure, not a contradiction — see `close`."
  [[[p q] [lo hi]]]
  (let [eps provers/*quantity-tolerance*]
    (or (> lo (+ hi eps))
        (and (= p q) (not (and (<= lo eps) (>= hi (- eps))))))))

(defn unsatisfiable-pairs
  "The pairs of `net` that `unsatisfiable-as-given?` refuses — what a reader wrote down that
  no assignment of times can satisfy, before any closure.  Empty when the network is
  unsatisfiable only *derivably*, through a cycle, which is the case a report has no single
  pair to blame for."
  [net]
  (into #{} (keep (fn [[pair :as entry]]
                    (when (unsatisfiable-as-given? entry) pair)))
        net))

(defn- distance-graph
  "The network as a weighted digraph `{[p q] → w}`, `w` an upper bound on `t(q) − t(p)`.
  Only finite weights are edges: an unbounded side constrains nothing and is the absence of
  an edge, which is also what keeps infinities out of the arithmetic.  The diagonal is zero,
  so a self-distance that ends up negative is a cycle and nothing else."
  [net node-vec]
  (reduce (fn [d [[p q] [_ hi]]]
            (if (or (= p q) (not (Double/isFinite (double hi))))
              d
              (let [cur (get d [p q])]
                (if (or (nil? cur) (< hi cur)) (assoc d [p q] hi) d))))
          (into {} (map (fn [n] [[n n] 0])) node-vec)
          net))

(defn- shortest-paths
  "Floyd–Warshall over `node-vec`: `d[p][q]` becomes the least total weight of any path from
  p to q, which is the tightest upper bound on `t(q) − t(p)` the constraints entail.  A
  missing entry is an unbounded gap and takes no part.

  The result does not depend on the order of `node-vec`: a shortest path is a property of
  the graph, and the loop is the textbook triple that computes it in one O(n³) pass."
  [d node-vec]
  (reduce
   (fn [d k]
     (reduce
      (fn [d p]
        (if-let [dpk (get d [p k])]
          (reduce (fn [d q]
                    (if-let [dkq (get d [k q])]
                      (let [w (+ dpk dkq), cur (get d [p q])]
                        (if (or (nil? cur) (< w cur)) (assoc d [p q] w) d))
                      d))
                  d node-vec)
          d))
      d node-vec))
   d node-vec))

(defn- read-back
  "The closed distance graph as a network again: the bound on `t(q) − t(p)` is `d[p][q]`
  above and `−d[q][p]` below, and a pair bounded on neither side is left unrecorded."
  [d node-vec]
  (into {}
        (for [p node-vec q node-vec
              :when (not= p q)
              :let  [hi (get d [p q] ##Inf)
                     lo (if-let [w (get d [q p])] (- w) ##-Inf)]
              :when (or (Double/isFinite (double lo)) (Double/isFinite (double hi)))]
          [[p q] [lo hi]])))

(defn negative-cycle-nodes
  "The instants lying on some negative cycle of the closed distance graph `d` — exactly
  those whose distance to themselves came out below zero.  What a report can name when the
  contradiction is derived rather than written.

  **Below zero by more than the tolerance.**  A cycle is a sum of stored magnitudes, each
  of them a stated figure multiplied by a stored conversion factor, so a chain that closes
  exactly can arrive back a sliver short — ten tenths of a second sum to
  0.9999999999999999, and against a stated second that is a cycle of −1.1e-16.  The band
  is the same one every other magnitude comparison here reads."
  [d node-vec]
  (let [eps provers/*quantity-tolerance*]
    (into #{} (filter (fn [n] (when-let [w (get d [n n])] (< w (- eps))))) node-vec)))

(defn close
  "All-pairs shortest paths over `net` across `nodes`, returning the tightest network the
  constraints entail — or `:inconsistent` when some instant reaches itself at a negative
  distance, which is a cycle of gaps that must all be closed and cannot be.  A constraint
  unsatisfiable *as given* counts too, whatever the node count: see
  `unsatisfiable-as-given?`.

  `nodes` is what the paths are drawn from, so it is the **caller's** obligation to pass
  every node the network mentions — a node left out is a path never composed.  Passing extra
  nodes is always safe: an isolated one has no finite edge in either direction, so it can
  tighten nothing and can be on no cycle.

  Both verdicts are read to `provers/*quantity-tolerance*`, and that is what makes the
  answer a claim about the *knowledge* rather than about the arithmetic that carried it.  A
  magnitude reaches here multiplied by a stored conversion factor, so one gap written two
  ways — `1.1 Hour` and `66 Minute` — arrives as 3960.0000000000005 and 3960.  Held to an
  exact comparison the pair would cross, a chain of them would close a cycle at −5e-13, and
  a KB whose own `sameQuantity` calls the two equal would have every metric goal in the
  context refused over them.  A contradiction wider than the epsilon is still one."
  [net nodes]
  (if (some unsatisfiable-as-given? net)
    :inconsistent
    (let [node-vec (vec (sort-by str nodes))
          closed   (shortest-paths (distance-graph net node-vec) node-vec)]
      (if (seq (negative-cycle-nodes closed node-vec))
        :inconsistent
        (read-back closed node-vec)))))

;; ---- reading a bound back as an ordering ---------------------------------

(defn point-possibilities
  "Which orderings of two instants a metric bound leaves open, as the base relations of
  `vaelii.impl.point`: given `[lo hi]` on `t(q) − t(p)`, p is before q while the gap can be
  positive, coincident while it can be nil, and after while it can be negative.  A bound is
  a closed interval, so at least one always survives.

  A gap sits within the **tolerance** of zero to count as nil, since a magnitude that ought
  to be exactly nil arrives multiplied by a stored conversion factor and can come back a
  last bit off — without the band an interval meeting another would read as overlapping it.
  The same epsilon `unsatisfiable-as-given?` and `negative-cycle-nodes` read, which is what
  keeps one network from being satisfiable and its orderings undecidable at once."
  [[lo hi]]
  (let [eps provers/*quantity-tolerance*]
    (cond-> #{}
      (> hi eps)                            (conj :before)
      (and (<= lo eps) (>= hi (- eps)))     (conj :equal)
      (< lo (- eps))                        (conj :after))))

(def endpoint-signature
  "Each Allen base relation as the four orderings it forces between two intervals' endpoints
  — A's start against B's start, A's start against B's end, A's end against B's start, and
  A's end against B's end.  The keys are `[which-of-A which-of-B]`.

  Writing an interval as `[start end]` with `start < end`, these follow from the endpoint
  inequalities that define the thirteen relations, with the comparisons those inequalities
  leave implicit filled in: `contains` says A starts first and ends last, and *therefore*
  A's start precedes B's end and A's end follows B's start.  All four are pinned for every
  relation, and the thirteen signatures are distinct — which is what makes them a decision
  procedure rather than a filter that could pass two."
  {:before        {[:start :start] :before [:start :end] :before
                   [:end :start]   :before [:end :end]   :before}
   :meets         {[:start :start] :before [:start :end] :before
                   [:end :start]   :equal  [:end :end]   :before}
   :overlaps      {[:start :start] :before [:start :end] :before
                   [:end :start]   :after  [:end :end]   :before}
   :finished-by   {[:start :start] :before [:start :end] :before
                   [:end :start]   :after  [:end :end]   :equal}
   :contains      {[:start :start] :before [:start :end] :before
                   [:end :start]   :after  [:end :end]   :after}
   :starts        {[:start :start] :equal  [:start :end] :before
                   [:end :start]   :after  [:end :end]   :before}
   :equal         {[:start :start] :equal  [:start :end] :before
                   [:end :start]   :after  [:end :end]   :equal}
   :started-by    {[:start :start] :equal  [:start :end] :before
                   [:end :start]   :after  [:end :end]   :after}
   :during        {[:start :start] :after  [:start :end] :before
                   [:end :start]   :after  [:end :end]   :before}
   :finishes      {[:start :start] :after  [:start :end] :before
                   [:end :start]   :after  [:end :end]   :equal}
   :overlapped-by {[:start :start] :after  [:start :end] :before
                   [:end :start]   :after  [:end :end]   :after}
   :met-by        {[:start :start] :after  [:start :end] :equal
                   [:end :start]   :after  [:end :end]   :after}
   :after         {[:start :start] :after  [:start :end] :after
                   [:end :start]   :after  [:end :end]   :after}})

(defn relations-from-endpoints
  "The Allen relations a closed metric network still permits between two intervals, given
  each one's `[start end]` instants.  A relation survives while every one of the four
  orderings its signature demands is still possible.

  Sound but not sharp: the four bounds are read independently, so a set of them that no
  single assignment of times realizes is not noticed here.  That can only leave a relation
  in that the metric network in fact excludes, never take one out that it permits — which is
  the direction a narrowing must err in."
  [closed [a-start a-end] [b-start b-end]]
  (let [poss {[:start :start] (point-possibilities (constraint closed a-start b-start))
              [:start :end]   (point-possibilities (constraint closed a-start b-end))
              [:end :start]   (point-possibilities (constraint closed a-end b-start))
              [:end :end]     (point-possibilities (constraint closed a-end b-end))}]
    (into #{}
          (filter (fn [rel]
                    (every? (fn [[slot ordering]] (contains? (poss slot) ordering))
                            (endpoint-signature rel))))
          iv/all-relations)))

(defn overlap-bounds-from-endpoints
  "How long two intervals overlap, as `[lo hi]`, read off a closed metric network and their
  endpoints alone.

  The shared stretch runs from the later of the two starts to the earlier of the two ends,
  and is nothing at all when that is backwards:

    overlap = max(0, min(a-end, b-end) − max(a-start, b-start))

  and `min(x,y) − max(p,q)` is `min(x−p, x−q, y−p, y−q)`, four gaps the network already
  bounds.  A minimum lies above the least of the lower bounds and below the least of the
  upper ones, so both sides carry through soundly, and clamping at zero is monotone and
  carries through with them."
  [closed [a-start a-end] [b-start b-end]]
  (let [gaps [(constraint closed a-start a-end)
              (constraint closed b-start a-end)
              (constraint closed a-start b-end)
              (constraint closed b-start b-end)]]
    [(max 0 (reduce min (map first gaps)))
     (max 0 (reduce min (map second gaps)))]))

;; =========================================================================
;; THE KB HALF — reading believed facts in, reading answers back out.
;; =========================================================================

(def stp-predicates
  "The metric predicate a constraint is stated with, and the prover claims."
  '#{temporalDistance})

(def endpoint-predicates
  "The two predicates naming an interval's bounding instants — the bridge to the interval
  algebra."
  '#{startOf endOf})

;; ---- measures in and out -------------------------------------------------
;; The rendering policy here is the one `vaelii.impl.duration` applies — the same tolerance
;; grid, and the dimension's base unit read back out of the same `conversionFactor` table
;; the normalization used — so a separation and a duration are written the same way and a
;; caller can compare one against the other.

;; ---- reading the KB into a network ---------------------------------------

(defn- node-term? [x] (and (symbol? x) (not (sx/variable? x))))

(defn- stated-constraints
  "Every believed, visible `(temporalDistance P Q M)` as `[[dimension base-unit] P Q lo hi]`,
  the magnitudes converted to the dimension's base unit and **snapped to the tolerance
  grid** on the way — `provers/round-magnitude`, the same call `duration/interval-length`
  makes on a length before comparing it.

  That is what makes two spellings of one gap arrive as one constraint rather than as two
  that intersect to nothing: `1.1 Hour` normalizes to 3960.0000000000005 and `66 Minute` to
  3960, and unsnapped they cross.  A separation and a duration are written the same way, so
  they are read to the same grid — and the closure's own tolerance (`close`) is then the
  second line rather than the only one, for noise a chain accumulates rather than one a
  conversion introduced."
  [kb context]
  (vec
   (for [m (res/matches-visible kb '(temporalDistance ?p ?q ?m) context)
         :let  [b (second m), p (get b '?p), q (get b '?q), measure (get b '?m)]
         :when (and (node-term? p) (node-term? q) (provers/measure? measure))
         :let  [[dim lo hi] (provers/normalize-quantity kb measure context)]]
     [[dim (provers/base-unit-of kb (last measure) context)] p q
      (provers/round-magnitude lo) (provers/round-magnitude hi)])))

(defn- file-violation!
  "Append one entry to the KB's accumulating violations ledger, newest 1000 kept — the
  shape `vaelii.impl.violations` keeps, without its chaining-run stamp: nothing here is
  reached from a firing, so there is no run to name."
  [kb entry]
  (when-let [v (:violations kb)]
    (swap! v (fn [entries]
               (let [e' (conj entries entry) n (count e')]
                 (if (> n 1000) (vec (subvec e' (- n 1000))) e'))))))

(defn- report-mixed-dimensions!
  "Append a refused mixed-dimension constraint set to the violations ledger, and log it at
  :warn.

  A gap in metres is not a duration, and summing the two would give a number that means
  nothing — so a context whose `temporalDistance` facts span more than one dimension gets no
  network at all.  That silences **every** metric goal there, one stated outright included,
  which is a wide consequence for what is usually a single mis-spelt unit.  A refusal that
  wide is content the engine dropped, and it belongs where the engine says what it dropped.

  Not a `wff` check, for the reasons `report-inconsistency!` gives and one of its own:
  which dimension is the intruder depends on how many facts stand in each, so blaming the
  odd one out would make the stored KB depend on what else is present."
  [kb context dims]
  (let [entry {:violation :metric-temporal-mixed-dimensions
               :context   context
               :sentence  nil
               :detail    {:message    (str "the temporalDistance constraints visible from "
                                            context " span more than one dimension, so no"
                                            " metric temporal goal is answered there")
                           :dimensions (vec (sort-by str (map first dims)))
                           :units      (vec (sort-by str (map second dims)))}}]
    (trove/log! {:level :warn :id ::metric-temporal-mixed-dimensions :data entry})
    (file-violation! kb entry)))

(defn- build-problem
  "The stated constraints as a problem — or `{:mixed dims}` when they span more than one
  dimension, which is the refusal `problem` reports and answers nil for.  Carried as a value
  rather than decided here so the read stays resident: the reading is a function of the
  believed facts, and whether it has been reported is not."
  [kb context]
  (let [stated (stated-constraints kb context)
        dims   (set (map first stated))]
    (cond
      (empty? stated)    nil
      (= 1 (count dims)) (let [[dim unit] (first dims)]
                           {:dimension dim
                            :unit      unit
                            :net (reduce (fn [net [_ p q lo hi]] (narrow net p q lo hi))
                                         {} stated)})
      :else              {:mixed dims})))

(defn problem
  "Every `temporalDistance` believed and visible from `context`, as `{:dimension :unit :net}`
  — the network together with the dimension and base unit its magnitudes are in.

  nil when nothing is stated, and nil when the stated constraints span **more than one
  dimension**: magnitudes only add up once they are in one unit, so a mixed set is refused
  outright rather than closed into numbers that mean nothing.  That is the same gate
  `duration`'s sum applies, and it fails the same way — no answer, rather than a wrong one.
  The refusal is **reported** (`report-mixed-dimensions!`), once per KB and context, because
  its reach is the whole metric layer there rather than the one goal a sum refuses.

  **Resident** on the KB's `:qcn` atom under a key of this namespace's own, stamped with
  `observe/change-clock` exactly as a qualitative network is (`qcn-kb/read-network`), so a
  rule joining a metric antecedent over many bindings reads the KB once rather than once
  per binding — and so does a settle re-checking one firing after another."
  [kb context]
  (let [prob (observe/cached (:qcn kb) [::problem context]
                             (fn [_stale] (build-problem kb context)))]
    (if-let [dims (:mixed prob)]
      (do (when (observe/newly-seen? (:qcn kb) [::reported-mixed context] dims)
            (report-mixed-dimensions! kb context dims))
          nil)
      prob)))

;; ---- the closure, memoized on the network value --------------------------

(def ^:private closure-cache-limit 256)

(def ^:private closure-cache
  "The closed network, keyed on the network *value*.  Sound across queries because the
  network is derived from the believed facts: any change to them yields a different map and
  so a different key.  Bounded and cleared wholesale when full, like the other caches here."
  (atom {}))

(defn- report-inconsistency!
  "Append an unsatisfiable metric network to the KB's violations ledger, and log it at :warn.

  A cycle of gaps that cannot all be closed is a clash among *several* stored facts with
  nothing to prefer between them, so it belongs where the engine reports content it had to
  drop rather than being thrown.  Three reasons it is not a `wff` check, and they are the
  metric reading of the three the qualitative calculi give:

  * `wff` **throws**, and the fact it would throw on is whichever arrived last.  No single
    constraint of a negative cycle is the wrong one — the cycle is a property of the set —
    so blaming a member of it would make the stored KB depend on assertion order.
  * the check costs an all-pairs closure, and `wff` runs per assert.  Every temporal fact
    would pay an O(n³) pass to store.
  * the prover is **opt-in**.  A KB that never registered it would be held to an arithmetic
    it never asked to reason with.

  Recorded on the way past, once per network **per KB and context**: the closure itself is
  shared on the network value across both, so a report keyed on it would fire for whichever
  caller ran the pass and leave the others answering nothing with nothing to read.  A change
  of belief yields a different network and reports again."
  [kb context {:keys [net unit]} cycle-nodes]
  (let [bad   (unsatisfiable-pairs net)
        entry {:violation :metric-temporal-inconsistency
               :context   context
               :sentence  nil
               :detail    (cond-> {:message (str "the temporalDistance constraints visible"
                                                 " from " context " cannot all be"
                                                 " satisfied, so no metric temporal goal"
                                                 " is answered there")
                                   :unit  unit
                                   :nodes (vec (sort-by str (nodes net)))}
                            (seq bad)         (assoc :pairs (vec (sort-by str bad)))
                            (seq cycle-nodes) (assoc :cycle (vec (sort-by str cycle-nodes))))}]
    (trove/log! {:level :warn :id ::metric-temporal-inconsistency :data entry})
    (file-violation! kb entry)))

(defn- cycle-nodes-of
  "The instants on a negative cycle of `net`, for the report.  Recomputed rather than carried
  out of `close`, which answers a verdict and not a diagnosis; it runs once per *newly*
  inconsistent network, never on the answering path."
  [net]
  (let [node-vec (vec (sort-by str (nodes net)))]
    (negative-cycle-nodes (shortest-paths (distance-graph net node-vec) node-vec) node-vec)))

(defn closure
  "The closed network of `prob`, memoized on the network value.  `:inconsistent` when the
  constraints contradict each other, reported through `report-inconsistency!` on the way
  past — the closure has just proved it, and the alternative is a query that silently answers
  nothing.

  The key is the **network alone**, not the nodes a caller adds because its goal names them.
  Such a node is isolated: it has a finite edge in neither direction, so it can tighten no
  pair and lie on no cycle, and `constraint` answers unbounded for a pair the read-back never
  recorded.  So one caller's answer is another's, and the pass runs once per network rather
  than once per shape of question.

  The **report** is deliberately not on that path.  Two KBs, or two contexts of one KB,
  reaching the same network share the pass — and a ledger entry is a claim about a KB and a
  context, so it hangs off `observe/newly-seen?` instead: this KB, this context, this
  network.  A cache hit still reports if the KB has not said it yet."
  [kb context {:keys [net] :as prob} extra-nodes]
  (let [result (caches/read-through closure-cache closure-cache-limit net
                                    #(close net (into (nodes net) extra-nodes)))]
    (when (and (= :inconsistent result)
               (observe/newly-seen? (:qcn kb) [::reported context] net))
      (report-inconsistency! kb context prob (cycle-nodes-of net)))
    result))

(defn closed-network
  "The closed metric network visible from `context`, or nil when nothing is stated (or the
  constraints span more than one dimension), or `:inconsistent` when they contradict."
  [kb context]
  (when-let [prob (problem kb context)]
    (closure kb context prob nil)))

(defn separation
  "The tightest `[lo hi]` bound on `t(q) − t(p)` the constraints visible from `context`
  entail, in the dimension's base unit, as `[[dimension unit] lo hi]`.

  nil when nothing is stated at all, and nil when the network is inconsistent — an
  unsatisfiable theory is not mined for a number, the same rule the qualitative calculi
  follow.  A pair the constraints reach on neither side comes back `[-∞ ∞]`, which is a real
  answer (\"nothing is known\") and not an absent one."
  [kb context p q]
  (when-let [{:keys [dimension unit] :as prob} (problem kb context)]
    (let [closed (closure kb context prob [p q])]
      (when-not (= :inconsistent closed)
        (into [[dimension unit]] (constraint closed p q))))))

(defn inconsistent?
  "Do the `temporalDistance` constraints visible from `context` contradict each other?"
  [kb context]
  (= :inconsistent (closed-network kb context)))

;; ---- the bridge to intervals ---------------------------------------------

(defn endpoints-of
  "An interval's `[start end]` instants as `(startOf I P)` and `(endOf I P)` state them,
  visible from `context` and believed — or nil when either is missing, or when either is
  stated of two *different* instants, which is a disagreement no reasoning should paper
  over."
  [kb i context]
  (let [one (fn [pred]
              (let [ps (into #{} (comp (map (comp #(get % '?p) second))
                                       (filter node-term?))
                             (res/matches-visible kb (list pred i '?p) context))]
                (when (= 1 (count ps)) (first ps))))
        s   (one 'startOf)
        e   (one 'endOf)]
    (when (and s e) [s e])))

(defn intervals-with-endpoints
  "Every interval both of whose bounding instants are named and agreed on, as
  `{interval [start end]}`."
  [kb context]
  (into {}
        (keep (fn [i] (when-let [ends (endpoints-of kb i context)] [i ends])))
        (into #{}
              (comp (mapcat #(res/matches-visible kb (list % '?i '?p) context))
                    (map (comp #(get % '?i) second))
                    (filter node-term?))
              endpoint-predicates)))

(defn allen-narrowing
  "What the metric constraints pin down about the *interval* relations, as an Allen network
  `{[i j] → #{base relations}}` for a caller to intersect into one read from stored facts.

  This is the payoff of the bridge, and it runs one way only: **metric narrows qualitative**.
  A closed gap of `end(A) < start(B)` leaves `before` the only Allen relation A and B can
  stand in, and the thirteen signatures in `endpoint-signature` do the same for every other
  shape of constraint.  Nothing is asserted, nothing is mutated, and no interval network is
  touched — the result is a value.

  Only pairs the constraints actually narrow are recorded; a pair still open to all thirteen
  is the absence of a claim.  nil when there is nothing to read: no metric constraints, no
  interval with both endpoints named, or an inconsistent network — which narrows nothing,
  since an unsatisfiable theory is not mined for conclusions."
  [kb context]
  (when-let [prob (problem kb context)]
    (let [ends (intervals-with-endpoints kb context)]
      (when (>= (count ends) 2)
        (let [closed (closure kb context prob (mapcat val ends))]
          (when-not (= :inconsistent closed)
            (into {}
                  (for [[i ei] ends [j ej] ends
                        :when (not= i j)
                        :let  [rels (relations-from-endpoints closed ei ej)]
                        :when (not= rels iv/all-relations)]
                    [[i j] rels]))))))))

(defn overlap-window
  "The bounds the metric constraints put on how long intervals `i1` and `i2` overlap, as
  `[[dimension unit] lo hi]` in the dimension's base unit — `hi` possibly infinite, since a
  network may pin a floor without a ceiling.

  nil when there is nothing to read (no constraints, an endpoint missing, an inconsistent
  network) and nil when the answer is the vacuous `[0 ∞]`, which is not a bound at all.
  `vaelii.impl.duration` intersects what comes back with the bound it computes from the
  stored lengths and the qualitative relation set: both are sound, so their intersection is."
  [kb context i1 i2]
  (when-let [{:keys [dimension unit] :as prob} (problem kb context)]
    (let [e1 (endpoints-of kb i1 context)
          e2 (endpoints-of kb i2 context)]
      (when (and e1 e2)
        (let [closed (closure kb context prob (concat e1 e2))]
          (when-not (= :inconsistent closed)
            (let [[lo hi] (overlap-bounds-from-endpoints closed e1 e2)]
              (when-not (and (zero? lo) (not (Double/isFinite (double hi))))
                [[dimension unit] lo hi]))))))))

;; ---- the prover ----------------------------------------------------------

(defn- contains-bound?
  "Is the derived `[lo hi]` contained in the stated one — is the stated bound *entailed*?
  A bound is a claim that the gap lies within it, so a wider claim follows from a narrower
  one, and the tolerance is the same epsilon the measure comparisons use."
  [[lo hi] [slo shi]]
  (let [eps provers/*quantity-tolerance*]
    (and (>= lo (- slo eps)) (<= hi (+ shi eps)))))

(defn- solve-distance
  "`(temporalDistance P Q M)` — close the constraints, read the tightest gap between P and Q,
  then bind or check.

  A **bind** needs both bounds finite: a half-bounded separation is a real piece of knowledge
  but not a measure, and there is no honest structural NAT for it, so the goal simply has no answer
  rather than a fabricated one.  A **check** has no such trouble — a stated bound with an
  infinite side is not written, and a finite one is either contained or not."
  [kb goal context]
  (let [[_ p q m] goal]
    (when-let [{:keys [dimension unit] :as prob} (problem kb context)]
      (let [closed (closure kb context prob [p q])]
        (when-not (= :inconsistent closed)
          (let [[lo hi] (constraint closed p q)]
            (cond
              (sx/variable? m)
              (when (and (Double/isFinite (double lo)) (Double/isFinite (double hi)))
                [{m (provers/render-quantity lo hi unit)}])

              (provers/measure? m)
              (let [[dim* slo shi] (provers/normalize-quantity kb m context)]
                (if (and (= dimension dim*) (contains-bound? [lo hi] [slo shi])) [{}] []))

              :else [])))))))

(defn- answer-slot?
  "Can `m` be the answer argument — a variable to bind, or a ground measure to check?"
  [m]
  (or (sx/variable? m) (provers/measure? m)))

(defrecord TemporalDistanceProver []
  provers/Prover
  (applicable? [_ _ goal _]
    (and (sequential? goal) (= 4 (count goal))
         (contains? stp-predicates (first goal))
         (node-term? (nth goal 1)) (node-term? (nth goal 2))
         (answer-slot? (nth goal 3))))
  ;; A computation, so at most one answer — and the estimate must not cost what it
  ;; estimates, which here would be the reads plus an all-pairs closure.
  (est-bindings [_ _ _ _] 1)
  ;; A closure over the stored constraints before the first answer, not a search.
  (cost         [_ _ _ _] :compute)
  ;; Authoritative over the constraints it reads: the answer is a property of the
  ;; *whole* set rather than of any one stored fact, and it entails every stated bound
  ;; it is contained in, so unioning a raw fact match in would add nothing this does
  ;; not already answer.  A source it does not read is `provers/sole-prover`'s
  ;; question.
  (completeness [_ _ _ _] 100)
  (solve [_ kb goal context] (solve-distance kb goal context)))

(defn stp-prover
  "The metric temporal prover, to register with `vaelii.core/add-prover`."
  []
  (->TemporalDistanceProver))

;; ---- what the metric side holds, declared -------------------------------
;;
;; Registered here rather than in a central list, so a process that never loaded the
;; metric-time reasoner reports no row for it — which is the honest answer, and better
;; than a row of zeroes for a cache that does not exist.

(caches/register-cache
 {:cache    :metric-closures
  :label    "Metric closures"
  :scope    :process
  :unit     "networks"
  :limit    closure-cache-limit
  :counters nil
  :note     (str "The all-pairs shortest-path closure of a metric network, keyed on the "
                 "network value — so two contexts stating the same durations share one "
                 "closure, and any change to the believed facts is a different key.")
  :read     (fn [_] {:entries (count @closure-cache)})
  :clear    (fn [_] (let [n (count @closure-cache)] (reset! closure-cache {}) n))})

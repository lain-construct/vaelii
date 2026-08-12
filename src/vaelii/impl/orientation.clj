;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.orientation
  "Cardinal-direction reasoning — a relation algebra over the generic constraint network
  in `vaelii.impl.qcn`, and the companion to the RCC-8 topology in `vaelii.impl.space`
  (`vaelii.impl.interval` is the third, over time).  RCC-8 says whether two regions touch
  or nest; this says where one place lies *relative to* another.  (Orientation is the
  standard qualitative-spatial
  name for this family — topology, orientation, distance — and it keeps the namespace
  clear of a rule's chaining `:direction`, which is an unrelated thing.)

  The nine base relations are the projection-based cardinal direction calculus.  A
  direction decomposes into two **independent** one-dimensional point relations, one per
  axis — east-west on x, north-south on y — each `:lt` / `:eq` / `:gt`:

    :n  [:eq :gt]   :ne [:gt :gt]   :e [:gt :eq]   :se [:gt :lt]
    :s  [:eq :lt]   :sw [:lt :lt]   :w [:lt :eq]   :nw [:lt :gt]
    :eq [:eq :eq]   (the same place)

  That decomposition is the whole trick, and it is why there is no 9×9 table here:
  **composition is computed, not transcribed.**  Composing two directions is composing
  their x projections and their y projections separately through the three-relation
  point algebra, then reading the result pairs back as directions.  Since the nine
  directions are exactly the nine `[x y]` combinations, that read-back is total and the
  composition of any two base directions is a non-empty set — so the table nobody wrote
  down cannot disagree with itself, and north-then-east *is* northeast because `:eq;:gt`
  is `:gt` on x and `:gt;:eq` is `:gt` on y.

  Directions are **stored as ordinary sentexes** — the nine named binary predicates
  (`northOf`, `southeastOf`, `sameLocationAs`, …), plus four derived predicates
  (`northwardOf`, `eastwardOf`, …) that each name a *disjunction* of them: a northerly
  component, whatever the east-west one.  Places are ordinary individuals; nothing about
  them is special.

  The calculus reads every asserted direction visible from a context into a
  qualitative constraint network — `{[a b] → #{possible base directions}}`, an
  unrecorded pair meaning \"unknown\", i.e. all nine — and `qcn/path-consistent`
  tightens it to a fixpoint.  the prover then answers a goal `(P a b)` by
  **entailment**: it holds iff every direction still possible from a to b satisfies P,
  `possible ⊆ denotation(P)`.  So `(northeastOf A B)` and `(northeastOf B D)` entail
  `(northeastOf A D)`, and with it the weaker `(northwardOf A D)` and `(eastwardOf A D)`.

  An emptied constraint anywhere means the asserted directions are unsatisfiable, and
  then *no* direction goal is answered — an inconsistent theory should not be mined for
  conclusions.

  **Soundness.** Path consistency is sound but not in general complete, so an entailment
  reported here is real while a *non*-entailment means \"not provable\", never \"provably
  false\" — the same open-world reading `argIsa` and `exceptWhen` take.

  The vocabulary ships in `kb/upper/CxSpace.txt` beside the RCC-8 one — both are
  *about* space, so CxCore keeps only the grammar they are declared in.  The prover
  is **opt-in** on top of it: register it with `vaelii.core/add-prover`, and until then a
  KB stores and retrieves directions as ordinary facts without paying for the network."
  (:require [clojure.set :as set]
            [vaelii.impl.qcn-kb :as qkb]))

;; ---- the algebra --------------------------------------------------------

(def all-directions
  "The nine base directions — the eight compass points and coincidence.  Jointly
  exhaustive and pairwise disjoint, so exactly one holds of any two places, and this is
  the universe of the algebra: the constraint on a pair nothing is known about."
  #{:n :ne :e :se :s :sw :w :nw :eq})

(def direction->xy
  "Each base direction as its `[x-relation y-relation]` projection — where the target
  lies on the east-west axis, and where on the north-south one."
  {:n  [:eq :gt], :ne [:gt :gt], :e [:gt :eq], :se [:gt :lt]
   :s  [:eq :lt], :sw [:lt :lt], :w [:lt :eq], :nw [:lt :gt]
   :eq [:eq :eq]})

(def xy->direction
  "The projection read backwards.  It is **total** over the nine `[x y]` combinations —
  three point relations on each of two axes, nine directions — which is what makes
  composition total: whatever pair of point relations the axes compose to names a
  direction, so no combination falls out of the algebra."
  (set/map-invert direction->xy))

(def point-compose
  "The one-dimensional point algebra: `[a b]` → the relations possible between x and z
  when a relates x to y and b relates y to z.  Only the two disagreeing pairs lose
  information — x < y and y > z says nothing at all about x and z."
  {[:lt :lt] #{:lt}, [:lt :eq] #{:lt}, [:lt :gt] #{:lt :eq :gt}
   [:eq :lt] #{:lt}, [:eq :eq] #{:eq}, [:eq :gt] #{:gt}
   [:gt :lt] #{:lt :eq :gt}, [:gt :eq] #{:gt}, [:gt :gt] #{:gt}})

(defn compose
  "The composition of two direction SETS: every direction possible from x to z when the
  direction x→y is in `s1` and y→z is in `s2`.

  Computed, never looked up.  Each direction is a pair of independent axis projections,
  so composing them is composing each axis through `point-compose` and taking the
  product of the two results — north-then-east is `:eq;:gt` = `:gt` on x and `:gt;:eq` =
  `:gt` on y, which is northeast.  Two opposite diagonals lose both axes at once and
  compose to the whole universe."
  [s1 s2]
  (into #{}
        (for [d1 s1 d2 s2
              :let [[ax ay] (direction->xy d1)
                    [bx by] (direction->xy d2)]
              cx (point-compose [ax bx])
              cy (point-compose [ay by])]
          (xy->direction [cx cy]))))

(def point-converse
  "The one-dimensional point algebra's converse: reading a relation backwards flips it."
  {:lt :gt, :eq :eq, :gt :lt})

(defn- converse-direction
  "The converse of one base direction — flip both axes, so north becomes south and
  northeast southwest.  Coincidence is its own converse."
  [d]
  (let [[x y] (direction->xy d)]
    (xy->direction [(point-converse x) (point-converse y)])))

(defn converse-set
  "The converse of a direction set — how an asserted `(P a b)` constraint is read
  backwards as the constraint on `(b a)`."
  [dirs]
  (into #{} (map converse-direction) dirs))

(def direction-algebra
  "The cardinal directions as a `vaelii.impl.qcn` relation algebra."
  {:universe all-directions
   :identity #{:eq}
   :compose  compose
   :converse converse-set})

;; ---- the vocabulary -----------------------------------------------------

(def base-direction-predicate
  "Base direction keyword → the binary predicate a fact about it is stored under."
  '{:n  northOf,     :ne northeastOf, :e eastOf, :se southeastOf
    :s  southOf,     :sw southwestOf, :w westOf, :nw northwestOf
    :eq sameLocationAs})

(def direction-denotation
  "Every direction predicate — the nine base ones and the four derived ones — mapped to
  the set of base directions it denotes.  A goal `(P a b)` is entailed exactly when the
  directions still possible from a to b are a *subset* of P's denotation, so a derived
  predicate is entailed by more networks than a base one, and the base predicates are
  the singletons.

  The four derived predicates each constrain one axis and leave the other open:
  `northwardOf` is anything with a northerly component, whatever it does east-west.  None
  of them contains `:eq`, so none holds of a place and itself."
  (merge
   (into {} (map (fn [[dir pred]] [pred #{dir}])) base-direction-predicate)
   '{northwardOf #{:n :ne :nw}
     southwardOf #{:s :se :sw}
     eastwardOf  #{:e :ne :se}
     westwardOf  #{:w :nw :sw}}))

;; ---- the calculus, and the glue it shares with every other algebra -------

(def cardinal
  "The cardinal directions as a `vaelii.impl.qcn-kb` calculus — the algebra, the
  vocabulary, and the two caches.  Everything below delegates to the shared glue, which
  is the same code RCC-8 and the interval algebra run."
  (qkb/calculus :cardinal direction-algebra direction-denotation))

(defn constraint
  "The constraint set on `[i j]` in `net`: `#{:eq}` on the diagonal, the recorded set,
  else all nine (unknown)."
  [net i j]
  (qkb/constraint cardinal net i j))

(defn possible-directions
  "The base directions still possible from place `a` to place `b` given everything
  believed in `context` — `#{}` when the network is inconsistent."
  [kb context a b]
  (qkb/possible cardinal kb context a b))

(defn definite-direction
  "The single base direction from `a` to `b` when path consistency pins it down;
  `:inconsistent` when the network contradicts itself, `:unknown` when two or more
  directions remain possible."
  [kb context a b]
  (qkb/definite cardinal kb context a b))

(defn inconsistent?
  "Is the direction network visible from `context` unsatisfiable?"
  [kb context]
  (qkb/inconsistent? cardinal kb context))

(defn orientation-prover
  "The cardinal-direction entailment prover, to register with `vaelii.core/add-prover`."
  []
  (qkb/prover cardinal))

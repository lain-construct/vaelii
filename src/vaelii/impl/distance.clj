;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.distance
  "Qualitative distance — how far apart two things are, said in classes rather than in
  numbers: co-located, very close, close, near, moderately far, far, very far.  A relation
  algebra over the generic constraint network in `vaelii.impl.qcn`, beside the RCC-8
  topology of `vaelii.impl.space`, the compass of `vaelii.impl.orientation`, the frame of
  reference of `vaelii.impl.relative` and Allen's intervals in `vaelii.impl.interval`.
  Those say *where* or *when*; this says *how far*, which is the third of the three
  standard qualitative-spatial questions — topology, orientation, distance.

  The seven classes are an ordered chain, each denoting a half-open interval `(lo, hi]` of
  the non-negative reals.  They tile `[0, ∞)` exactly, so they are jointly exhaustive and
  pairwise disjoint and exactly one holds of any two things.  The bounds are the **one**
  thing here that is transcribed rather than computed, and they are a *scale* rather than
  a unit: multiplying every bound by one factor leaves the composition table unchanged, so
  what the numbers fix is the ratio between neighbouring classes, not a length in metres.

  **Composition is computed from the bounds by the triangle inequality**, not transcribed.
  If d(A,B) ∈ (l1, h1] and d(B,C) ∈ (l2, h2] then

    max(l1 - h2, l2 - h1)  <  d(A,C)  <=  h1 + h2

  — the lower bound strict because a lower bound is, the upper attained when the two legs
  are laid out in a line — and the composed class set is every class whose own interval
  meets that range.  Distance being non-negative, a lower bound below zero simply means
  zero is reachable, which is exactly the co-located class's interval `(-∞, 0]`, so the
  arithmetic needs no special case for it.  That makes composition **exact**: the range is
  the set of distances the geometry actually admits, and the table is the set of classes
  that meet it.  A different chain of bounds gives a different, still-correct table, which
  is what a transcribed table could never promise.

  **This composes weakly, and that is the honest reading of it.**  Composing two mid-range
  classes usually leaves several classes possible — close-then-close spans everything from
  co-located to near — because a class is an interval and the triangle inequality relates
  intervals loosely.  So the payoff is **refutation and consistency-checking** rather than
  pinpoint entailment: it will tell you that two things very close to a third cannot be
  very far from each other, and it will catch a set of distance claims that no arrangement
  satisfies.  Pinning a pair down takes either a chain through the co-located class, which
  is the identity, or several facts about the same pair intersecting.

  **Distance is symmetric**, so the converse of every class set is itself and `converse` is
  the identity function — the one place this algebra differs structurally from the four
  beside it, whose converse maps each base relation to a different one.  The symmetry lives
  in the algebra and deliberately *not* in a `(symmetric P)` declaration: that metadata
  would hand these predicates to the generic symmetric-relation prover as well, where the
  entailment prover means to claim them alone.

  Distances are **stored as ordinary sentexes** — the seven named binary predicates
  (`coLocatedWith`, `closeTo`, `veryFarFrom`, …), plus three derived predicates
  (`withinNearDistanceOf`, `beyondFarDistanceFrom`, `atSomeDistanceFrom`) that each name a
  *range* of them.  The things related are ordinary individuals; nothing about them is
  special.

  The calculus reads every asserted distance visible from a context into a
  qualitative constraint network — `{[a b] → #{possible classes}}`, an unrecorded pair
  meaning \"unknown\", i.e. all seven — and `qcn/path-consistent` tightens it to a
  fixpoint.  The prover then answers a goal `(P a b)` by **entailment**: it holds iff every
  class still possible between a and b satisfies P, `possible ⊆ denotation(P)`.

  An emptied constraint anywhere means the asserted distances are unsatisfiable, and then
  *no* goal of this calculus is answered in that context — an inconsistent theory should
  not be mined for conclusions.

  **Soundness.** Path consistency is sound but not in general complete, so an entailment
  reported here is real while a *non*-entailment means \"not provable\", never \"provably
  false\" — the same open-world reading `argIsa` and `exceptWhen` take.

  The vocabulary ships in `kb/upper/SpaceContext.txt` beside the topology, the compass and
  the frames of reference — all of them are *about* space, so CoreContext keeps only the
  grammar they are declared in.  The prover is **opt-in** on top of it: register it with
  `vaelii.core/add-prover`, and until then a KB stores and retrieves distances as ordinary
  facts without paying for the network."
  (:require [vaelii.impl.qcn-kb :as qkb]))

;; ---- the algebra --------------------------------------------------------

(def class-order
  "The seven classes as the chain they are, nearest first.  Nothing reasons from this
  order — the bounds decide everything — but reading and rendering want it."
  [:co :very-close :close :near :moderate :far :very-far])

(def class-bounds
  "Each class as the bounds `[lo hi]` of the distances it covers, read as the half-open
  interval `(lo, hi]`: lower bound exclusive, upper inclusive.  The intervals tile the
  non-negative reals in `class-order`, each starting where the one before it ends, so
  every distance falls in exactly one.

  `:co` runs from -∞ so that, distance being non-negative, it denotes exactly zero — which
  is what makes it the identity of the algebra without an arm in the arithmetic to say so.
  `:very-far` runs to +∞ for the same kind of reason: the chain has to end somewhere, and
  the honest end is unbounded.

  This table is the only transcribed thing in the namespace, and it is a *scale*: scaling
  every finite bound by one factor changes no entry of the composition table."
  {:co         [##-Inf 0]
   :very-close [0 1]
   :close      [1 10]
   :near       [10 100]
   :moderate   [100 1000]
   :far        [1000 10000]
   :very-far   [10000 ##Inf]})

(def all-classes
  "The seven jointly-exhaustive, pairwise-disjoint distance classes — the universe of the
  algebra, and so the constraint on a pair nothing is known about."
  (set class-order))

(defn classify
  "The single class a numeric distance `d` falls in.  The classes tile `[0, ∞)`, so this is
  total over real distances — and nil for a negative number, which is no distance at all
  and which `:co`'s unbounded lower end would otherwise swallow."
  [d]
  (when-not (neg? d)
    (first (filter (fn [c]
                     (let [[lo hi] (class-bounds c)]
                       (and (< lo d) (<= d hi))))
                   class-order))))

(defn- triangle-range
  "The distances possible between A and C when d(A,B) lies in `(l1, h1]` and d(B,C) in
  `(l2, h2]` — the triangle inequality |d1 - d2| <= d3 <= d1 + d2 read on the bounds, as
  the half-open range `(L, H]`.

  The lower bound is the larger of the two one-sided differences, and it is exclusive
  because the legs' own lower bounds are: d1 > l1 and d2 <= h2 give d1 - d2 > l1 - h2
  strictly.  A negative L means the two legs' intervals overlap, so the legs can be equal
  and zero is reachable — and `(-∞, 0]` is exactly the co-located class's interval, so
  nothing special has to be said about it."
  [[l1 h1] [l2 h2]]
  [(max (- l1 h2) (- l2 h1)) (+ h1 h2)])

(defn- meets?
  "Do the half-open ranges `(lo, hi]` and `(l, h]` share a distance?  Two such intervals
  intersect exactly when each starts before the other ends."
  [[lo hi] [l h]]
  (and (< lo h) (< l hi)))

(defn compose
  "The composition of two class SETS: every distance class possible between A and C when
  d(A,B) is in `s1` and d(B,C) is in `s2`.

  Computed, never looked up.  Each class is an interval, so composing two of them is
  the triangle inequality over their bounds, and the answer is every class whose interval
  meets the resulting range.  Since the range is exactly the set of distances the geometry
  admits and the classes tile the line, the answer is exactly the set of classes that can
  occur — no looser, and no tighter than the truth."
  [s1 s2]
  (into #{}
        (for [c1 s1 c2 s2
              :let [r (triangle-range (class-bounds c1) (class-bounds c2))]
              c   class-order
              :when (meets? (class-bounds c) r)]
          c)))

(defn converse-set
  "The converse of a class set — **itself**.  Distance is symmetric, d(a,b) = d(b,a), so
  reading an asserted `(P a b)` backwards as the constraint on `(b a)` changes nothing.
  Named rather than inlined so that what is a structural fact about this algebra reads as
  one beside the four whose converse permutes their relations."
  [classes]
  classes)

(def distance-algebra
  "Qualitative distance as a `vaelii.impl.qcn` relation algebra."
  {:universe all-classes
   :identity #{:co}
   :compose  compose
   :converse converse-set})

;; ---- the vocabulary -----------------------------------------------------

(def base-class-predicate
  "Distance class keyword → the binary predicate a fact about it is stored under.  `:co` is
  spelled `coLocatedWith` rather than borrowing the compass's `sameLocationAs` or the
  frame's `sameRelativePositionAs`: a predicate belongs to exactly one calculus, each
  network reads only its own vocabulary, and this one is a claim about a distance being
  zero."
  '{:co         coLocatedWith
    :very-close veryCloseTo
    :close      closeTo
    :near       nearTo
    :moderate   moderatelyFarFrom
    :far        farFrom
    :very-far   veryFarFrom})

(def distance-denotation
  "Every distance predicate — the seven base ones and the three derived ones — mapped to
  the set of classes it denotes.  A goal `(P a b)` is entailed exactly when the classes
  still possible between a and b are a *subset* of P's denotation, so a derived predicate
  is entailed by more networks than a base one, and the base predicates are the singletons.

  The three derived ones each name a contiguous *range* of the chain, which is the shape a
  question about a scale actually takes: no further than near, at least far, and any
  distance at all above zero.  `atSomeDistanceFrom` is the complement of the identity, so
  it holds of no thing and itself."
  (merge
   (into {} (map (fn [[cls pred]] [pred #{cls}])) base-class-predicate)
   {'withinNearDistanceOf  #{:co :very-close :close :near}
    'beyondFarDistanceFrom #{:far :very-far}
    'atSomeDistanceFrom    (disj all-classes :co)}))

;; ---- the calculus, and the glue it shares with every other algebra -------

(def qualitative-distance
  "Qualitative distance as a `vaelii.impl.qcn-kb` calculus — the algebra, the vocabulary,
  and the two caches.  Everything below delegates to the shared glue, which is the same
  code the other calculi run."
  (qkb/calculus :distance distance-algebra distance-denotation))

(defn constraint
  "The constraint set on `[i j]` in `net`: `#{:co}` on the diagonal, the recorded set, else
  all seven (unknown)."
  [net i j]
  (qkb/constraint qualitative-distance net i j))

(defn possible-distances
  "The distance classes still possible between `a` and `b` given everything believed in
  `context` — `#{}` when the network is inconsistent."
  [kb context a b]
  (qkb/possible qualitative-distance kb context a b))

(defn definite-distance
  "The single distance class between `a` and `b` when path consistency pins it down;
  `:inconsistent` when the network contradicts itself, `:unknown` when two or more classes
  remain possible — which, on a chain this coarse, is the usual answer."
  [kb context a b]
  (qkb/definite qualitative-distance kb context a b))

(defn inconsistent?
  "Is the distance network visible from `context` unsatisfiable?"
  [kb context]
  (qkb/inconsistent? qualitative-distance kb context))

(defn distance-prover
  "The qualitative-distance entailment prover, to register with `vaelii.core/add-prover`."
  []
  (qkb/prover qualitative-distance))

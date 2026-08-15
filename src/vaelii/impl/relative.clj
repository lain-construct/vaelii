;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.relative
  "Relative direction — where one thing lies from another **as seen from a point of
  view**: the mouse on the lion's left, the crow in front of the fox.  A relation algebra
  over the generic constraint network in `vaelii.impl.qcn`, beside the RCC-8 topology of
  `vaelii.impl.space`, the cardinal directions of `vaelii.impl.orientation` and Allen's
  intervals in `vaelii.impl.interval`.  The compass says where a place is on the map;
  this says where a thing is from where you stand, which is the only thing a story ever
  says.

  **The frame of reference is the context.**  Relative direction is ternary in the
  literature — A is left of B *from viewpoint C* — and a constraint network is strictly
  binary, a constraint being a set of relations on a *pair*.  The resolution is that a
  context already **is** a frame of reference: a network is built per context out of the
  facts visible there, so `(leftOf Mouse Lion)` asserted in `CxLionMouse` is a claim
  in that context's frame and in no other.  Two contexts looking at the same
  individuals from opposite sides state opposite facts and neither contaminates the
  other; a frame that has to be argued about rather than assumed is a context, and the
  argument is `genlCx`.  So this calculus is binary, composes exactly as the
  cardinal directions do, and needs nothing of the shared glue that the other three do
  not already need.

  The nine base relations are the projection-based calculus that shape allows.  A
  relative direction decomposes into two **independent** one-dimensional point relations,
  one per axis of the frame — left-right, and front-back — each `:lt` / `:eq` / `:gt`,
  reading the axes as coordinates that grow rightwards and frontwards:

    :left  [:lt :eq]   :front-left  [:lt :gt]   :behind-left  [:lt :lt]
    :right [:gt :eq]   :front-right [:gt :gt]   :behind-right [:gt :lt]
    :front [:eq :gt]   :behind      [:eq :lt]   :eq           [:eq :eq]

  That decomposition is the whole trick, and it is why there is no 9×9 table here:
  **composition is computed, not transcribed.**  Composing two relations is composing
  their left-right projections and their front-back projections separately through the
  three-relation point algebra, then reading the result pairs back as relations.  Since
  the nine relations are exactly the nine `[left-right front-back]` combinations, that
  read-back is total and the composition of any two base relations is a non-empty set —
  so the table nobody wrote down cannot disagree with itself, and left-then-in-front *is*
  front-left because `:lt;:eq` is `:lt` on one axis and `:eq;:gt` is `:gt` on the other.
  (The one-dimensional point algebra below is the same mathematics the cardinal
  directions project onto; the two calculi share it as a fact about ordered axes, not as
  code, and neither reads the other's vocabulary.)

  Relative directions are **stored as ordinary sentexes** — the nine named binary
  predicates (`leftOf`, `frontRightOf`, `sameRelativePositionAs`, …), plus four derived
  predicates (`leftwardOf`, `frontwardOf`, …) that each name a *disjunction* of them: a
  leftward component, whatever the front-back one.  The things related are ordinary
  individuals; nothing about them is special, and nothing declares a viewpoint, because
  the context is the viewpoint.

  The calculus reads every asserted relation visible from a context into a
  qualitative constraint network — `{[a b] → #{possible base relations}}`, an unrecorded
  pair meaning \"unknown\", i.e. all nine — and `qcn/path-consistent` tightens it to a
  fixpoint.  The prover then answers a goal `(P a b)` by **entailment**: it holds iff
  every relation still possible between a and b satisfies P, `possible ⊆ denotation(P)`.
  So `(leftOf A B)` and `(leftOf B D)` entail `(leftOf A D)`, and with it the weaker
  `(leftwardOf A D)`.

  An emptied constraint anywhere means the asserted relations are unsatisfiable, and then
  *no* goal of this calculus is answered in that context — an inconsistent theory should
  not be mined for conclusions.  Since the frame is the context, an inconsistency is
  confined to the frame it was stated in.

  **Soundness.** Path consistency is sound but not in general complete, so an entailment
  reported here is real while a *non*-entailment means \"not provable\", never \"provably
  false\" — the same open-world reading `argIsa` and `exceptWhen` take.

  The vocabulary ships in `kb/upper/CxSpace.txt` beside the topology, the compass and
  the distance scale — all of them are *about* space, so CxCore keeps only the
  grammar they are declared in.  The prover is **opt-in** on top of it: register it with
  `vaelii.core/add-prover`, and until then a KB stores and retrieves relative directions
  as ordinary facts without paying for the network."
  (:require [vaelii.impl.projection :as proj]
            [vaelii.impl.qcn-kb :as qkb]))

;; ---- the algebra --------------------------------------------------------

(def relation->axes
  "Each base relation as its `[left-right front-back]` projection — where the target lies
  on the frame's left-right axis, and where on its front-back one.  The coordinates grow
  rightwards and frontwards, so `:lt` on the first axis is *to the left* and `:gt` on the
  second is *in front*.  The nine base relations are these keys: the four sides, the four
  corners between them, and coincidence, jointly exhaustive and pairwise disjoint, so
  exactly one holds of any two things in one frame.

  This table is the whole of what distinguishes the relative frame from the cardinal
  directions (`vaelii.impl.orientation`); everything algebraic about them is
  `vaelii.impl.projection`'s, computed from here."
  {:left  [:lt :eq], :front-left  [:lt :gt], :behind-left  [:lt :lt]
   :right [:gt :eq], :front-right [:gt :gt], :behind-right [:gt :lt]
   :front [:eq :gt], :behind      [:eq :lt], :eq           [:eq :eq]})

(def relative-algebra
  "The relative frame as a `vaelii.impl.qcn` relation algebra — universe, identity,
  composition and converse, all derived from the projection above."
  (proj/algebra relation->axes))

(def all-relations
  "The universe of the algebra: the constraint on a pair nothing is known about."
  (:universe relative-algebra))

(def compose
  "The composition of two relation SETS: every relative direction possible from x to z
  when the direction x→y is in `s1` and y→z is in `s2`.  Computed axis-wise — see
  `vaelii.impl.projection`.

  Both relations are read in **one** frame, which is what makes the composition
  legitimate at all: the network they live in is the network of a single context."
  (:compose relative-algebra))

(def converse-set
  "The converse of a relation set — how an asserted `(P a b)` constraint is read backwards
  as the constraint on `(b a)`.  Left becomes right and front-left behind-right;
  coincidence is its own converse."
  (:converse relative-algebra))

;; ---- the vocabulary -----------------------------------------------------

(def base-relation-predicate
  "Base relation keyword → the binary predicate a fact about it is stored under.  `:eq` is
  spelled `sameRelativePositionAs` rather than borrowing the compass's `sameLocationAs`:
  a predicate belongs to exactly one calculus, each network reads only its own vocabulary,
  and this one is a claim about a frame's own axes."
  '{:left         leftOf
    :right        rightOf
    :front        inFrontOf
    :behind       behind
    :front-left   frontLeftOf
    :front-right  frontRightOf
    :behind-left  behindLeftOf
    :behind-right behindRightOf
    :eq           sameRelativePositionAs})

(def relative-denotation
  "Every relative-direction predicate — the nine base ones and the four derived ones —
  mapped to the set of base relations it denotes.  A goal `(P a b)` is entailed exactly
  when the relations still possible from a to b are a *subset* of P's denotation, so a
  derived predicate is entailed by more networks than a base one, and the base predicates
  are the singletons.

  The four derived predicates each constrain one axis and leave the other open:
  `leftwardOf` is anything with a leftward component, whatever it does front-to-back.
  None of them contains `:eq`, so none holds of a thing and itself."
  (merge
   (into {} (map (fn [[rel pred]] [pred #{rel}])) base-relation-predicate)
   '{leftwardOf  #{:left :front-left :behind-left}
     rightwardOf #{:right :front-right :behind-right}
     frontwardOf #{:front :front-left :front-right}
     rearwardOf  #{:behind :behind-left :behind-right}}))

;; ---- the calculus, and the glue it shares with every other algebra -------

(def relative
  "Relative direction as a `vaelii.impl.qcn-kb` calculus — the algebra, the vocabulary,
  and the two caches.  Everything below delegates to the shared glue, which is the same
  code the other calculi run."
  (qkb/calculus :relative relative-algebra relative-denotation))

(defn possible-relative-directions
  "The base relations still possible from `a` to `b` in the frame `context` names, given
  everything believed there — `#{}` when the network is inconsistent."
  [kb context a b]
  (qkb/possible relative kb context a b))

(defn definite-relative-direction
  "The single base relation from `a` to `b` when path consistency pins it down;
  `:inconsistent` when the network contradicts itself, `:unknown` when two or more
  relations remain possible."
  [kb context a b]
  (qkb/definite relative kb context a b))

(defn inconsistent?
  "Is the relative-direction network visible from `context` unsatisfiable?  A frame can be
  incoherent on its own without saying anything about any other."
  [kb context]
  (qkb/inconsistent? relative kb context))

(defn relative-prover
  "The relative-direction entailment prover, to register with `vaelii.core/add-prover`."
  []
  (qkb/prover relative))

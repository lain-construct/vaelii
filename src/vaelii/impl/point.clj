;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.point
  "The point algebra over time **instants** — a relation algebra over the generic
  constraint network in `vaelii.impl.qcn`, and the smallest one there is.  Three base
  relations, jointly exhaustive and pairwise disjoint, so exactly one holds of any two
  instants:

    :before   t(a) < t(b)
    :equal    t(a) = t(b)
    :after    t(a) > t(b)

  `vaelii.impl.interval` is about stretches of time, which have extent and can therefore
  meet, overlap and nest; this is about the moments themselves, where the only question is
  which came first.  The two meet at `vaelii.impl.stp`, which relates an interval to its
  two endpoint instants and puts numbers on the gaps between them.

  **The same algebra appears twice in this tree.**  `vaelii.impl.projection` builds a
  nine-relation algebra out of two independent one-dimensional projections — the cardinal
  directions of `vaelii.impl.orientation` and the relative frame of `vaelii.impl.relative`
  are both that shape — and each projection is exactly these three relations under the
  spellings `:lt` / `:eq` / `:gt`.  The table is duplicated rather than shared: there the
  three relations are a position on an axis and an implementation detail of the algebras
  built over them, here they are an order in time with their own vocabulary, and neither
  namespace should have to read the other's keywords to say what it means.  Nine identical
  entries are cheaper than that coupling, and either copy is checkable against the
  definitions on its own.

  Instants are **stored as ordinary sentexes** — the three named binary predicates
  (`instantBefore`, `instantAfter`, `instantEqual`) plus three derived ones
  (`instantNotBefore`, `instantNotAfter`, `instantNotEqual`) that each name a *disjunction*
  of them.  Instants are ordinary individuals; nothing about them is special, and nothing
  here is about clocks or calendars — only about order.

  The calculus reads every asserted instant relation visible from a context into a
  qualitative constraint network — `{[i j] → #{possible base relations}}`, an unrecorded
  pair meaning \"unknown\", i.e. all three — and `qcn/path-consistent` tightens it to a
  fixpoint.  The prover then answers a goal `(P i j)` by **entailment**: it holds iff every
  relation still possible between i and j satisfies P, `possible ⊆ denotation(P)`.  So
  `(instantBefore A B)` and `(instantBefore B C)` entail `(instantBefore A C)`, and the
  weaker `(instantNotAfter A C)` with it.

  For three relations path consistency is not merely sound but **complete**: the point
  algebra's full disjunctive form is tractable, and a network of it that survives the pass
  has a model.  So an emptied constraint here means genuine unsatisfiability, which is what
  makes a cycle of strict `instantBefore` facts a reportable contradiction rather than a
  suspicion.

  The vocabulary ships in `kb/upper/CxTime.txt` beside the interval relations.  The
  prover is **opt-in** on top of it: register it with `vaelii.core/add-prover`, and until
  then a KB stores and retrieves instant relations as ordinary facts without paying for the
  network."
  (:require [vaelii.impl.qcn-kb :as qkb]))

;; ---- the algebra --------------------------------------------------------

(def all-relations
  "The three jointly-exhaustive, pairwise-disjoint instant relations — the universe of the
  algebra, and so the constraint on a pair nothing is known about."
  #{:before :equal :after})

(def point-converse
  "Each base relation's converse — reading the claim backwards.  One pair and one
  self-converse, since `:equal` is the identity."
  {:before :after, :equal :equal, :after :before})

(defn converse-set
  "The converse of a relation set — how an asserted `(P a b)` constraint is read backwards
  as the constraint on `(b a)`."
  [rels]
  (into #{} (map point-converse) rels))

(def point-composition
  "`(get-in point-composition [r1 r2])` is the set of base relations possible between a and
  c given `r1`(a,b) and `r2`(b,c).  `:equal` is the identity element on both sides.

  Only two entries lose information, and they are the same shape twice: a before b with b
  after c puts both a and c on the far side of b, in either order, so nothing at all
  follows.  Everything else is a singleton — which is why a chain of strict orderings
  composes to a strict ordering however long it is."
  {:before {:before #{:before} :equal #{:before} :after all-relations}
   :equal  {:before #{:before} :equal #{:equal}  :after #{:after}}
   :after  {:before all-relations :equal #{:after} :after #{:after}}})

(defn compose
  "The composition of two relation SETS: every base relation possible between a and c when
  r(a,b) ∈ `s1` and r(b,c) ∈ `s2` — the union of the table entries, since a disjunction on
  either side admits every combination."
  [s1 s2]
  (into #{}
        (mapcat (fn [a] (mapcat (fn [b] (get-in point-composition [a b])) s2)))
        s1))

(def point-algebra
  "The point algebra as a `vaelii.impl.qcn` relation algebra."
  {:universe all-relations
   :identity #{:equal}
   :compose  compose
   :converse converse-set})

;; ---- the vocabulary -----------------------------------------------------

(def base-relation-predicate
  "Base relation keyword → the binary predicate a fact about it is stored under.  Every
  name carries the `instant` prefix: `before` and `after` are already Allen's *interval*
  relations, and a moment ordered against a moment is a different claim from a stretch
  ordered against a stretch.  `:equal` is `instantEqual` for the reason `intervalEqual` is
  not `equals` — two instants coinciding is a claim about time, not about the identity of
  two terms."
  '{:before instantBefore
    :equal  instantEqual
    :after  instantAfter})

(def instant-denotation
  "Every instant predicate — the three base ones and the three derived ones — mapped to the
  set of base relations it denotes.  A goal `(P a b)` is entailed exactly when the relations
  still possible between a and b are a *subset* of P's denotation, so a derived predicate is
  entailed by more networks than a base one, and the base predicates are the singletons.

  The three derived predicates are each the complement of one base relation, and over a
  jointly-exhaustive triple a complement *is* a negation — so the names are literal.
  `instantNotAfter` is ≤ and `instantNotBefore` is ≥, which is what a temporal ordering
  usually wants; `instantNotEqual` is ≠.  With them the vocabulary names every disjunction
  the algebra can express bar the universe, which is the absence of a claim and needs no
  name."
  (merge
   (into {} (map (fn [[rel pred]] [pred #{rel}])) base-relation-predicate)
   '{instantNotAfter  #{:before :equal}
     instantNotBefore #{:after :equal}
     instantNotEqual  #{:before :after}}))

;; ---- the calculus, and the glue it shares with every other algebra -------

(def instants
  "The point algebra as a `vaelii.impl.qcn-kb` calculus — the algebra, the vocabulary, and
  the two caches.  Everything below delegates to the shared glue, which is the same code
  RCC-8, the cardinal directions and Allen's intervals run."
  (qkb/calculus :point point-algebra instant-denotation))

(defn possible-point-relations
  "The base relations still possible between instants `i1` and `i2` given everything
  believed in `context` — `#{}` when the network is inconsistent.

  This is the algebra read directly rather than through a goal, so a caller that needs to
  know *how much* is pinned down — rather than whether one named relation is entailed —
  asks here."
  [kb context i1 i2]
  (qkb/possible instants kb context i1 i2))

(defn definite-point-relation
  "The single base relation between `i1` and `i2` when path consistency pins it down;
  `:inconsistent` when the network contradicts itself, `:unknown` when two or more relations
  remain possible."
  [kb context i1 i2]
  (qkb/definite instants kb context i1 i2))

(defn inconsistent?
  "Is the instant network visible from `context` unsatisfiable?"
  [kb context]
  (qkb/inconsistent? instants kb context))

(defn point-prover
  "The point-algebra entailment prover, to register with `vaelii.core/add-prover`."
  []
  (qkb/prover instants))

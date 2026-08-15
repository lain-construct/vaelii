;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.space
  "RCC-8 qualitative spatial reasoning — a relation algebra over the generic constraint
  network in `vaelii.impl.qcn`, alongside the cardinal directions of
  `vaelii.impl.orientation` and the interval time of `vaelii.impl.interval`.  This one is
  topology: whether two regions touch, overlap or nest, saying nothing about which way
  they lie.

  The eight RCC-8 base relations between two regions are jointly exhaustive and
  pairwise disjoint, so exactly one of them holds of any pair:

    :dc    DC    disconnected
    :ec    EC    externally connected (touching, no shared interior)
    :po    PO    partially overlapping
    :eq    EQ    equal
    :tpp   TPP   tangential proper part      (x inside y, touching the boundary)
    :ntpp  NTPP  non-tangential proper part  (x strictly inside y)
    :tppi  TPPi  the converse of TPP
    :ntppi NTPPi the converse of NTPP

  Spatial knowledge is **stored as ordinary sentexes** — the eight named binary
  predicates (`nonTangentialProperPart`, `externallyConnected`, …), plus six derived
  predicates (`partOfRegion`, `regionOverlaps`, …) that each name a *disjunction* of
  base relations.  Regions are ordinary individuals; nothing about them is special.

  `region-network` reads every asserted spatial relation visible from a context into a
  qualitative constraint network — `{[r1 r2] → #{possible base relations}}`, an
  unrecorded pair meaning \"unknown\", i.e. all eight — and `qcn/path-consistent`
  tightens it to a fixpoint.  the prover then answers a goal `(P r1 r2)` by
  **entailment**: it holds iff every relation still possible between r1 and r2
  satisfies P, `possible ⊆ denotation(P)`.  So `(nonTangentialProperPart A B)` and
  `(nonTangentialProperPart B C)` entail both `(nonTangentialProperPart A C)` (the
  composition table pins the pair to `#{:ntpp}`) and the weaker `(partOfRegion A C)`
  and `(regionOverlaps A C)`, whose denotations are supersets of it.

  An emptied constraint anywhere means the asserted network is spatially inconsistent,
  and then *no* spatial goal is answered — an inconsistent theory should not be mined
  for conclusions.

  **Soundness.** Path consistency is sound, and decides RCC-8 over its maximal
  tractable subclass; on the full language it can leave a network path-consistent yet
  globally unsatisfiable.  So an entailment this prover reports is real, but a
  *non*-entailment means \"not provable\", never \"provably false\".  That is the same
  open-world reading `argIsa` and `exceptWhen` take, and it is what story-scale
  networks need.

  The vocabulary ships as `kb/upper/CxSpace.txt`, an *upper* context rather than
  the vocabulary head: these fourteen predicates are *about* space, so CxCore keeps
  only the grammar they are declared in (`binaryPredicate`, `comment`) and a KB carries
  the subject only if it loads the layer.  The prover is **opt-in** on top of that —
  register it with `vaelii.core/add-prover` — so a KB can store spatial facts and
  retrieve them as ordinary facts without paying for the network."
  (:require [vaelii.impl.qcn-kb :as qkb]))

;; ---- the algebra --------------------------------------------------------

(def all-relations
  "The eight jointly-exhaustive, pairwise-disjoint RCC-8 base relations — the
  universe of the algebra, and so the constraint on a pair nothing is known about."
  #{:dc :ec :po :eq :tpp :ntpp :tppi :ntppi})

(def rcc8-converse
  "Each base relation's converse.  DC/EC/PO/EQ are symmetric; TPP↔TPPi, NTPP↔NTPPi."
  {:dc :dc, :ec :ec, :po :po, :eq :eq,
   :tpp :tppi, :ntpp :ntppi, :tppi :tpp, :ntppi :ntpp})

(defn converse-set
  "The converse of a relation set — how an asserted `(P a b)` constraint is read
  backwards as the constraint on `(b a)`."
  [rels]
  (into #{} (map rcc8-converse) rels))

(def rcc8-composition
  "The RCC-8 composition table: `(get-in rcc8-composition [r1 r2])` is the set of base
  relations possible between x and z given `r1`(x,y) and `r2`(y,z).  The canonical
  Randell–Cui–Cohn table; EQ is the identity element, and PO∘PO is unconstrained."
  {:dc    {:dc    all-relations
           :ec    #{:dc :ec :po :tpp :ntpp}
           :po    #{:dc :ec :po :tpp :ntpp}
           :tpp   #{:dc :ec :po :tpp :ntpp}
           :ntpp  #{:dc :ec :po :tpp :ntpp}
           :tppi  #{:dc}
           :ntppi #{:dc}
           :eq    #{:dc}}
   :ec    {:dc    #{:dc :ec :po :tppi :ntppi}
           :ec    #{:dc :ec :po :tpp :tppi :eq}
           :po    #{:dc :ec :po :tpp :ntpp}
           :tpp   #{:ec :po :tpp :ntpp}
           :ntpp  #{:po :tpp :ntpp}
           :tppi  #{:dc :ec}
           :ntppi #{:dc}
           :eq    #{:ec}}
   :po    {:dc    #{:dc :ec :po :tppi :ntppi}
           :ec    #{:dc :ec :po :tppi :ntppi}
           :po    all-relations
           :tpp   #{:po :tpp :ntpp}
           :ntpp  #{:po :tpp :ntpp}
           :tppi  #{:dc :ec :po :tppi :ntppi}
           :ntppi #{:dc :ec :po :tppi :ntppi}
           :eq    #{:po}}
   :tpp   {:dc    #{:dc}
           :ec    #{:dc :ec}
           :po    #{:dc :ec :po :tpp :ntpp}
           :tpp   #{:tpp :ntpp}
           :ntpp  #{:ntpp}
           :tppi  #{:dc :ec :po :tpp :tppi :eq}
           :ntppi #{:dc :ec :po :tppi :ntppi}
           :eq    #{:tpp}}
   :ntpp  {:dc    #{:dc}
           :ec    #{:dc}
           :po    #{:dc :ec :po :tpp :ntpp}
           :tpp   #{:ntpp}
           :ntpp  #{:ntpp}
           :tppi  #{:dc :ec :po :tpp :ntpp}
           :ntppi all-relations
           :eq    #{:ntpp}}
   :tppi  {:dc    #{:dc :ec :po :tppi :ntppi}
           :ec    #{:ec :po :tppi :ntppi}
           :po    #{:po :tppi :ntppi}
           :tpp   #{:po :eq :tpp :tppi}
           :ntpp  #{:po :tpp :ntpp}
           :tppi  #{:tppi :ntppi}
           :ntppi #{:ntppi}
           :eq    #{:tppi}}
   :ntppi {:dc    #{:dc :ec :po :tppi :ntppi}
           :ec    #{:po :tppi :ntppi}
           :po    #{:po :tppi :ntppi}
           :tpp   #{:po :tppi :ntppi}
           :ntpp  #{:po :tpp :ntpp :tppi :ntppi :eq}
           :tppi  #{:ntppi}
           :ntppi #{:ntppi}
           :eq    #{:ntppi}}
   :eq    {:dc #{:dc} :ec #{:ec} :po #{:po} :tpp #{:tpp}
           :ntpp #{:ntpp} :tppi #{:tppi} :ntppi #{:ntppi} :eq #{:eq}}})

(defn compose
  "The composition of two relation SETS: every base relation possible between x and z
  when r(x,y) ∈ `s1` and r(y,z) ∈ `s2` — the union of the table entries, since a
  disjunction on either side admits every combination."
  [s1 s2]
  (into #{}
        (mapcat (fn [a] (mapcat (fn [b] (get-in rcc8-composition [a b])) s2)))
        s1))

(def rcc8-algebra
  "RCC-8 as a `vaelii.impl.qcn` relation algebra."
  {:universe all-relations
   :identity #{:eq}
   :compose  compose
   :converse converse-set})

;; ---- the vocabulary -----------------------------------------------------

(def base-relation-predicate
  "Base relation keyword → the binary predicate a fact about it is stored under."
  '{:dc    spatiallyDisconnected
    :ec    externallyConnected
    :po    partiallyOverlapping
    :eq    spatiallyEqual
    :tpp   tangentialProperPart
    :ntpp  nonTangentialProperPart
    :tppi  tangentialProperPartInverse
    :ntppi nonTangentialProperPartInverse})

(def spatial-denotation
  "Every spatial predicate — the eight base ones and the six derived ones — mapped to
  the set of base relations it denotes.  A goal `(P r1 r2)` is entailed exactly when
  the relations still possible between r1 and r2 are a *subset* of P's denotation, so
  a derived predicate with a wide denotation is entailed by more networks than a base
  one, and the base predicates are the singletons."
  (merge
   (into {} (map (fn [[rel pred]] [pred #{rel}])) base-relation-predicate)
   '{regionConnectedTo  #{:ec :po :eq :tpp :ntpp :tppi :ntppi}   ; C  — connected
     partOfRegion       #{:tpp :ntpp :eq}                        ; P  — part of
     properPartOfRegion #{:tpp :ntpp}                            ; PP — proper part of
     hasRegionPart      #{:tppi :ntppi :eq}                      ; Pi — has as a part
     regionOverlaps     #{:po :tpp :ntpp :tppi :ntppi :eq}       ; O  — share a part
     regionDiscreteFrom #{:dc :ec}}))                            ; DR — share no part

(def spatial-predicates
  "The predicates the RCC-8 prover claims — the keys of `spatial-denotation`."
  (set (keys spatial-denotation)))

;; ---- the calculus, and the glue it shares with every other algebra -------

(def rcc8
  "RCC-8 as a `vaelii.impl.qcn-kb` calculus — the algebra, the vocabulary, and the two
  caches.  Everything below delegates to the shared glue, which is the same code the
  cardinal directions and the interval algebra run."
  (qkb/calculus :rcc8 rcc8-algebra spatial-denotation))

(defn region-network
  "Every asserted spatial relation visible from `context`, as a constraint network."
  [kb context]
  (qkb/network kb rcc8 context))

(defn possible-relations
  "The RCC-8 base relations still possible between regions `r1` and `r2` given everything
  believed in `context` — `#{}` when the network is inconsistent."
  [kb context r1 r2]
  (qkb/possible rcc8 kb context r1 r2))

(defn definite-relation
  "The single base relation between `r1` and `r2` when path consistency pins it down;
  `:inconsistent` when the network contradicts itself, `:unknown` when two or more
  relations remain possible."
  [kb context r1 r2]
  (qkb/definite rcc8 kb context r1 r2))

(defn inconsistent?
  "Is the spatial network visible from `context` unsatisfiable?"
  [kb context]
  (qkb/inconsistent? rcc8 kb context))

(defn spatial-prover
  "The RCC-8 entailment prover, to register with `vaelii.core/add-prover`."
  []
  (qkb/prover rcc8))

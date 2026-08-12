;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.core-context
  "The CxCore ontology — Vaelii's vocabulary context.  It defines and
  documents the core predicates the engine interprets, as sentexes in CxCore:
  the special-predicate surface (types/contexts, argIsa, disjoint, the `set/*Rule`
  wrappers, the predicate metadata, negation, `ist`, the evaluables) and the
  predicate meta-ontology.  Documentation rides on `comment` sentexes,
  `(comment <term> \"...\")` — ordinary sentexes (stored, indexed, queryable) — so the
  KB documents itself in its own representation.

  The content is a KB file, `resources/kb/CxCore.txt` (read by
  vaelii.impl.seed); this namespace loads it and reads the docs back.

  CxCore is the spindle **head**: the root every context sees, and the only
  layer a core-only KB has.  The layers below it — the definitional `upper`
  contexts (between Core and Universe) and the theory `middle` contexts (between
  Universe and Well) — are the starter's, not the core KB's, and each wires itself
  into the spindle in its own KB file (see vaelii.impl.starter)."
  (:require [vaelii.core :as v]
            [vaelii.impl.seed :as seed]))

(defn load-into
  "Assert the CxCore vocabulary into `kb` from its KB file
  (resources/kb/CxCore.txt). Returns kb.

  The one sentence asserted **before** the file is the topology edge
  `(genlCx CxUniverse CxCore)`, and it is here rather than in the file
  because of *when* it has to hold.  A `decontextualizedPredicate` declaration lifts
  the facts already present into CxUniverse, and a rule stated in CxCore
  fires on the copy — so the two contexts must already be comparable, or that firing
  has no placement and the conclusion is lost.  The file is read term-centrically in
  natural sort order, which would put `genlCx` after `functional`, making which
  meta-ontology conclusions survive a function of predicate spelling.  Asserted first,
  it cannot be."
  [kb]
  (v/assert kb '(genlCx CxUniverse CxCore) 'CxCore)
  (seed/load-context kb 'CxCore))

(defn comment-of
  "The documentation string(s) attached to `term` via comment sentexes."
  [kb term]
  (map (comp #(nth % 2) :sentence)
       (v/sentexes-matching kb (list 'comment term '?text) '?ctx)))

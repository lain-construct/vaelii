;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.starter
  "A starter common-sense KB: a documented, **schema-only** upper + middle ontology.
  It loads the CxCore vocabulary (vaelii.impl.core-context), then the starter's own
  contexts, each a KB file on the classpath under resources/kb/:

    * upper (definitional — between Core and Universe): what things *are*, always
      true, like `genl`.  Split by domain, one context each:
        - CxAbstract.txt — the abstract type skeleton (physical/intangible and
                                their kinds) + the structural relations partOf/locatedIn.
        - CxOrganism.txt — the biological taxonomy + its disjointness.
        - CxLife.txt     — the organism relations (parentOf, siblingOf, flies,
                                mortal, birthYearOf, olderThan, …) with arg + metadata.
        - CxSociety.txt  — the social relations (marriedTo, likes, owns).
        - CxMeasure.txt  — the theory of measurement: the two measure terms, the
                                dimensionOf/conversionFactor table with the units that
                                fill it, the comparisons, and weightOf / heightOf.
        - CxSpace.txt    — qualitative space: RCC-8 region relations (eight base
                                + six derived) and cardinal directions (nine + four).
        - CxTime.txt     — qualitative time: Allen's interval relations (thirteen
                                base + seven derived), plus the length / totalDuration /
                                overlapDuration vocabulary the arithmetic computes over.
    * middle (theory — between Universe and Well): how the definitional things
      *interrelate*, where several overlapping theories can coexist.
        - CxAnatomy.txt   — what kinds of thing have what kinds of part.
        - CxBiology.txt   — birds fly by default except penguins; living things
                                 are mortal; flight enables travel; sleep is what the
                                 theory is willing to assume.
        - CxKinship.txt   — grandparentOf, ancestorOf, olderThan, and parenthood
                                 from maternity and paternity.
        - CxMereology.txt — a part is located where its whole is; owning a whole
                                 entails owning its parts.
        - CxSize.txt      — comparative size: stated between kinds, computed
                                 between objects from their measures.
        - CxSocial.txt    — what acquaintance follows from; employment as one way
                                 of belonging.

  The context spindle is a five-layer axis, most general (top) to most specific
  (bottom): CxCore, the upper layer, CxUniverse, the middle layer,
  CxWell.  Each upper/middle file wires itself into the axis, so the topology is
  data.  **No cast and no contingent facts ship**: the starter is a schema, and
  contingent data (a cast, worked examples, the Aesop fables) belongs below CxWell
  and lives in the tests that need it.

  The unit table is the one place individuals ship, and it applies that rule rather
  than excepting itself from it: a minute is sixty seconds by stipulation, so the
  factor is vocabulary and not a measurement anybody took.  CxMeasure.txt states
  the test it holds a unit to.

  What stays in code here is the *order the layers* load in — loading order is logic,
  the definitional layer must precede the theories that reason over it — and the one
  computed batch (every type is also a unaryPredicate).  Within a layer, every
  context file present is loaded (discovered from the classpath), so adding a KB is
  dropping a file in kb/upper/ or kb/middle/, no code change."
  (:require [vaelii.core :as v]
            [vaelii.impl.core-context :as core-context]
            [vaelii.impl.seed :as seed]
            [vaelii.impl.taxonomy :as tax]))

(defn load-into
  "Populate `kb` with the starter schema — every context under resources/kb/, loaded
  on kb start by default. Returns kb."
  [kb]
  (core-context/load-into kb)                                       ; CxCore.txt: the vocabulary head
  (seed/load-layer kb "upper"  (seed/layer-contexts "upper"))  ; every definitional context
  (seed/load-layer kb "middle" (seed/layer-contexts "middle")) ; every theory context
  ;; every type is a unaryPredicate — computed over the taxonomy, so it stays in code;
  ;; a predicate classification, placed with the others in CxCore
  (doseq [t (sort-by str (tax/types (:taxonomy kb)))]
    (v/assert kb (list 'unaryPredicate t) 'CxCore))
  kb)

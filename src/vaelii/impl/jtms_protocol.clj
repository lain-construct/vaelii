;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.jtms-protocol
  "The representation seam of the truth-maintenance system: the `Tms` protocol
  alone, with no implementation.

  It lives in its own namespace, apart from `vaelii.impl.jtms` (the reference
  network) and `vaelii.impl.dense-jtms` (the dense one), for two reasons.  Both
  implementations depend on it and neither on the other, so the seam is the one
  thing they share.  And it is large — forty-odd methods, each documented — which
  makes the generated protocol map big enough that re-evaluating the form (as
  cloverage does, form by form, to instrument a namespace) overflows the JVM's
  64 KB per-method bytecode limit; isolated here, the protocol is loaded but not
  instrumented while the whole of `vaelii.impl.jtms` still is (scripts/coverage.sh).")

(defprotocol Tms
  "What a truth-maintenance network must answer, independent of how it stores the
  graph.  Two implementations ship: `RefTms` in `vaelii.impl.jtms` — an atom over one
  persistent map, the reference — and `vaelii.impl.dense-jtms`, which holds the same
  graph in bitmaps and primitive-keyed maps.  Selected per KB (`open-kb`'s `:tms` opt),
  dense by default since 0.9.0, and proven to answer identically by `jtms_dense_oracle_test`.

  The seam is at the *representation*, not at the algorithm: both implementations
  run the same least-fixpoint relabel over the same affected region, because that is
  the semantics, not an implementation detail.  What differs is where a node's
  premise flag, depth and adjacency live.

  Every method is named with a leading `-`; the plain names (`in?`, `add-premise`, …)
  are the public functions in `vaelii.impl.jtms`, which dispatch here.  Callers use those."
  (-believed?        [tms datum] "Is `datum` believed (IN, minus supersession)?")
  (-believed         [tms]       "Seq of the believed datums, or nil when none.")
  (-node?            [tms datum] "Is there a node for `datum`?")
  (-datums           [tms]       "Seq of every datum with a node.")
  (-any-node?        [tms]       "Is there any node at all?  A boolean that must not
    materialize the datum seq — `(first (-datums …))` drains the whole dense bitmap
    into boxed Longs, so callers on a render/poll path use this instead.")
  (-any-belief?      [tms]       "Is any datum believed (IN, minus supersession)?  Like
    `-any-node?`, terminates at the first believed datum rather than draining `-believed`.")
  (-depth            [tms datum] "Derivation depth, 0 when unknown.")
  (-premise?         [tms datum] "Is `datum` a premise?")
  (-premise-strength [tms datum] "Its assumption strength, or nil.")
  (-defeat-class     [tms datum] "Defeat-class of an IN datum, nil when OUT.")
  (-defeated         [tms]       "The forced-OUT set.")
  (-blocked          [tms]       "The blocked justification-id set.")
  (-superseded       [tms]       "The `datum -> reason` supersession map.")
  (-touched          [tms]       "Datums whose region was relabelled since the reset.")
  (-touched-in       [tms]       "Of those, the ones already believed when first relabelled.")
  (-touched-new      [tms]       "Datums whose node this window created.")
  (-reset-touched    [tms]       "Clear the touched sets.")
  (-supports         [tms datum] "Justification ids concluding `datum`.")
  (-dependents       [tms datum] "Justification ids using `datum` as an antecedent.")
  (-justification    [tms jid]   "The graph justification (`graph-just` — no bindings), or nil.")
  (-justifications   [tms]       "Every live graph justification.")
  (-ensure-node      [tms datum depth] "Create the node if absent; lower its depth.")
  (-add-premise      [tms datum strength] "Mark `datum` a premise at `strength`.")
  (-suspend-premise  [tms datum] "Drop `datum`'s premise mark and relabel — no sweep.")
  (-add-justification [tms just] "Record `just` and relabel what it moves.")
  (-restrength-informant [tms informant strength]
    "Set `strength` as the rule-contribution slot of every justification whose
    informant is `informant`, and relabel the region their consequences span.")
  (-relabel          [tms]       "Whole-graph relabel — no engine path calls it; see
    `vaelii.impl.jtms/relabel`.")
  (-defeat           [tms datums] "Force `datums` OUT and relabel their region.")
  (-clear-defeats    [tms]       "Empty the defeated set and relabel.")
  (-set-blocked      [tms jids]  "Replace the blocked set and relabel what moved.")
  (-update-blocked   [tms f]     "Apply `f` to the blocked set as one atomic step.")
  (-supersede        [tms m]     "Replace the supersession map (no relabel).")
  (-retract          [tms datum] "Drop the premise, relabel, sweep; return the removals.")
  (-sweep            [tms seeds] "Sweep the consequence closure of `seeds`.")
  (-snapshot         [tms]
    "The whole network as one canonical persistent map — `:nodes :justs :in
    :groundable :defeated :blocked :superseded :classes`.  This is the *comparison*
    shape the differential oracle checks and the shape `RefTms` happens to store; a
    dense implementation materializes it, so it is a debugging and testing surface,
    never something an engine path calls."))

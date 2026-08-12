;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.reindex
  "Rebuild the index store wholesale from the record store.

  Everything the index holds — the trie, the secondary roots, the rule index, the
  exception re-check index, the inverted term index — is *derived* from the
  stored sentexes, so the repair for a damaged or stale index is mechanical:
  clear it and re-derive every entry.  Three situations need it:

  * a crash between the record write and the index pipeline (`assert` spans both
    stores; each side is a single pipeline, but the seam between them remains)
    — the orphaned record is unfindable, and re-asserting its sentence
    would mint a *second* handle for the same canonical form;
  * an index layout change (the leaf/child key split makes an index written in the
    old shape read as empty — fail-safe, but a persistent KB needs this rebuild);
  * any suspicion that counts and extents have drifted: a rebuild is cheaper
    than an audit.

  Run `core/recover` afterwards: it rebuilds the TMS and taxonomy from the
  stores, and parts of that rebuild (`rebuild-taxonomy` reads the functor root)
  read the very index this restores.

  Named bare, like `recover`: the `!` convention marks destruction of stored
  *knowledge*, and this destroys only derived state and recreates it from the
  records, which stay untouched."
  (:require [vaelii.impl.observe :as observe]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]))

(defn- index-rule-entry
  "Register a rule the way `special/index-rule-sentex` does: under all its
  antecedent and consequent predicates, plus the re-check index when it carries an
  `(unknown S)` NAF antecedent.  An `exceptWhen` exception rides a separate
  meta-sentex, re-posted by `index-exceptWhen-entry`.  The recheck *queue* is
  deliberately not touched — that is settle-time state, and the settle after
  `recover` re-evaluates exceptions anyway — which is why this stays a separate fn
  taking the index store rather than a kb.  Kept in lockstep by `reindex_test`'s
  equivalence check."
  [index handle rule-sentex]
  (let [s (:sentence rule-sentex)]
    (p/index-rule index handle
                  (rules/antecedent-predicates s)
                  (rules/consequent-predicate s))
    (when (rules/rechecked? rule-sentex)
      (p/index-exception index handle (rules/recheck-predicates rule-sentex)))))

(defn- index-exceptWhen-entry
  "Register an exceptWhen meta-sentex's exception the way
  `special/index-exceptWhen-meta` does: post the rule it names under each predicate
  its query mentions (and into the `:rules` roster).  No recheck queue, like the rule
  entry above."
  [index meta-sentex]
  (let [rh    (sx/exceptWhen-rule-handle (:sentence meta-sentex))
        preds (rules/watched-predicates
               (sx/exception-query-conjuncts (:sentence meta-sentex)))]
    (when rh (p/index-exception index rh preds))))

(defn index-one!
  "Index one stored sentex `sx` at handle `h` into `index`: its positional / term / root
  entry (`index-sentex`), plus — when `sx` is a rule — the rule-predicate entry, or — when
  it is an `exceptWhen` meta-sentex — the exception entry.  This is the per-sentex core
  `reindex` folds over every live handle, *and* the core the importer's inline bulk load
  calls with the record already in hand, so a rebuilt index and a freshly-loaded one can
  never drift.  Returns true iff `sx` is a rule (the caller's rule tally)."
  [index sx h]
  (p/index-sentex index sx h)
  (let [rule? (rules/rule? sx)]
    (cond
      rule?                                (index-rule-entry index h sx)
      (sx/exceptWhen-meta? (:sentence sx)) (index-exceptWhen-entry index sx))
    rule?))

(defn reindex
  "Flush the index store and rebuild every entry from the stored sentexes.
  Returns {:sentexes n :rules n}."
  [kb]
  (let [records (:records kb)
        index   (:index kb)]
    (p/clear-index! index)
    ;; the index moves wholesale here rather than through the per-sentex choke point, so
    ;; the clock a resident derived structure stamps itself with is bumped by hand — as
    ;; `core/clear!` does, and for the same reason
    (observe/note-change)
    (reduce
     (fn [acc h]
       (if-let [sx (p/get-sentex records h)]
         (cond-> (update acc :sentexes inc)
           (index-one! index sx h) (update :rules inc))
         acc))
     {:sentexes 0 :rules 0}
     (p/sentex-ids records))))

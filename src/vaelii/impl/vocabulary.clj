;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.vocabulary
  "What the engine does with each term of its own grammar — the answer to \"is this
  declaration enforced?\", which is otherwise only readable by grepping `special.clj` and
  `checks.clj`.

  The question exists because nothing about a declaration's *shape* says whether anything
  reads it.  A naming invariant passes on anything correctly spelled, so
  `(maxCardinality parentOf 2)` is a well-formed ternary fact, storable, believed, and
  read by nobody — and a KB author gets identical silence from a constraint that is
  enforced and one that was never implemented.  A roster is what turns that silence into
  an answer.

  **Population: CxCore's own terms.**  Not every predicate in the KB — a domain
  relation is *supposed* to be inert, and `(likes Fred Mary)` asks nothing of the engine.
  CxCore is the vocabulary context, whose charter (see the header of
  `resources/kb/CxCore.txt`) is exactly \"the engine-interpreted special predicates
  and the predicate meta-ontology\", and its file is term-centric: one `(comment <term>
  …)` block per term.  So the terms it comments are precisely the grammar, and precisely
  the set where \"declared but unimplemented\" is a defect rather than the normal case.

  **Two classes, and the distinction is the point.**  `:enforced` means some code path
  reads it and the KB will refuse, derive, or answer differently because of it — the
  string under that key says which path, and whether that path is keyed on this functor
  by name or is a generic mechanism the declaration merely enrols in.  `:inert` means nothing does,
  with `:why` recording that this is a decision rather than an omission: most of the
  inert entries are *derived* predicate types, which exist so a KB can be queried for
  what a mark implies, and are read by no check because the mark itself is what the
  checks read.

  **Where the answer is written.**  Not here: each term's prose sits on its own entry in
  `vaelii.impl.predicates`, beside that term's shape, storage kind and facets, and this
  roster is that field read back.  One entry per term is what stops the answer being a
  second list keyed by the same functors — the failure the declaration namespace exists
  to end — and the *class* is read off the `:facets` rather than off which key the prose
  was written under, so a term the engine demonstrably reads cannot be classified inert
  by writing different prose beside it.

  **What keeps it honest** is `audit`, and two tests over it: a term CxCore comments
  with no roster entry fails, and a roster entry naming a term CxCore no longer
  comments fails.  So the next plausible-looking functor cannot land unimplemented in
  silence, and a retired one cannot leave a stale claim behind.  `:contradicted` is the
  third, and the one that needs no judgement: a functor some data structure in the tree
  proves has behaviour — the special table's keys, the aggregates, the evaluables, the
  rule wrappers — and the roster calls inert is a contradiction, not a matter of
  opinion.

  **Why the answer does not live in the ontology.**  A `(notEnforced P)` marker was the
  obvious alternative and is self-defeating — it would be a declaration the engine does
  not read, which is the exact defect this namespace exists to find.  Putting it in each
  term's `comment` prose is worse: nothing can check prose without matching strings, so it
  would drift the first time a check was added and the sentence was not.  A roster in code
  drifts too, but a test can see it drift."
  (:require [vaelii.impl.predicates :as pr]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.special :as special]))

(def vocabulary-context
  "The context whose terms this roster is about.  `core-context/load-into` names the
  same symbol; it is the one context whose contents are the engine's own grammar."
  'CxCore)

(def roster
  "`term -> {:enforced \"where\"}` or `term -> {:inert \"why\"}`, over every term
  CxCore comments.

  The `:enforced` prose names a code path, so it is the thing to update when one moves —
  and `audit` is what notices when a *term* moves without it.  Both live on the term's
  entry in `vaelii.impl.predicates`; this is that field read back, keyed and shaped the
  way `classify`, `audit` and `core/interpreted` have always read it.

  **The class comes from the facets**, not from which key the prose was written under: a
  term carrying `:cached`, `:convicts`, `:answers` or any other lane is enforced whatever
  is written beside it, and only a term whose facets say `:inert` — which the `inert`
  constructor is the sole way to write — is classified inert.

  **The population is still CxCore's**, and stays a question about the ontology rather
  than about the declaration: an entry carries prose iff CxCore comments the term, so the
  seven grammar terms it does not comment (`equals`, `sameAs`, `functionalInArg` and the
  four query operators) are simply not in here.  A term CxCore starts commenting and
  nobody answers for lands in `audit`'s `:unclassified`, which is the whole mechanism and
  is untouched by the move."
  (into {}
        (keep (fn [[term spec]]
                (when-let [prose (or (:enforced spec) (:inert spec))]
                  [term {(if (contains? (:facets spec) :inert) :inert :enforced) prose}])))
        pr/entries))

(defn classify
  "What the engine does with vocabulary term `term`: `{:enforced \"where\"}`,
  `{:inert \"why\"}`, or nil for a term the roster does not cover.

  Nil is **not** \"nothing reads it\" — the roster's population is CxCore's grammar,
  so an ordinary domain predicate is simply not a term this question is asked about."
  [term]
  (get roster term))

(defn- declared-terms
  "Every term `vocabulary-context` comments — the grammar, read off the loaded KB rather
  than off the file, so the audit is about what this KB has.

  **As stored**, so a `comment` on a defeated declaration still names its term.  The
  audit's question is which grammar terms this KB carries documentation for, and a
  `comment` is documentation rather than a claim about the world: the term is spelled in
  the vocabulary whatever the JTMS currently makes of the sentex that spells it, and a
  believed entry point would report the grammar shrinking whenever a settle moved a belief
  nobody wrote the comment about."
  [kb]
  (into (sorted-set)
        (comp (keep #(p/get-sentex (:records kb) %))
              (filter #(= vocabulary-context (:context %)))
              (keep (fn [s] (let [[_ t] (:sentence s)] (when (symbol? t) t)))))
        (reads/as-stored-with-functor (:index kb) 'comment)))

(def ^:private machine-readable-enforced
  "The functors whose behaviour is provable from a data structure rather than from prose:
  the special-predicate table's own keys, the aggregate roster, the evaluable comparisons,
  and the rule wrappers.  `audit` reports a roster entry that calls one of these inert,
  which is the one kind of wrong answer here that does not need a human to notice — and
  every roster the engine already keeps as data belongs in it, since each one added is a
  claim nobody has to review again."
  (delay (-> #{}
             (into (map first) special/entries)
             (into (keys sx/aggregate-functors))
             (into provers/evaluable-predicates)
             (into (keys sx/rule-direction-wrappers))
             (conj sx/default-rule-wrapper))))

(defn audit
  "Classify every term `vocabulary-context` declares in `kb`:

      {:enforced    [[term \"where\"] …]
       :inert       [[term \"why\"] …]
       :unclassified [term …]      ; declared, and the roster says nothing — the defect
       :retired      [term …]      ; the roster claims a term the KB no longer declares
       :contradicted [term …]}     ; called inert, but the special table gives it an arm

  `:unclassified` is what this exists for: a declaration that landed without anybody
  deciding whether the engine reads it.  `:retired` is the mirror — a claim about a term
  that is gone, which is how a roster goes quietly wrong.  `:contradicted` is the check
  that needs no judgement at all.

  Vectors sorted by term, so two runs over one KB compare."
  [kb]
  (let [declared (declared-terms kb)
        entry    (fn [t] [t (or (:enforced (roster t)) (:inert (roster t)))])]
    {:enforced     (mapv entry (filter #(:enforced (roster %)) declared))
     :inert        (mapv entry (filter #(:inert (roster %)) declared))
     :unclassified (vec (remove roster declared))
     :retired      (vec (remove declared (sort (keys roster))))
     :contradicted (vec (filter #(and (:inert (roster %))
                                      (contains? @machine-readable-enforced %))
                                declared))}))

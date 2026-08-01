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

  **Population: CoreContext's own terms.**  Not every predicate in the KB — a domain
  relation is *supposed* to be inert, and `(likes Fred Mary)` asks nothing of the engine.
  CoreContext is the vocabulary microtheory, whose charter (see the header of
  `resources/kb/CoreContext.txt`) is exactly \"the engine-interpreted special predicates
  and the predicate meta-ontology\", and its file is term-centric: one `(comment <term>
  …)` block per term.  So the terms it comments are precisely the grammar, and precisely
  the set where \"declared but unimplemented\" is a defect rather than the normal case.

  **Two classes, and the distinction is the point.**  `:enforced` means some code path
  reads it and the KB will refuse, derive, or answer differently because of it — the
  `:by` string says which path, and whether that path is keyed on this functor by name or
  is a generic mechanism the declaration merely enrols in.  `:inert` means nothing does,
  with `:why` recording that this is a decision rather than an omission: most of the
  inert entries are *derived* predicate types, which exist so a KB can be queried for
  what a mark implies, and are read by no check because the mark itself is what the
  checks read.

  **What keeps it honest** is `audit`, and two tests over it: a term CoreContext comments
  with no roster entry fails, and a roster entry naming a term CoreContext no longer
  comments fails.  So the next plausible-looking functor cannot land unimplemented in
  silence, and a retired one cannot leave a stale claim behind.  The `:enforced` side is
  cross-checked against `special/entries` as well, which is machine-readable: a functor
  the table gives an arm to and the roster calls inert is a contradiction, not a matter of
  opinion.

  **Why the answer does not live in the ontology.**  A `(notEnforced P)` marker was the
  obvious alternative and is self-defeating — it would be a declaration the engine does
  not read, which is the exact defect this namespace exists to find.  Putting it in each
  term's `comment` prose is worse: nothing can check prose without matching strings, so it
  would drift the first time a check was added and the sentence was not.  A roster in code
  drifts too, but a test can see it drift."
  (:require [vaelii.impl.protocols :as p]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.special :as special]))

(def vocabulary-context
  "The microtheory whose terms this roster is about.  `core-context/load-into` names the
  same symbol; it is the one context whose contents are the engine's own grammar."
  'CoreContext)

(def roster
  "`term -> {:enforced \"where\"}` or `term -> {:inert \"why\"}`, over every term
  CoreContext comments.

  The `:by` prose names a code path, so it is the thing to update when one moves — and
  `audit` is what notices when a *term* moves without it."
  '{;; ---- the taxonomy relations, cached rather than chained ----------------
    genl        {:enforced "taxonomy/add-genl — the cached closure every membership, match and placement reads"}
    genlContext {:enforced "taxonomy/add-genlContext — the visibility closure a context read walks"}
    thing       {:enforced "checks — the hierarchy root the open-world floors test against by name"}
    predicate   {:enforced "generic: the argIsa target CoreContext constrains its own meta-level with"}

    ;; ---- the definitional constraints -------------------------------------
    argIsa      {:enforced "checks/args-problem — refuses on the way in, and entails under *assertive-arg-types?*"}
    argGenl     {:enforced "checks/genls-problem — the same, one level up"}
    interArgIsa {:enforced "checks/inter-args-problem — the conditional form, same two paths"}
    arity       {:enforced "checks/arity-problem at the door, settle/report-arity-reach! over content stored before it"}
    disjoint    {:enforced "taxonomy/add-disjoint, read by checks/disjoint-problems and arbitrated by settle"}
    disjointMetatype {:enforced "taxonomy/mark-disjoint-metatype — the clique consulted, never stored"}
    functional  {:enforced "checks/functional-problems, and special/derive-functional-equalities on two symbols"}
    asymmetric  {:enforced "checks/asymmetry-problem — a nogood against the converse"}
    variableArity {:enforced "checks/arity-problem — the one exemption from the arity check"}
    relationKind  {:enforced "generic: a disjointMetatype, so its two members separate each other"}
    instanceRelationPredicate {:enforced "checks/declaration-problem — an argGenl on one is refused"}
    typeRelationPredicate     {:enforced "checks/declaration-problem — an argIsa on one is refused"}
    unaryPredicate   {:enforced "checks/predicate-type-arities — the membership spelling of an arity"}
    binaryPredicate  {:enforced "checks/predicate-type-arities — the membership spelling of an arity"}
    ternaryPredicate {:enforced "checks/predicate-type-arities — the membership spelling of an arity"}

    ;; ---- predicate metadata answered by a prover --------------------------
    transitive  {:enforced "taxonomy prop :transitive — the generic closure prover"}
    symmetric   {:enforced "taxonomy prop :symmetric — canonical argument order, so both spellings are one sentex"}
    reflexive   {:enforced "taxonomy prop :reflexive — the reflexive prover"}
    inverse     {:enforced "taxonomy/add-inverse — the prover that hands the swapped goal back"}
    argPreserving        {:enforced "inherit — the argument reach along a declared transitive relation"}
    argPreservingInverse {:enforced "inherit — the same, read backwards"}
    abduciblePredicate   {:enforced "taxonomy prop :abducible — the gate on what abduce may hypothesize"}

    ;; ---- placement and lifting --------------------------------------------
    decontextualizedPredicate       {:enforced "special — the UniverseContext lift, retroactive over the extent"}
    forcedDecontextualizedPredicate {:enforced "special — storage straight into UniverseContext"}
    ist  {:enforced "assert and rule placement — never stored, it names where the sentence goes"}

    ;; ---- the connectives and rule wrappers, read by the canonicalizer -----
    implies {:enforced "sentex canonicalization — becomes the antecedent/consequent slots of a RuleSentex"}
    and     {:enforced "sentex canonicalization — the antecedent conjunction, never stored alone"}
    not     {:enforced "sentex canonicalization — the truth slot, and the negation nogoods"}
    set/forwardRule  {:enforced "sentex/peel-rule-wrapper — sets the rule's direction"}
    set/backwardRule {:enforced "sentex/peel-rule-wrapper — sets the rule's direction"}
    set/defaultRule  {:enforced "sentex/peel-rule-wrapper — sets the conferred strength"}
    set/inertRule    {:enforced "sentex/peel-rule-wrapper — stored, indexed for neither direction"}

    ;; ---- the query operators, answered and never stored -------------------
    evaluate    {:enforced "the evaluable prover — a whitelist over the arithmetic operators"}
    lessThan    {:enforced "the comparison prover, plus the chain collapse in a rule body"}
    greaterThan {:enforced "the comparison prover — canonicalizes to lessThan reversed"}
    agg/count   {:enforced "the aggregate prover"}
    agg/sum     {:enforced "the aggregate prover"}
    agg/avg     {:enforced "the aggregate prover"}
    agg/min     {:enforced "the aggregate prover"}
    agg/max     {:enforced "the aggregate prover"}

    ;; ---- reified terms ----------------------------------------------------
    reifiableFunction   {:enforced "taxonomy prop :reifiable — the gate that turns the nat reify pass on"}
    unreifiableFunction {:enforced "taxonomy prop :unreifiable — kept structural for a prover to compute"}
    termOfUnit  {:enforced "nat — the constant-to-expression half of the reified-term map"}
    rewriteOf   {:enforced "nat for a compound right side, the equality partition for a symbol"}
    resultIsa   {:enforced "nat — materialized as a membership on each minted constant"}
    resultGenl  {:enforced "nat — materialized as a genl edge on each minted constant"}
    functionCorrespondingPredicate
    {:enforced "nat — reifies an application to the value the predicate already names, and projects a minted constant back onto it"}

    ;; ---- documentation ----------------------------------------------------
    comment     {:enforced "gloss, core-context/comment-of, and the browser's term pages — ordinary sentexes, queried like any fact"}

    ;; ---- declared and read by nothing, on purpose -------------------------
    contradicts {:inert "a report form the engine *writes*: conflicts and contradictions compose it per settle. Nothing reads it as input, and asserting one would put a stale claim under truth maintenance."}
    typeToInstancePred {:inert "a link, not a rule. Moving a claim between the type and instance levels needs a quantifier reading nothing here fixes, so the pairing is recorded for a reader and inferred from by nobody."}
    functionalPredicate  {:inert "a derived predicate type, so a KB can be queried for what the mark implies. The checks read (functional P); this is its consequence, not its cause."}
    symmetricPredicate   {:inert "a derived predicate type — see functionalPredicate."}
    transitivePredicate  {:inert "a derived predicate type — see functionalPredicate. (transitivePredicate genl) is asserted so genl can be named as a preserved-along relation, which inherit reads through the taxonomy rather than through this type."}
    reflexivePredicate   {:inert "a derived predicate type — see functionalPredicate."}
    asymmetricPredicate  {:inert "a derived predicate type — see functionalPredicate."}})

(defn classify
  "What the engine does with vocabulary term `term`: `{:enforced \"where\"}`,
  `{:inert \"why\"}`, or nil for a term the roster does not cover.

  Nil is **not** \"nothing reads it\" — the roster's population is CoreContext's grammar,
  so an ordinary domain predicate is simply not a term this question is asked about."
  [term]
  (get roster term))

(defn- declared-terms
  "Every term `vocabulary-context` comments — the grammar, read off the loaded KB rather
  than off the file, so the audit is about what this KB has."
  [kb]
  (into (sorted-set)
        (comp (keep #(p/get-sentex (:records kb) %))
              (filter #(= vocabulary-context (:context %)))
              (keep (fn [s] (let [[_ t] (:sentence s)] (when (symbol? t) t)))))
        (p/sentexes-with-functor (:index kb) 'comment)))

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

;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.rules
  "A rule *is* a sentex — same structure (sentence + context), different indexing.
  Its sentence is an implication:

    (implies (and <antecedent> ...) <consequent>)     ; single antecedent needs no `and`

  Antecedents and consequent are sentence patterns that may contain variables.
  Rules are indexed by their antecedent/consequent predicates (see the index
  store) so forward chaining finds candidate rules without scanning, and — being
  ordinary sentexes — they get handles, TMS support, and retraction for free.

  Rules must be range-restricted: every consequent variable appears in some
  antecedent, so a fired consequent is ground.  The one exemption is a **head
  existential** — a consequent variable explicitly marked `(exists ?y C)`, which
  forward firing skolemizes to a deterministic constant (docs/skolem.md); range
  restriction permits only the marked variable and still rejects any *accidentally*
  unbound one.  The same closure is required of an `exceptWhen` exception, which is a
  query rather than a conclusion but must be ground for the same reason (checked at the
  assert layer via `sentex/check-exception-closed`)."
  (:require [vaelii.impl.naming :as nm]
            [vaelii.impl.sentex :as sx]))

;; The rule *form* — its functor, its parts, its builder — has one owner:
;; `vaelii.impl.sentex`, whose constructor both parses and rebuilds it, so its
;; spelling decisions are the stored spelling.  The names below are delegations
;; kept for this namespace's readers; the dependency direction — rules already
;; requires sentex for the wrapper tables, peeling, and exception machinery —
;; decides which namespace owns the form.

(def rule-functor sx/rule-functor)

(defn rule-sentence?
  "Is `sentence` a rule form `(implies <ante> <conseq>)`?"
  [sentence]
  (sx/implies? sentence))

(defn rule? [sentex] (rule-sentence? (:sentence sentex)))

(defn antecedents
  "The antecedent patterns of a rule sentence (unwrapping a leading `and`)."
  [sentence]
  (sx/rule-antecedents sentence))

(defn consequent [sentence] (sx/rule-consequent sentence))

(defn rule-sentence
  "Build a rule sentence from antecedent patterns and a consequent pattern.
  One spelling for the whole codebase — see `sentex/rule-sentence`."
  [antecedents consequent]
  (sx/rule-sentence antecedents consequent))

(defn parse [sentence]
  {:antecedents (antecedents sentence) :consequent (consequent sentence)})

(defn antecedent-predicates [sentence] (keep nm/functor (antecedents sentence)))

(defn consequent-predicate
  "The predicate a rule concludes.  A consequent of the form `(ist Ctx S)` (place S
  into context Ctx) is indexed by S's predicate, not by ist."
  [sentence]
  (let [c (consequent sentence)]
    (if (and (sequential? c) (= sx/ist-functor (first c)))
      (nm/functor (nth c 2))
      (nm/functor c))))

;; ---- virtual rule-direction predicates ----------------------------------
;; Wrapping a rule sets its inference direction on assert.  Default (a bare
;; implies) is :both; :forward indexes only by antecedent, :backward only by
;; consequent, :inert not at all (documentation).

(defn forward?  [direction] (contains? #{:forward :both} direction))
(defn backward? [direction] (contains? #{:backward :both} direction))

(defn forward-sentex?
  "Does this stored rule sentex forward-chain?  Read off the record, which carries
  the direction its `set/*Rule` wrapper set.  An `assumptionRule` (a choice head) and a
  `hard`/`softConstraint` (a contradiction marker) never chain — their heads are decided
  or forbidden by a solve, not derived — so they are inference-inert in both directions
  regardless of the direction they were written with."
  [sentex] (and (not (:assumption sentex)) (not (:constraint sentex))
                (forward? (:direction sentex))))

(defn backward-sentex?
  "Does this stored rule sentex backward-chain?  An `assumptionRule` / constraint rule
  does not (see `forward-sentex?`)."
  [sentex] (and (not (:assumption sentex)) (not (:constraint sentex))
                (backward? (:direction sentex))))

;; ---- exceptWhen: the rule states its own exception ------------------------
;; `(exceptWhen <query> <rule>)` blocks: for a binding its query holds of, the rule
;; does not conclude.  The exception is *not* part of the rule record — it is a
;; separate belief-following meta-sentex `(exceptWhen <query> (sentexHandle H))`
;; naming the rule by handle (`sentex/exceptWhen-meta`); the engine reads a rule's
;; exceptions through `provers/rule-exceptions`, and their predicates are registered
;; in the re-check index by the meta-sentex's own indexing (`special`).  See
;; docs/exceptions.md.

(defn assumption?
  "Is this stored rule sentex a `set/assumptionRule` — a choice rule whose head a solve
  decides rather than the chainer deriving?  Read straight off the record's
  `:assumption` field, like `:defeasible` (docs/solving.md)."
  [sentex] (boolean (:assumption sentex)))

(defn constraint-of
  "The constraint class of this stored rule sentex — `:hard` / `:soft` from its
  `set/hardConstraint` / `set/softConstraint` wrapper, or nil for an ordinary rule.
  Read straight off the record's `:constraint` field (docs/solving.md)."
  [sentex] (:constraint sentex))

(defn constraint?
  "Is this stored rule sentex a `set/hardConstraint` / `set/softConstraint` — a
  contradiction rule whose conjunctive body a solve grounds into a nogood?"
  [sentex] (boolean (:constraint sentex)))

;; ---- negation as failure: `unknown` antecedents --------------------------
;; An `(unknown S)` antecedent is closed-world negation inline in the rule body, the
;; per-literal cousin of `exceptWhen`: the rule does not conclude for a binding under
;; which `S` is derivable.  Like an exception it is re-evaluated (never stored) and
;; drives the same block / sweep / revive machinery — so the accessors below mirror
;; the exception ones, and `special`/`settle` read both.  (A standalone positive
;; `thereExists` is desugared away in the sentex constructor, so it is an ordinary
;; antecedent here, not a NAF one.)  See docs/naf.md.

(defn naf-antecedents-of
  "The `(unknown S)` antecedent literals of a raw rule *sentence* — for the checks
  that run before a rule is stored as a sentex (stratification)."
  [rule-sentence]
  (filter sx/unknown? (antecedents rule-sentence)))

(defn naf-antecedents
  "The `(unknown S)` antecedent literals of a stored rule — its negation-as-failure
  conditions."
  [sentex]
  (naf-antecedents-of (:sentence sentex)))

(defn has-naf?
  "Does this rule carry any `unknown` antecedent?"
  [sentex]
  (boolean (seq (naf-antecedents sentex))))

(defn- naf-query
  "The query literal inside an `(unknown …)` antecedent — its argument, unwrapped past
  a `thereExists` so the predicate a re-check keys on is the one the level-6 query
  actually runs (`(unknown (thereExists ?x (parentOf ?x Tom)))` watches `parentOf`)."
  [unk]
  (let [s (second unk)]
    (if (sx/there-exists? s) (nth s 2) s)))

(defn naf-predicates-of
  "The predicates a raw rule *sentence*'s `unknown` antecedents mention — for the
  stratification check on a rule not yet stored (the mirror of the exception's
  negative dependence)."
  [rule-sentence]
  (keep #(nm/functor (naf-query %)) (naf-antecedents-of rule-sentence)))

(defn naf-predicates
  "The predicates a rule's `unknown` antecedents mention — the keys the re-check index
  posts the rule under, so a fact arriving or leaving on one re-evaluates the NAF
  condition.  The exception analogue is `exception-predicates`; both feed the same
  `[:exception-index …]` index."
  [sentex]
  (naf-predicates-of (:sentence sentex)))

(defn naf-queries
  "The inner query literals of a rule's `unknown` antecedents (each unwrapped past a
  `thereExists`), so the settle-time firing filter can shape them against a trigger
  exactly as it shapes an exception's conjuncts — the ground ones narrow, the
  existential ones fall through to 'keep' like any non-flat conjunct."
  [sentex]
  (map naf-query (naf-antecedents sentex)))

;; ---- aggregation: a rule antecedent that counts --------------------------
;; An aggregate antecedent is the other non-monotonic literal a rule body can carry:
;; `(agg/count ?n ?v S)` binds `?n` to a function of what is *believed*, so a
;; fact arriving on `S`'s predicate can withdraw a firing that rested on the old
;; count.  That is `unknown`'s maintenance problem exactly, so it takes `unknown`'s
;; machinery — the same re-check index, the same settle-time re-evaluation, the same
;; negative edge in the stratification graph.  See docs/aggregate.md.

(defn aggregate-antecedents-of
  "The aggregate antecedent literals of a raw rule *sentence* — for the checks that
  run before a rule is stored as a sentex (stratification)."
  [rule-sentence]
  (filter sx/aggregate? (antecedents rule-sentence)))

(defn aggregate-antecedents
  "The aggregate antecedent literals of a stored rule."
  [sentex]
  (aggregate-antecedents-of (:sentence sentex)))

(defn has-aggregate?
  "Does this rule carry any aggregate antecedent?"
  [sentex]
  (boolean (seq (aggregate-antecedents sentex))))

(defn aggregate-queries
  "The body queries of a rule's aggregate antecedents, so the settle-time firing
  filter can shape them against a trigger exactly as it shapes an exception's
  conjuncts.  Each mentions the reduction variable by construction, so none of them is
  ground and every one falls through to 'keep' — an aggregate's firings are never
  narrowed away, which is the safe direction."
  [sentex]
  (map sx/aggregate-body (aggregate-antecedents sentex)))

(defn aggregate-predicates-of
  "The predicates a raw rule *sentence*'s aggregate bodies mention — the negative-edge
  keys the stratification graph reads, and the re-check keys the index posts under."
  [rule-sentence]
  (keep #(nm/functor (sx/aggregate-body %)) (aggregate-antecedents-of rule-sentence)))

(defn aggregate-predicates
  "The predicates a stored rule's aggregate bodies mention."
  [sentex]
  (aggregate-predicates-of (:sentence sentex)))

(defn recheck-predicates
  "The predicates whose change must re-check this rule for its **own** re-check
  conditions — the predicates its `unknown` antecedents and its **aggregate** bodies
  mention.  (An exceptWhen exception is a separate meta-sentex, registered under its
  rule by the meta-sentex's own indexing; it is not read off the rule.)  The key set
  the `[:exception-index …]` index posts a rule under when it is indexed.

  The two kinds are one key set because they are one problem: both read what the KB
  believes at firing time rather than a fact the justification names, so both need a
  fact arriving on those predicates to bring the firing back for re-decision."
  [sentex]
  (distinct (concat (naf-predicates sentex) (aggregate-predicates sentex))))

(defn rechecked?
  "Does this rule carry a re-check condition of its **own** — an `unknown` antecedent
  or an aggregate?  The gate on registering it in the re-check index; an exceptWhen
  exception is registered by its own meta-sentex and is not read off the rule."
  [sentex]
  (or (has-naf? sentex) (has-aggregate? sentex)))

;; ---- what the join cannot do, and the placement can ----------------------
;; An aggregate is evaluated per **placement context**, not in the join, because a
;; census depends on where it is taken and the join does not yet know where the
;; conclusion lands.  So its `?n` is unbound for the whole join — and that reaches
;; further than the aggregate itself: a `(lessThan 2 ?n)` written after it is a
;; *computed* literal, so it has no fact to match and nothing to wait for, and the
;; chainer refuses to run it against an unbound input rather than report a comparison
;; that never ran as one that failed.
;;
;; The answer is that such a literal is not a join literal at all.  It moves to the
;; placement phase with the aggregate that feeds it, where `?n` exists — which is also
;; the context the backward chainers evaluate it in, so the three agree.

(defn post-join-literals
  "The antecedent literals evaluated **after** the join: every aggregate, plus every
  deferred literal reading a variable an aggregate produces — or that one of *those*
  produces in turn, so an `(evaluate ?d (+ ?n 1))` carries a later `(lessThan ?d 9)`
  along with it.

  **In written order**, which is the order they run in, because a computed literal
  reads what is written before it.  That is not a rule aggregates introduce: an
  `evaluate` chain has always had to be written downhill, since canonical order holds a
  deferred literal in the author's position and every chainer runs it there.  Making an
  aggregate an exception — reordering the phase so a comparison could be written above
  its own count — is what a *forward* chainer could do and a backward one could not, so
  it would buy convenience at the price of the two disagreeing about one rule.
  `sentex/check-naf-closed` refuses the uphill writing instead.

  `unknown` is deliberately not here: it binds nothing, so it never needs the ordering,
  and it is already evaluated per placement as `:naf`.

  Asked on **every** join, so the gate is a short-circuiting `some` that allocates
  nothing: no aggregate, no post-join phase, and the overwhelming majority of rules
  have none."
  [antes]
  (if-not (some sx/aggregate? antes)
    []
    (:out (reduce (fn [{:keys [produced out] :as acc} a]
                    (if (or (sx/aggregate? a)
                            (and (sx/deferred-literal? a)
                                 (not (sx/unknown? a))
                                 (some produced (sx/deferred-input-vars a))))
                      {:produced (into produced (sx/deferred-output-vars a))
                       :out      (conj out a)}
                      acc))
                  {:produced #{} :out []}
                  antes))))

(defn post-join-antecedents
  "`post-join-literals` over a stored rule's antecedents."
  [sentex]
  (post-join-literals (vec (antecedents (:sentence sentex)))))

(def ^:private direction-wrapper
  (into {} (map (fn [[w d]] [d w])) sx/rule-direction-wrappers))

(defn wrap-direction
  "Express `direction` as the corresponding `set/*Rule` wrapper around `sentence`.
  `:both` needs no wrapper — a bare `(implies …)` already works both ways."
  [sentence direction]
  (if-let [w (direction-wrapper direction)] (list w sentence) sentence))

(defn inner-rule
  "The bare `(implies …)` inside any virtual rule wrappers (`set/*Rule` and
  `exceptWhen`, which may nest in any order — a defeasible forward rule with an
  exception).  The direction / default / assumption wrappers become record fields and
  the exceptWhen becomes a meta-sentex, so the checks and the stored sentence both work
  on this."
  [sentence]
  (let [[_ _ _ _ _ inner] (sx/peel-rule-wrapper sentence)] inner))

;; ---- polycanonicalization: split a conjunctive consequent ----------------

(defn- conjunctive? [c] (and (sequential? c) (= 'and (first c))))

(defn rewrap
  "Put the direction / default / assumption / constraint wrappers a rule was written
  with back around `sentence` — the inverse of `sx/peel-rule-wrapper`, since the
  wrappers ride the record, not the stored sentence.  Two callers: a polycanonicalized
  conjunct keeps the mode of the rule it came from, and an equality merge's migrated
  rule twin keeps the mode of the rule it restates (`special/migrate-sentex`).  An
  exceptWhen is not among them — it is split off before this runs and stored as a
  meta-sentex against each conjunct's handle (`split-exceptWhen`)."
  [sentence direction defeasible assumption constraint]
  (cond-> sentence
    defeasible      (->> (list sx/default-rule-wrapper))
    assumption      (->> (list sx/assumption-rule-wrapper))
    constraint      (->> (list (get {:hard 'set/hardConstraint :soft 'set/softConstraint}
                                    constraint)))
    direction       (wrap-direction direction)))

(defn expand-consequent
  "Polycanonicalize a rule that concludes a conjunction into one rule per conjunct,
  preserving any virtual wrapper (default / forward / backward / inert / assumptionRule).
  A rule `(implies A (and C1 C2))` becomes `[(implies A C1) (implies A C2)]`; anything
  else (a non-rule, or a rule with a single consequent) returns `[sentence]` unchanged.

  Runs on a rule whose exceptWhen has already been split off (`split-exceptWhen`), so
  the exception is re-attached once per conjunct by the caller, against each conjunct's
  own handle."
  [sentence]
  (let [[dir def? _exc assum con inner] (sx/peel-rule-wrapper sentence)]
    (if (and (rule-sentence? inner)
             (conjunctive? (consequent inner)) (seq (rest (consequent inner))))
      (let [as (antecedents inner)]
        (mapv #(rewrap (rule-sentence as %) dir def? assum con) (rest (consequent inner))))
      [sentence])))

(defn split-exceptWhen
  "Split an `(exceptWhen <query> <rule>)` assertion into `[exception inner]`.

  `exception` is the flattened conjunction of every exceptWhen wrapper (a vector of
  literals in the author's variable names, block-if-all-hold), and `inner` is what the
  exceptWhen qualifies: the wrapped rule with its exceptWhen(s) stripped but its
  direction / default / assumption wrappers intact, or the `(sentexHandle H)` a
  bare-handle exceptWhen named.  `[nil sentence]` when there is no exceptWhen.

  This is the layer at which an exceptWhen becomes a separate meta-sentex: the assert
  layer stores `inner` as the rule (or resolves the handle) and the exception as
  `(exceptWhen <aligned-query> (sentexHandle H))` against it."
  [sentence]
  (let [[dir def? exc assum con inner] (sx/peel-rule-wrapper sentence)]
    (if (seq exc)
      [(vec exc) (if (sx/sentex-handle? inner) inner (rewrap inner dir def? assum con))]
      [nil sentence])))

(defn- deep-vars
  "Every variable anywhere in a form (descends into nested subterms, so an ist
  consequent's inner sentence and its context slot are both covered)."
  [form]
  (filter sx/variable? (tree-seq sequential? seq form)))

(defn range-problems
  "Why `antecedents => consequent` is not range-restricted, as a seq of problem
  strings — empty when the rule is fine.  The value form, like the wff arms:
  a caller that refuses wraps it in a throw, and a fixpoint that must not abort
  can record it instead.

  A head existential `(exists ?y C)` exempts **only** its marked variable(s): the
  check runs over the inner `C`, and every consequent variable that is neither
  antecedent-bound nor existentially marked is still a problem — so an accidental
  typo is caught while a deliberate `∃` is allowed (docs/skolem.md)."
  [antecedents consequent]
  (let [exists?   (sx/head-exists? consequent)
        evars     (if exists? (sx/head-exists-vars consequent) #{})
        cbody     (if exists? (sx/head-exists-body consequent) consequent)
        cvars     (deep-vars cbody)
        ante-vars (into #{} (mapcat deep-vars antecedents))]
    (cond-> []
      (and (sequential? cbody) (= 'and (first cbody))
           (empty? (rest cbody)))
      (conj "rule consequent is an empty conjunction")

      ;; `_` is an anonymous wildcard: two occurrences are two *different* variables
      ;; (canonicalization numbers each one separately), so it can never carry a
      ;; binding from an antecedent to the consequent — matching one against another
      ;; would store a non-ground junk fact.
      (some #(= '_ %) cvars)
      (conj "rule consequent uses the anonymous wildcard _, which binds nothing")

      :always
      (into (for [v (distinct cvars)
                  :when (and (not= '_ v) (not (ante-vars v)) (not (evars v)))]
              (str "rule is not range-restricted: consequent variable " v
                   " is unbound by the antecedents"))))))

(defn check-range-restricted
  "Throw `:type :not-range-restricted` unless every consequent variable is bound by
  some antecedent (and the consequent is a well-formed conclusion).

  Uses `ex-info`, not `clojure.core/assert`: an elidable check under `*assert*` false
  would store the junk rule *silently* — the exact failure `check-ground` exists to
  prevent — and an `AssertionError` carries no `:type` for callers to discriminate
  on."
  [antecedents consequent]
  (when-let [problems (seq (range-problems antecedents consequent))]
    (throw (ex-info (first problems)
                    {:type        :not-range-restricted
                     :problems    (vec problems)
                     :antecedents (vec antecedents)
                     :consequent  consequent}))))

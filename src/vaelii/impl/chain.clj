;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.chain
  "Forward chaining: the semi-naive fixpoint, one agenda for bare and defeasible
  rules alike, with the definitional checks re-run on the derivation path and the
  `exceptWhen` guard consulted before a conclusion is placed.

  Fifth layer of the engine stack (kb <- checks <- special <- integrate <- chain
  <- settle): a firing joins antecedents against stored facts (kb), checks its
  conclusion (checks), and reflects what it places into the caches through the
  derivation-path choke point (special).  Belief settling happens *after* a run,
  in `vaelii.impl.settle` — nothing here defeats or arbitrates."
  (:require [taoensso.trove :as trove]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.plan :as plan]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.qcn-kb :as qkb]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.skolem :as skolem]
            [vaelii.impl.special :as special]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.violations :as violations]))

(def default-chain-opts
  "max-depth bounds derivation depth to catch productive infinite recursion;
  max-derivations is a hard backstop on a single chain run."
  {:max-depth 64 :max-derivations 100000})

(def ^:private default-progress-ms
  "How long a run may go without reporting, unless `opts` says otherwise
  (`:progress-every-ms`).  The interval is **wall-clock rather than a datum count**,
  because the two are not proportional: most datums are a fact triggering nothing and cost
  microseconds, while one rule datum joins over the whole corpus and can hold the loop for
  a minute on its own.  Counting datums would report thousands of times a second through
  the cheap stretch and go silent through the expensive one — which is the stretch a
  reader is watching."
  250)

(def ^:private ^:dynamic *tick*
  "Called by `derive-conclusion` after each rule firing with how many sentexes it created,
  or nil outside a reporting run.  This is what makes a *single* long datum visible: the
  agenda loop only sees a datum once it is finished, and the rule datum that fires over a
  whole corpus is one datum.  Bound by `chain` for the length of the run."
  nil)

(def ^:dynamic *matcher*
  "How the forward join looks up the stored facts satisfying a **non-trigger**
  antecedent — `(fn [kb pattern context] -> seq of [handle bindings …])`, returning
  exactly what `res/match-pattern` does.

  The default is `res/match-pattern` (the count-aware trie), which is the reference
  path and leaves forward chaining unchanged.  `vaelii.impl.rete` binds this to a RAM
  alpha-memory matcher that answers the same set through an index on argument values,
  so a non-trigger antecedent with a leading variable — `(parentOf ?x Pi)` — is a
  hash lookup rather than a full functor scan.  The *set* it returns is identical
  (proven by the rete oracle), so every downstream behaviour is the reference's; only
  the candidate lookup changes.  This is the sole seam the incremental matcher needs,
  because the trigger match (`match1`) is already selective and everything else —
  placement, exceptions, the definitional checks, justification dedup — is reused
  verbatim.  See docs/inference.md, \"Incremental rule matching\"."
  res/match-pattern)

;; ---- exceptWhen: evaluating the exception -------------------------------
;; The exception is **any closed level-6 query** once the rule's bindings are
;; substituted in.  Level 6 (`:solved`) is the full prover stack *minus* rule
;; backchaining, so an exception reaches through genl specificity, the genlContext
;; visibility closure, the transitive / symmetric / inverse metadata, disjointness and
;; the evaluables — but never invokes an unbounded proof search from inside the
;; relabel loop.  See docs/exceptions.md, "The exception is a query, not a literal".

(defn exception-holds?
  "Does `except` — a rule's exception, a vector of literals — hold under `bindings`,
  evaluated in `pctx`, the context the conclusion would be placed in?

  Three properties make this cheap, and each is load-bearing:

  * **Closed.**  Every exception variable is bound by an antecedent (enforced in the
    `sentex` constructor), so substitution leaves a *ground* question.  The conjuncts
    therefore share nothing and need no join — each is an independent existence check,
    and **all** must hold.
  * **One answer suffices.**  The levels stack is lazy throughout, so `first` stops
    the query at its first result rather than enumerating an extent.
  * **An unanswerable exception does not hold**, and the rule fires.  That is the
    open-world reading, and it matches `argIsa`, where an argument whose type is
    unknown cannot violate a constraint: blocking on \"cannot tell\" would let a
    missing fact silently suppress knowledge.

  An empty / absent exception never holds, so an ordinary rule takes no cost here.

  Defined in `vaelii.impl.provers` because the backward chainers need exactly the same
  judgement; `pctx` here is the conclusion's placement context, where backward passes
  the query's."
  [kb except bindings pctx]
  (provers/exception-holds? kb except bindings pctx))

;; ---- negation-as-failure antecedents ------------------------------------
;; An `(unknown S)` antecedent is `exceptWhen` inlined per-literal: the rule does not
;; conclude for a binding under which `S` is derivable.  It shares the exception's
;; evaluator — a closed level-6 existence check — and its whole block / sweep / revive
;; machinery, differing only in polarity and combination: each `unknown` is an
;; *independent* block condition (block if **any** inner holds), where an exception's
;; conjuncts are one condition (block if **all** hold).  Nothing is stored; the inner
;; query is re-evaluated on the same triggers.  See docs/naf.md.

(defn- unknown-inner-holds?
  "Does the query inside an `(unknown …)` antecedent hold under `bindings`, evaluated
  in `pctx`?  Run exactly like an exception conjunct — `provers/exception-holds?` over
  the single inner literal — so `unknown` and `exceptWhen` share one level-6 evaluator
  and cannot drift; a nested `thereExists` is dispatched to its prover from there.
  When it holds, `S` is derivable, so `(unknown S)` is false and the firing is blocked."
  [kb unk bindings pctx]
  (provers/exception-holds? kb [(second unk)] bindings pctx))

(defn naf-blocks?
  "Is a firing blocked by any of its `unknown` antecedents `naf-antes` — is any inner
  query derivable under `bindings`, in `pctx`?  Block-if-**any**: each `(unknown S)`
  independently requires `S` absent, so one derivable `S` withdraws the conclusion."
  [kb naf-antes bindings pctx]
  (boolean (some #(unknown-inner-holds? kb % bindings pctx) naf-antes)))

(defn post-join-bindings
  "Extend `bindings` with what a firing's post-join literals compute (`rules/post-join
  -literals`), or nil when one of them has no answer.

  This is where an aggregate antecedent is actually evaluated: not in the join, which
  does not yet know where the conclusion lands, but per placement context — the same
  answer `exceptWhen` and `unknown` give to the same question, and the one that makes
  the three chainers agree.  Each literal is solved through the prover registry under
  the bindings the previous ones produced, so an aggregate feeds the comparison on its
  own count.

  **Each keeps the context it would have had in the join.**  An aggregate runs in
  `pctx`, because a census is of what that context believes.  A comparison runs in the
  wildcard, because arithmetic holds as arithmetic rather than as knowledge asserted
  somewhere — the same reason `solve-deferred` uses it.  Moving a literal later must
  not quietly move it to another context.

  Nil is a **block**, and it means one of two things that the caller need not
  distinguish: the literal has no answer at all (a `min` over an empty group, a
  comparison that came out false), or its output was already bound — by an earlier
  antecedent, or by the firing this is re-checking — and the recomputed value no
  longer matches it."
  [kb literals bindings pctx]
  (reduce (fn [bs lit]
            (let [g   (res/substitute lit bs)
                  ctx (if (sx/aggregate? lit) pctx '?ctx)]
              (if-let [sol (first (provers/solve-goal kb g ctx))]
                (merge bs sol)
                (reduced nil))))
          bindings
          literals))

(defn- rule-calculi
  "The registered calculi a rule's antecedents draw on — empty for every rule that does
  not mention one, and for every KB that registered no prover."
  [kb rsx]
  (into #{}
        (keep (fn [ante]
                (when (and (sequential? ante) (= 3 (count ante)) (symbol? (first ante)))
                  (qkb/calculus-for kb (first ante)))))
        (:antecedent rsx)))

(defn- entailment-withdrawn?
  "Was this firing licensed by a qualitative entailment the network no longer makes?

  Only one thing can do that, and it is worth being precise about which: adding a
  constraint only ever *narrows* what is possible, and narrowing makes a positive
  entailment more likely rather than less — so an entailed relation is never lost by
  learning more. What is lost is the right to use it at all, when the facts turn out to
  be unsatisfiable: an impossible theory entails everything and is mined for nothing.

  A justification's antecedents cannot express that. They name the facts the entailment
  rested on, and those are all still stored and believed when some *other* fact makes
  the network impossible. So the conclusion is blocked the way an excepted one is, and
  revived by the same machinery when the clash is retracted."
  [kb rsx pctx]
  (let [calcs (rule-calculi kb rsx)]
    (boolean (and (seq calcs)
                  (some #(qkb/inconsistent? % kb pctx) calcs)))))

(defn- post-join-withdrawn?
  "Was this firing licensed by a count the KB no longer computes?

  A justification's antecedents cannot express that.  They name the facts the join
  matched, and every one of them is still stored and believed when some *other* fact
  changes what an aggregate antecedent counts — the new fact is not among them,
  precisely because an aggregate reads what is believed rather than matching a tuple.
  So the firing is blocked the way an excepted one is, and revived by the same
  machinery when the count comes back.

  The re-check runs `post-join-bindings` in the conclusion's own context under the
  firing's stored bindings, where every output is already bound — so each literal runs
  in **check** mode and nil means the recomputed value no longer matches the one this
  conclusion was drawn from.  The comparisons on a count are re-run too, and have to
  be: a firing licensed by `(lessThan 2 ?n)` at a count of 3 is not licensed at a count
  of 1, and the aggregate alone would report only that the number moved.

  `bindings` is a delay, forced only once there is a post-join literal to re-run —
  every rule reaches here and most have none."
  [kb rsx bindings pctx]
  (let [post (rules/post-join-antecedents rsx)]
    (boolean (and (seq post)
                  (nil? (post-join-bindings kb post @bindings pctx))))))

(defn- settled-bindings
  "A firing's stored bindings, with each bound term rewritten to the representative
  `pctx` now elects.

  A justification records what matched **when it fired**, and an equality merge does not
  go back and edit it: a firing that bound `?c` to `C3` still says `C3` after `(sameAs
  C2 C3)` has retired that spelling.  Every re-check below substitutes these bindings
  into a query and asks the engine — so left as stored they ask about a term the KB no
  longer answers under, and what comes back is the honest empty that reads as *not
  excepted*, *not derivable*, *counted nothing*.  An `exceptWhen` would quietly stop
  guarding, which is the loudest way this can go wrong: an unanswerable exception does
  not hold, and the rule fires.

  Rewritten in the **conclusion's** context, the scoping every other read of the
  partition takes — a merge that context cannot see must not rename what its own
  re-check asks about.  One visibility predicate for the whole map, since a firing's
  bindings are all read from the one context and building it costs a record fetch per
  equality supporter.

  A KB whose partition is empty and which declares no schematic equation hands the
  bindings straight back — the two things that could rewrite a term are the two gated
  here, and this runs per firing on the settle path, where a `filterv` over the rewrite
  rules per bound term is what an ungated version would cost."
  [kb bindings pctx]
  (let [tx (:taxonomy kb)]
    (if (and (nil? (tax/merged-term-pred tx)) (empty? (tax/rewrite-rules tx)))
      bindings
      (let [visible? (res/visible-supporter-fn kb pctx)]
        (reduce-kv (fn [m v t] (assoc m v (kb/rewrite-term* kb t visible?))) {} bindings)))))

(defn justification-excepted?
  "Is justification `j` currently blocked — by its rule's `exceptWhen` exception, by an
  `(unknown S)` antecedent whose `S` is now derivable, by an **aggregate** antecedent
  whose count has moved, by a visibility `except` hiding one of its antecedents from
  the conclusion's context, or by the qualitative network it joined on having become
  unsatisfiable?

  The context is the **conclusion's**, not the rule's: an exceptWhen query and a NAF
  literal are *about* the conclusion (one invisible from where it lives has no business
  blocking it), and a visibility `except` is precisely about where a fact can be seen —
  a derivation resting on an antecedent the conclusion's context cannot see is invalid
  there.  Nothing is cached: this re-runs the checks every time, which is what keeps
  blocking from drifting out of step with belief."
  [kb j]
  (when-let [csx (p/get-sentex (:records kb) (:consequence j))]
    (let [pctx (:context csx)
          inf  (:informant j)]
      (boolean
       (or
        ;; `except`: the conclusion's context hides one of the firing's antecedent facts
        ;; (`res/excepted-handles` is gated on the `except` root, so this is free when
        ;; nothing is excepted).  The rule handle is among `:antecedents` too, but a rule
        ;; is never an `except` target, so it never spuriously matches.
        (let [hidden (res/excepted-handles kb pctx)]
          (and (seq hidden) (boolean (some hidden (:antecedents j)))))
        ;; `exceptWhen` / `unknown`, and a qualitative network gone impossible
        (when (integer? inf)
          (when-let [rsx (p/get-sentex (:records kb) inf)]
            (let [b (delay (settled-bindings kb (:bindings j) pctx))]
              (or (when (or (rules/has-naf? rsx) (p/exception-rule? (:index kb) inf))
                    (or (provers/exceptions-block? kb inf @b pctx)
                        (and (rules/has-naf? rsx)
                             (naf-blocks? kb (rules/naf-antecedents rsx) @b pctx))))
                  (post-join-withdrawn? kb rsx b pctx)
                  (entailment-withdrawn? kb rsx pctx))))))))))

;; ---- forward chaining ---------------------------------------------------

;; **Deferred antecedents.**  A deferred (evaluable) literal — `lessThan`,
;; `greaterThan`, `evaluate`, `different` (`sentex/deferred-predicates`) — is not a
;; stored fact.  It is *computed* from the bindings the other antecedents produced,
;; which is why `vaelii.impl.sentex` holds it back to the end of the canonical
;; antecedent order and `vaelii.impl.plan` pulls it forward only once its inputs are
;; bound.  Joining it with `match-pattern` therefore looks up a fact nobody ever
;; stored, finds nothing, and kills the whole join — silently, since an empty join is
;; indistinguishable from a rule that simply had nothing to fire on.  The backward
;; chainers never had that bug because they discharge every antecedent through
;; `provers/solve-goal`, where the evaluable provers live.  The join below goes to the
;; same registry rather than growing a second evaluator that could disagree with it.

(defn- solve-deferred
  "Solve a deferred antecedent against `bindings` by **computing** it: the substituted
  literal goes to the prover registry, which answers it with `EvaluableProver` /
  `EvaluateProver` / `DifferentProver`.  Returns the extended binding maps — a test
  (`lessThan`, `different`) yields the bindings unchanged or nothing at all, while
  `evaluate` adds the binding it computed, so both the testing and the binding flavour
  fall out of the one call.

  The context is the wildcard, and deliberately so: a computed literal holds as
  arithmetic rather than as knowledge asserted somewhere, so there is no context that
  could fail to see it.  That is the same reason the caller records no handle for it.

  **Its inputs must already be bound**, and two things arrange that before the join
  runs: `sentex/check-naf-closed` refuses at assert time a rule whose deferred literal
  reads a variable nothing in the rule writes, and `planned-join` withholds the ones
  whose inputs an aggregate supplies per placement.  So reaching here unbound means one
  of those two broke, and it throws.  Answering it with an empty join instead would
  report a comparison that was never *run* as a comparison that *failed*, which is
  precisely the silent-empty-join failure this whole section exists to remove."
  [kb literal bindings]
  (let [g (res/substitute literal bindings)]
    (when-let [unbound (seq (sx/deferred-input-vars g))]
      (throw (ex-info (str "deferred antecedent " (pr-str g) " reached the join with unbound "
                           "input " (pr-str (vec unbound)) " — it is computed, not looked up, "
                           "so an earlier antecedent must bind its inputs")
                      {:literal literal :goal g :unbound (vec unbound)})))
    (map #(merge bindings %) (provers/solve-goal kb g '?ctx))))

;; ---- qualitative antecedents: joining on what a network entails ----------
;; A relation algebra derives relations nobody stored (docs/qcn.md).  Those could not
;; fire a forward rule, and the reason was not the wiring: an entailed relation has no
;; handle, so there was no antecedent for a justification to rest on, and a conclusion
;; nothing can withdraw is worse than a conclusion never drawn.
;;
;; Support closes it.  The fixpoint now reports which stored facts a tightened
;; constraint rests on, so an entailed antecedent contributes *those* handles — the
;; conclusion is withdrawn when any fact behind the entailment goes, which is exactly
;; the contract an ordinary matched antecedent has.  The deferred (evaluable) path
;; cannot do this and correctly does not try: `(lessThan 1 2)` is a function of the
;; bindings, where `(partOfRegion A C)` is a function of what is *stored*.
;;
;; This is **union, not replacement**.  Entailment subsumes assertion — an asserted
;; relation is trivially entailed — but the two disagree at the edges (a literal whose
;; arguments are not network nodes is outside the calculus under either polarity), so
;; the ordinary matcher still runs and nothing that matched before stops matching.
;; Duplicate justifications from the two routes are set-deduped by the TMS.

(def ^:dynamic *qcn-contexts*
  "Per-run cache of `{calculus-name -> #{context}}` — the readers of a calculus, which
  are the networks an entailed antecedent is solved against.

  Collecting them walks the calculus's own extent, the same order as reading one
  network, and where its facts span microtheories a `genlContext` closure besides, so it
  is cached for the length of a chaining run rather than recomputed per antecedent per
  binding.  Bound by `chain`; nil outside one, where it simply recomputes."
  nil)

(defn- calculus-contexts
  "The networks worth re-joining `calc` against — `qcn-kb/reader-contexts`, cached for
  the length of a chaining run.

  A network is what a **reader** sees, and a reader sees the whole `genlContext` cone
  above it, so the contexts that merely *hold* a fact are not the networks a forward
  rule may join on: a context inheriting two microtheories composes what neither
  composes alone, and that entailment exists for no other reader.  `ask` has always
  answered it there.  Left at the fact contexts, such a firing would wait for some
  unrelated fact to be stated in the meeting context and then survive its retraction —
  belief decided by an assertion that entails nothing, which is the arrival-order
  dependence the engine does not allow (docs/nmtms.md).

  Which context the *conclusion* lands in is still not decided here.  Placement reads
  the contexts of the support handles, exactly as it reads the contexts of ordinarily
  matched facts, so a firing solved at a meeting context is placed by the facts that
  entailed it and lands there because *they* meet there."
  [kb calc]
  (if-let [memo *qcn-contexts*]
    (or (get @memo (:name calc))
        (let [cs (qkb/reader-contexts kb calc)] (swap! memo assoc (:name calc) cs) cs))
    (qkb/reader-contexts kb calc)))

(def ^:dynamic *qualitative-delta*
  "`{:literal <antecedent> :moved {context (:all | #{pair})}}`, or nil.

  What makes a re-join **semi-naive**.  A qualitative fact re-joins every rule mentioning
  its calculus, and joining over every pair the network entails means the nth arriving
  fact redoes what the (n-1)th already did.  Bound by `rejoin-qualitative` to the pairs
  that have moved since the last such re-join (`qcn-kb/join-delta`), it narrows the
  enumeration of **one** antecedent — the named literal — and leaves the rest full.

  One antecedent, because that is the delta rule: for a rule with two qualitative
  antecedents, narrowing both at once would drop every firing pairing a moved binding with
  an unmoved one.  So `rejoin-qualitative` runs the join once per qualitative antecedent,
  each with a different one narrowed, and the overlap re-derives conclusions the TMS
  dedups.

  Read by literal rather than by position: `plan/order` reorders the antecedents, so a
  position means nothing by the time the join runs.  Two identical antecedents in one rule
  are both narrowed, which is the same set — they bind identically."
  nil)

(defn- solve-qualitative
  "Solve a qualitative antecedent by **entailment**, against every network the calculus
  has facts in.  Each solution carries the support handles the entailment rests on, so
  the firing's justification names them and retraction reaches them.

  An entailment with empty support is dropped by `qcn-kb/solve-with-support` rather than
  answered groundlessly — see there.

  Narrowed to the moved pairs when this is the literal `*qualitative-delta*` names, and a
  context nothing moved in is skipped outright.  Both are per **context**: an arriving
  fact narrows the networks that see it and leaves the others exactly where they were."
  [kb calc literal states]
  (let [ctxs  (calculus-contexts kb calc)
        d     *qualitative-delta*
        moved (when (and d (= literal (:literal d))) (:moved d))]
    (distinct
     (for [{:keys [bindings handles matched]} states
           :let [g (res/substitute literal bindings)]
           ctx ctxs
           :let [m     (when moved (get moved ctx :all))
                 pairs (when (and m (not= m :all)) m)]
           :when (or (nil? m) (= m :all) (seq pairs))
           [bnd sup] (qkb/solve-with-support calc kb g ctx pairs)]
       ;; `:matched` passes through unextended: an entailed antecedent was licensed by
       ;; the network rather than by the taxonomy, so it rests on no `genl` edge and
       ;; has no antecedent-functor pairing to record.
       {:bindings (merge bindings bnd) :handles (into handles sup) :matched matched}))))

(defn- qualitative-antecedent
  "The registered calculus claiming `ante`, or nil — nil for every KB that registered no
  prover, which is why this costs nothing until a caller opts in.  Positive binary
  literals only: a negated one is refuted by the network rather than entailed by it, and
  what a refutation rests on is the whole network rather than a support list."
  [kb ante]
  (when (and (sequential? ante) (= 3 (count ante)) (symbol? (first ante)))
    (qkb/calculus-for kb (first ante))))

(defn- join-antecedent
  "Extend the partial join `states` ({:bindings :handles :matched}) by one antecedent.

  A deferred literal is computed (see above) and contributes **no handle**.  Every
  other antecedent contributes the handle of the fact that satisfied it, and a
  computed one has no fact to name.  Inventing a placeholder would be worse than
  omitting it: `retract!` withdraws a conclusion by walking its justifications'
  antecedents, so a handle that names nothing retractable is a support that can never
  be taken away.  Omitting it is also *sufficient* — the computed literal's truth is a
  function of the bindings, and those bindings come from the fact handles that are
  listed, so dropping any contributing fact still withdraws the conclusion.  A firing
  whose antecedents are all computed lists the rule handle alone, which is the honest
  reading: nothing but the rule supports it.

  `:matched` pairs each ordinarily matched fact with the **functor of the antecedent
  it satisfied**, which `:handles` alone cannot say: the join runs in cost order
  (`planned-join`), so a handle's position in the vector names nothing.  The pairing is
  what lets a firing tell which of its facts reached its antecedent through the `genl`
  hierarchy, and therefore which taxonomy edges it rests on (`subsumption-links`).  A
  qualitative entailment's support handles are not paired: the network licensed them,
  not the taxonomy."
  [kb ante states]
  (cond
    ;; An `(unknown S)` antecedent is negation as failure, checked at *derive time* in
    ;; the conclusion's placement context — exactly where `exceptWhen` is checked, and
    ;; for the same reason: forward and backward must evaluate it in the same context.
    ;; It binds nothing and names no fact, so the join passes straight through; the
    ;; block decision is `naf-blocks?` in `derive-conclusion`, and later fact arrivals
    ;; re-block it through the same re-check path exceptions use.
    (sx/unknown? ante) states

    ;; An aggregate antecedent binds `?n` to a **census**, and which facts are in the
    ;; census is decided by the context the conclusion lands in — which the join does
    ;; not know yet, placement being computed from the matched facts afterwards.  So it
    ;; passes through here exactly as `unknown` does, and `?n` is bound per placement
    ;; in `place-conseq`.  That is also what makes forward and backward agree: the
    ;; backward chainers evaluate it in the goal's context, and both are "the context
    ;; the conclusion is about" (docs/aggregate.md).
    ;;
    ;; `planned-join` has already withheld this literal and everything downstream of
    ;; it, so reaching here means a caller joined an antecedent list directly.  Held as
    ;; a guard rather than dropped: falling through to the deferred arm below would
    ;; answer the census in the wildcard context, which is a *wrong* count rather than
    ;; a missing one.
    (sx/aggregate? ante) states

    (sx/deferred-literal? ante)
    (mapcat (fn [{:keys [bindings handles matched]}]
              (map (fn [b] {:bindings b :handles handles :matched matched})
                   (solve-deferred kb ante bindings)))
            states)

    :else
    (let [af  (nm/functor ante)
          hit (mapcat (fn [{:keys [bindings handles matched]}]
                        (for [[h b2] (*matcher* kb (res/substitute ante bindings) '?ctx)]
                          {:bindings (merge bindings b2) :handles (conj handles h)
                           :matched  (conj matched [af h])}))
                      states)]
      (if-let [calc (qualitative-antecedent kb ante)]
        (distinct (concat hit (solve-qualitative kb calc ante states)))
        hit))))

(defn- planned-join
  "Order `antecedents` by estimated fan-out under the bindings already in hand (`b0`),
  then join them left to right from `seed`.  Reordering a conjunction changes only how
  fast the answer is reached, never the answer set — and justification dedup is
  set-based (`jtms/has-justification?`), so the reordered `:handles` still dedup — so
  this is a pure cost decision, the same one `res/planned-antecedents` makes for the
  backward chainers.  `plan/order` pins the operational literals exactly as canonical
  antecedent order did: the deferred (evaluable) and `unknown` (NAF) literals never
  outrun what binds them, and the recursive literal stays put (`consequent-pred`).
  Antecedents are substituted with `b0` before planning so the trigger's bindings make
  the estimates exact, mirroring the backward path.

  The **post-join** literals are withheld entirely (`rules/post-join-literals`): an
  aggregate and everything reading its output are evaluated per placement context, so
  a join that ran them would either take the census in the wrong context or reach a
  comparison whose input nothing here can bind."
  [kb antecedents b0 consequent-pred seed]
  (let [subbed (mapv #(res/substitute % b0) antecedents)
        post   (set (rules/post-join-literals subbed))]
    (reduce (fn [states ante] (if (post ante) states (join-antecedent kb ante states)))
            seed
            (plan/order kb subbed '?ctx {:consequent-pred consequent-pred}))))

(defn- complete-antecedents
  "Enumerate {:bindings :handles} completions of a rule fired at position
  `trigger-idx` by `trigger-handle`, joining the other antecedents from facts in
  any context, in cost order (`planned-join`).

  **Any context on purpose** — the join passes `'?ctx` throughout.  Admissibility is
  placement's question: `place-conseq` requires a context that sees the rule and
  every antecedent fact (the common-descendant rule), and a firing it rejects is
  recorded as `:no-placement`.  Narrowing the join by some context's visibility
  would silently drop firings placement accepts, and turn a recorded outcome into
  a firing that never happened.

  A deferred literal at the trigger position is computed like any other, and the
  trigger handle is dropped.  That position is reachable — nothing stops a caller
  asserting `(lessThan 1 2)` as a fact, and the rule index keys the antecedent by its
  functor — but a computed literal must not draw support from a stored twin: the same
  firing arrives by every other antecedent's trigger with the literal *computed*, and
  two justifications for one conclusion that disagree about what supports it is the
  ambiguity the fix is meant to remove.  So a non-deferred trigger is recorded as a
  handle and dropped from the join; a deferred trigger is joined (computed) and the
  cost planner orders it among the rest."
  [kb antecedents trigger-idx trigger-handle b0 consequent-pred]
  (let [trigger-ante (nth antecedents trigger-idx)
        handle-only? (not (sx/deferred-literal? trigger-ante))
        to-join      (if handle-only?
                       (vec (keep-indexed (fn [j a] (when (not= j trigger-idx) a)) antecedents))
                       (vec antecedents))
        seed         [{:bindings b0
                       :handles  (if handle-only? [trigger-handle] [])
                       ;; the trigger is a match like any other, and it is the one most
                       ;; likely to have subsumed: `fire-rules-for` reaches a rule
                       ;; through the arriving fact's *supertypes*
                       :matched  (if handle-only? [[(nm/functor trigger-ante) trigger-handle]] [])}]]
    (planned-join kb to-join b0 consequent-pred seed)))

(defn solve-rule
  "Full join of a rule's antecedents against current facts (used when a rule is
  added), in cost order.  The seeded arity starts from `b0` instead of the empty
  binding map, which is how `why-not` reconstructs a firing backwards from its
  conclusion; `consequent-pred` (the rule's consequent functor, nil if unknown) lets
  the planner keep the recursive literal in place."
  ([kb antecedents] (solve-rule kb antecedents {} nil))
  ([kb antecedents b0] (solve-rule kb antecedents b0 nil))
  ([kb antecedents b0 consequent-pred]
   (planned-join kb (vec antecedents) b0 consequent-pred
                 [{:bindings b0 :handles [] :matched []}])))

(defn- free-consequent-vars
  "The variables remaining in a rule's substituted conclusion `form` — the head
  existential variables the antecedent bindings did not cover.  Empty for an ordinary
  range-restricted rule, so this is the cheap test for whether skolemization applies.

  A direct walk rather than `tree-seq` + `filter` + `distinct`, because it runs **per
  firing** and its answer is almost always nil: those three compose into a lazy seq
  apiece over a form that is usually `(pred a b)`, where the walk they wrap is three
  `cond` arms.  Nothing is allocated until a variable is actually found."
  [form]
  (letfn [(walk [acc x]
            (cond
              (sx/variable? x) (if (some #(= x %) acc) acc (conj acc x))
              (sequential? x)  (reduce walk acc x)
              :else            acc))]
    (seq (walk [] form))))

(defn- place-conclusion
  "Persist/justify a rule conclusion `conseq` in context `pctx` at justification
  `strength` (:monotonic / :default); return the handles newly created (for
  enqueueing) — the conclusion itself, plus a copy in each context its predicate is
  declared to lift into.

  The definitional constraints — argIsa types, disjointness, functionality — hold of
  *derived* content as much as of asserted content; a rule that concludes
  `(cat Rex)` where `(dog Rex)` is believed and the two are declared disjoint has
  concluded something the KB says cannot be.  They are checked here, on the
  derivation path, exactly as `assert-one` checks them on the assert path.  So does
  stratification, for the one conclusion that can break it: a derived `genl` /
  `genlContext` edge that would close a cycle through negation.

  A failure is **dropped and recorded**, never thrown: chaining is a fixpoint and
  must not abort halfway through it, and an exception escaping a rule firing would
  make the resulting belief set depend on which rule happened to fire first.  The
  conclusion is skipped (no sentex, no justification) and the violation lands in the
  KB's `violations` atom, readable with `core/violations`.

  Dropping is the pragmatic answer, not the principled one.  The principled end state
  is to reframe these as **high-priority nogoods** so a derived violation is
  *arbitrated* by the settle layer like any other contradiction — defeating whichever
  side is weaker instead of unconditionally discarding the newcomer — which is what
  docs/nmtms.md already proposes.  That is a larger change and is not made here."
  [kb rule conseq pctx all-antes depth bindings strength]
  (let [existing (kb/find-sentex-handle kb conseq pctx)
        ;; Checked only when the conclusion is **new**.  Re-deriving a sentence already
        ;; stored in this context adds a *justification*, not content — whatever it says
        ;; was admissible when it was first placed, so a second derivation of it cannot
        ;; introduce a violation that was not already there.  This is not a
        ;; micro-optimization: `args-problem` runs `isa?`, which walks a type's whole spec
        ;; closure with an index lookup per subtype, and forward chaining re-derives the
        ;; same conclusion on every round of every defaults pass.  Paying it per firing
        ;; rather than per new conclusion made the starter's load ten times slower.
        ;; ...and the rule-set constraint alongside them: a derived `genl` edge
        ;; reaches the taxonomy through `integrate-transitive` below, so it can close
        ;; a cycle through negation with no caller asserting anything.  Same
        ;; treatment — dropped and reported, never thrown.
        ;; one pass over the definitional checks, answering both halves: the violation
        ;; that drops the conclusion, and — for an admitted one — what the argument
        ;; constraints entail about its arguments, materialized below once it has a
        ;; handle to be justified against
        adm      (when-not existing (checks/constraint-admission kb conseq pctx))
        v        (when-not existing
                   (or (:violation adm)
                       ;; structural well-formedness of a special predicate the rule
                       ;; concluded — a derived `genl` edge can close a taxonomy cycle
                       (special/wff-violation kb conseq)
                       (checks/edge-stratification-violation kb conseq)))]
    (if v
      (do (violations/report kb
                             [(assoc v :sentence conseq :context pctx :rule (:rule-handle rule))])
          [])
      (let [[h s new?] (if existing
                         [existing (p/get-sentex (:records kb) existing) false]
                         (let [[h s] (kb/create-sentex kb conseq pctx)] [h s true]))]
        ;; the derivation-path choke point: a derived genl edge reaches the closure,
        ;; and a derived fact is a re-check trigger like an asserted one
        (when new? (special/derived-sentex-added kb s h))
        (jtms/ensure-node (:tms kb) h depth)
        (when-not (jtms/has-justification? (:tms kb) (:name rule) all-antes h)
          (let [jid  (p/next-id (:records kb))
                just (jtms/->just jid (:name rule) all-antes h bindings strength)]
            (p/put-justification (:records kb) just)
            (jtms/add-justification (:tms kb) just)))
        ;; A *derived* second value for a functional predicate merges exactly as an
        ;; asserted one does.  It has to be here as well as in `assert-one`, because
        ;; `functional-problem` does not refuse a symbol clash (it derives an equality
        ;; instead): without this a rule concluding `(motherOf Tom MrsSmith)` alongside
        ;; `(motherOf Tom Mary)` would leave two values of a functional predicate
        ;; believed and unreconciled.  The
        ;; twins it creates are not fed back onto the agenda — they are placed and
        ;; justified immediately, they just do not re-trigger rules within this run.
        (when new?
          (when-let [m (special/derive-functional-equalities kb conseq pctx h)]
            (violations/report kb (:violations m)))
          ;; ...and the declaration's own side of the same inference: a rule concluding
          ;; `(functional P)` reaches P's stored facts exactly as an asserted one does,
          ;; or which values a slot reconciles would depend on whether the declaration
          ;; was written or derived
          (when-let [m (special/equate-existing kb conseq)]
            (violations/report kb (:violations m))))
        ;; A decontextualized predicate is a claim about the predicate, so the lift runs
        ;; on content a rule concluded exactly as it runs on content a caller asserted
        ;; (`assert-one`).  Unconditionally, not only for a new conclusion: a
        ;; re-derivation is how a conclusion that was already stored — and so was
        ;; skipped by the retroactive sweep, or arrived before the declaration did —
        ;; picks its copy up.  The copy is a new datum in a context that did not have
        ;; it, so it is enqueued like the conclusion itself.
        ;; The argument constraints entail of a *derived* conclusion exactly what they
        ;; entail of an asserted one — a claim about the predicate, not about how the
        ;; sentence arrived.  Drawn only for a new conclusion, like the checks above: a
        ;; re-derivation adds a justification, not content, and whatever the sentence
        ;; entailed was entailed when it was first placed.  A conclusion that *is* a
        ;; declaration reaches back over the stored facts, as an asserted one does.
        (let [lift (special/deduce-lifts kb conseq h pctx)
              args (special/deduce-arg-types kb (:entailments adm) h pctx)
              back (special/entail-existing kb conseq h)]
          (violations/report kb (concat (:violations lift) (:violations args)
                                        (:violations back)))
          (-> (if new? [h] [])
              (into (:new lift))
              (into (:new args))
              (into (:new back))
              ;; a *derived* genl edge makes stored facts matchable at a supertype
              ;; they did not have, exactly as an asserted one does — same seeds, or
              ;; the fixpoint would depend on which rule fired first
              (into (special/subsumption-seeds kb conseq))
              ;; and a derived genlContext edge widens what a rule can see, for the
              ;; same reason and with the same remedy
              (into (special/visibility-seeds kb conseq))))))))

(defn- subsumption-links
  "The `[fact-functor antecedent-functor]` pairs a firing reached through
  **predicate/type subsumption** — one per matched fact whose own functor is not the
  functor of the antecedent it satisfied.

  Empty for every ordinary firing, which is what keeps this free: a fact matches an
  antecedent of its own functor, so the `not=` drains the pipeline before a closure is
  ever read.  `record-of` is the firing's already-fetched records; a matched handle
  with no record (swept mid-run) is skipped rather than guessed at.

  Read **upward from the fact**, not downward from the antecedent: `ff ∈ specs(af)` and
  `af ∈ genls(ff)` are the same reachability on the same edges, and the up-closure of a
  term is its chain to `thing` where the down-closure of a general antecedent can be
  most of the hierarchy (OpenCyc's `thing` has six figures of them).  Same answer, and
  the memo it fills is the small one.

  The global closure is the gate, not a placement's: whether the two functors are
  related at all is a property of the KB, and *which* contexts can see the relating
  edges is `subsumption-support`'s question, asked once per placement."
  [kb matched record-of]
  (let [tax (:taxonomy kb)]
    (into []
          (comp (keep (fn [[af h]]
                        (when-let [ff (nm/functor (:sentence (record-of h)))]
                          (when (and (symbol? af) (symbol? ff) (not= af ff)) [ff af]))))
                (distinct)
                (filter (fn [[ff af]] (contains? (tax/genls tax ff) af))))
          matched)))

(defn- subsumption-support
  "A witness for each of a firing's subsumptions, as `[handle ctx]` supporter pairs
  (`tax/reach-support`) — or nil when `vantage` sees no path for one of them.  A nil
  `vantage` asks globally, which is what placement does: the edges are an *ingredient*
  of the firing, so their contexts are an input to deciding where it lands rather than
  a test on a decision already made.

  A fact that satisfied an antecedent of a different functor did so over a `genl` path,
  and a conclusion that rests on that path may only live where the path is visible —
  otherwise a microtheory believes `(ancestorOf Tom Bob)` on the strength of a
  `(genl fatherOf parentOf)` edge some sibling theory asserted and it cannot see.
  Feeding the supporters' contexts to `maximal-common-descendant-contexts` beside the
  rule's and the facts' makes that structural: every placement it returns sees every
  edge by construction, so there is nothing left to filter, and the firing's three
  ingredients — rule, facts, taxonomy — are treated alike.

  The join itself stays global (`complete-antecedents`, any context on purpose): which
  facts *exist* is not the placement's question, and narrowing the join would drop
  firings placement accepts."
  [kb links vantage]
  (reduce (fn [acc [ff af]]
            (if-let [hs (tax/reach-support (:taxonomy kb) :genl ff af vantage)]
              (into acc hs)
              (reduced nil)))
          []
          links))

(defn- placement-ingredients
  "Where a firing's conclusion may live, and which `genl` supporters it names getting
  there: `[placement-contexts {placement-context [edge-handle]}]`.

  An **`(ist Ctx S)` consequent names its own context**, and that is an escape hatch
  rather than a computed placement, so there is nothing to derive — the target is fixed
  and the only question is whether it can reproduce the subsumption, asked from `Ctx`
  itself so the edges it names are the ones it can see.  No witness there, no placement.

  Everything else is derived from the firing's three ingredients — the rule, the
  antecedent facts, and the taxonomy the match climbed — by the one rule that has always
  governed the first two: the **maximal contexts that see all of them**.  The edges enter
  that computation as their supporters' asserting contexts.

  They are chosen to **constrain the placement least**, which is what makes this a
  widening of the rule for the rule and the facts alone rather than a different one.
  Where a maximal context seeing the rule and the facts can also see a path, the edges
  add no constraint at all and the placement is exactly what it would have been —
  per candidate, since two incomparable candidates may see different supporters of one
  edge, and picking one witness for both would drop whichever candidate cannot see it.
  Only where *no* such candidate exists is the taxonomy a binding constraint, and then
  the conclusion descends to the maximal contexts that see the edges too — where it used
  to evaporate into a `:no-placement`.  A supporter with no recorded context is seen from
  everywhere and constrains nothing, so it drops out of the list rather than emptying it.

  Deliberately conservative in one direction: the descent uses one global witness, so a
  firing whose candidates *some* of which see a path keeps only those, and does not also
  descend below the others.  Placing under both would need the union re-maximalized, and
  the case — incomparable candidates disagreeing about one edge — is exotic."
  [kb rule raw-c ist? links fact-ctxs]
  (if ist?
    (let [c  (when (nm/context? (second raw-c)) (second raw-c))
          hs (when c (subsumption-support kb links c))]
      (if (and c hs) [[c] {c (mapv first hs)}] [nil nil]))
    (let [tax  (:taxonomy kb)
          base (tax/maximal-common-descendant-contexts tax (cons (:context rule) fact-ctxs))]
      (if (empty? links)
        [base {}]
        (let [seeing (reduce (fn [m b]
                               (if-let [hs (subsumption-support kb links b)]
                                 (assoc m b (mapv first hs))
                                 m))
                             {} base)]
          (if (seq seeing)
            [(filterv seeing base) seeing]
            (when-let [hs (subsumption-support kb links nil)]
              (let [ps (tax/maximal-common-descendant-contexts
                        tax (concat [(:context rule)] fact-ctxs (keep second hs)))]
                [ps (zipmap ps (repeat (mapv first hs)))]))))))))

(defn- place-conseq
  "Place one ground conclusion literal `raw-c` from a firing: resolve its placement
  contexts — an `(ist Ctx S)` names its own, else the maximal contexts that see the
  rule and all antecedent facts — and place it in each unless the rule's exception or a
  NAF antecedent blocks it there.  Returns the newly created handles.  A firing with no
  placement context is recorded like any other dropped conclusion.

  `links` are the firing's subsumptions (`subsumption-links`); the `genl` supporters
  witnessing them are an **ingredient of the placement** (`placement-ingredients`), not
  a filter on it, and they join the antecedent list."
  [kb rule raw-c all-antes facts links depth bindings]
  (let [ist?        (and (sequential? raw-c) (= sx/ist-functor (first raw-c)))
        conseq      (if ist? (nth raw-c 2) raw-c)         ; (ist Ctx S) concludes S ...
        fact-ctxs   (map :context facts)
        [placements support] (placement-ingredients kb rule raw-c ist? links fact-ctxs)]
    (if (empty? placements)
      ;; The join completed — every antecedent matched — and then the conclusion
      ;; evaporated: no context sees everything the firing rests on (sibling
      ;; microtheories with no common descendant, the taxonomy it climbed included), or
      ;; an ist consequent named something that is not a context or an edge it cannot
      ;; see.  "Possibly none" is a legitimate outcome of
      ;; maximal-common-descendant-contexts, but a silent one reads as "the rule fired",
      ;; so it is recorded like any other dropped conclusion — naming the subsumption
      ;; when there was one, since "your microtheory cannot see that genl edge" is a
      ;; different thing to go and fix from "your facts are in sibling contexts".  The
      ;; contexts that *would* have taken it but for the edges are recomputed here, on
      ;; the drop path only, because that difference is the whole diagnosis.
      (do (violations/report kb
                             [{:violation :no-placement :sentence conseq :rule (:rule-handle rule)
                               :detail (cond-> {:rule-context  (:context rule)
                                                :fact-contexts (vec (distinct fact-ctxs))
                                                :message
                                                (if (seq links)
                                                  (str "completed firing has no placement context — "
                                                       "no context sees the rule, all antecedent facts, "
                                                       "and the genl edges the match subsumed through")
                                                  (str "completed firing has no placement context — "
                                                       "no context sees the rule and all antecedent facts"))}
                                         (seq links)
                                         (assoc :subsumed (mapv first links)
                                                :would-place
                                                (vec (when-not ist?
                                                       (tax/maximal-common-descendant-contexts
                                                        (:taxonomy kb)
                                                        (cons (:context rule) fact-ctxs))))))}])
          [])
      ;; `exceptWhen`, `unknown`, and a visibility `except` all **block**: for a
      ;; placement one of whose exceptions holds, one of whose `(unknown S)` antecedents
      ;; finds `S` derivable, or one of whose antecedent facts a believed `except` hides
      ;; from the placement context, there is no conclusion and no justification —
      ;; nothing to defeat and nothing to arbitrate.  The check is per *placement*,
      ;; because all three are evaluated in the conclusion's context and a firing may
      ;; place into several.  `all-antes` includes the rule handle, never an `except`
      ;; target, so it cannot spuriously match the hidden set.
      ;; `mapcat`, not `map`: one placement yields the conclusion *and* a copy in each
      ;; context the predicate is lifted into, and every one of them is a new datum the
      ;; agenda has to see.
      (into []
            (mapcat (fn [pctx]
                      ;; the `genl` supporters are per placement, so the antecedent list
                      ;; is too — and it is this list, not `all-antes`, that the `except`
                      ;; check reads, since `justification-excepted?` re-runs that check
                      ;; over the *stored* justification's antecedents and the two must
                      ;; not disagree about what the firing rests on
                      (let [antes (into all-antes (get support pctx))
                            post  (:post-join rule)
                            ;; the aggregates and whatever reads their output are
                            ;; computed *here*, in the conclusion's own context, and
                            ;; they extend the bindings every check below reads — so an
                            ;; exception or a NAF literal mentioning `?n` sees the count
                            ;; this placement rests on.  A rule without them pays one
                            ;; `seq` and keeps the substituted conclusion the join
                            ;; already built.
                            bindings (if (seq post)
                                       (post-join-bindings kb post bindings pctx)
                                       bindings)]
                        (when-not (or (nil? bindings)
                                      (some #(exception-holds? kb % bindings pctx) (:excepts rule))
                                      (naf-blocks? kb (:naf rule) bindings pctx)
                                      (let [hidden (res/excepted-handles kb pctx)]
                                        (and (seq hidden) (some hidden antes))))
                          (place-conclusion kb rule
                                            (cond-> conseq
                                              ;; they may have bound a consequent
                                              ;; variable the join left open
                                              (seq post) (res/substitute bindings))
                                            pctx antes depth bindings
                                            (:strength rule))))))
            placements))))

(defn- derive-conclusion
  "Record one rule firing at the rule's own justification strength (`:strength` on the
  rule view — a bare rule confers :monotonic and so caps the conclusion at its
  weakest antecedent, a `set/defaultRule` confers :default).  The justification is placed
  in the *maximal* contexts that see the rule and all antecedent facts (via
  genlContext); returns {:new [handles]} for any newly created sentexes.  The rule
  handle is part of the justification, so retracting the rule retracts its
  justifications.  A default conclusion is placed *unconditionally* — any defeat is
  decided at settle time, so belief is order-independent.

  A **head existential** `(exists ?y C)` leaves `?y` unbound after the antecedent
  substitution; it is skolemized to a deterministic constant here, before placement, so
  the fixpoint terminates (docs/skolem.md).  When the head is a conjunction the
  witness is shared across the conjuncts, which are placed one by one."
  [kb rule {:keys [bindings handles matched]} max-depth truncated]
  (let [depth (inc (reduce max 0 (map #(jtms/depth (:tms kb) %) handles)))]
    (if (> depth max-depth)
      (do (reset! truncated true) (when *tick* (*tick* 0)) {:new []})
      (let [raw0      (res/substitute (:consequent rule) bindings)
            ;; existential head variables are exactly the ones still unbound here; an
            ;; ordinary range-restricted rule leaves none and skips skolemization.
            ;; A post-join literal's output is unbound here too — it is computed per
            ;; placement — and it is emphatically not existential: skolemizing `?n`
            ;; would mint a constant where a count belongs.
            free      (let [f (free-consequent-vars raw0)]
                        (if-let [post (seq (:post-join rule))]
                          (seq (remove (into #{} (mapcat sx/deferred-output-vars) post) f))
                          f))
            raw       (if free (skolem/skolemize-conclusion kb rule raw0 bindings free) raw0)
            ;; a conjunctive skolemized head shares one witness across its conjuncts
            ;; (only a head existential stores a conjunctive consequent — an ordinary
            ;; one is split by `expand-consequent` before storage)
            conjuncts (if (and (sequential? raw) (= sx/and-functor (first raw)))
                        (vec (rest raw)) [raw])
            all-antes (conj (vec handles) (:rule-handle rule))
            ;; the matched records, fetched once: placement reads their contexts, and
            ;; the subsumption links read their functors
            facts     (mapv #(p/get-sentex (:records kb) %) handles)
            links     (subsumption-links kb matched (zipmap handles facts))
            new       (vec (mapcat #(place-conseq kb rule % all-antes facts links depth bindings)
                                   conjuncts))]
        ;; a firing is the finest unit of work the fixpoint has, so it is where a long
        ;; datum reports from — including a firing that placed nothing, since a join
        ;; grinding through matches that all turn out blocked is exactly the stretch that
        ;; otherwise looks hung
        (when *tick* (*tick* (count new)))
        {:new new}))))

(defn rule-view-of
  "The chainer's view of a rule sentex.  `:strength` is the justification class its
  firings confer, read off the record's `:defeasible` — the same authority the
  direction is read from, so a rule needs no separate index to know how it fires."
  [kb handle rsx]
  (let [s (:sentence rsx)]
    {:name handle :rule-handle handle :context (:context rsx)
     :antecedents (rules/antecedents s) :consequent (rules/consequent s)
     ;; A bare rule adds no defeasibility of its own, so it confers :monotonic and
     ;; the conclusion is capped by its weakest antecedent; a `set/defaultRule`
     ;; introduces defeasibility, so its conclusions are always :default.
     :strength (if (:defeasible rsx) :default :monotonic)
     ;; the `exceptWhen` exceptions — the queries of the belief-following meta-sentexes
     ;; naming this rule, block-if-any (`provers/rule-exceptions`).  Fetched only when
     ;; the cheap roster gate says the rule is watched, so an ordinary firing pays
     ;; nothing (docs/exceptions.md).
     :excepts (when (p/exception-rule? (:index kb) handle)
                (provers/rule-exceptions kb handle))
     ;; the negation-as-failure antecedents — `(unknown S)` literals, blocked the same
     ;; way an exception is, per placement context (docs/naf.md)
     :naf (rules/naf-antecedents rsx)
     ;; the aggregate antecedents and whatever consumes their output — evaluated per
     ;; placement context rather than in the join, since a census depends on where it
     ;; is taken and a comparison on one cannot run before it (docs/aggregate.md)
     :post-join (rules/post-join-antecedents rsx)}))

(defn- rule-view [kb handle]
  (rule-view-of kb handle (p/get-sentex (:records kb) handle)))

(defn- fire-rule
  "Apply a newly added rule over existing facts, at the rule's own strength."
  [kb rule-handle max-depth truncated]
  (let [{:keys [antecedents consequent] :as rule} (rule-view kb rule-handle)]
    (reduce (fn [nh state]
              (into nh (:new (derive-conclusion kb rule state max-depth truncated))))
            []
            (solve-rule kb antecedents {} (nm/functor consequent)))))

(defn- delta-fire-rule
  "Re-join one rule over a qualitative **delta**: the same full join `fire-rule` runs, but
  with one qualitative antecedent's enumeration narrowed to the pairs that moved
  (`*qualitative-delta*`), once per such antecedent.

  Falls back to the plain full join when the rule has no qualitative antecedent to narrow,
  or when nothing moved in any context that a delta could be taken for — a cold read, a
  retraction, a network gone unsatisfiable.  That is the same boundary the warm-started
  pass has, and for the same reason: what a widening invalidated is not computable from
  the answer it invalidated."
  [kb rule-handle rsx moved max-depth truncated]
  (let [qs (distinct (filter #(qualitative-antecedent kb %)
                             (rules/antecedents (:sentence rsx))))]
    (if (or (empty? qs) (every? #(= :all %) (vals moved)))
      (fire-rule kb rule-handle max-depth truncated)
      (reduce (fn [nh q]
                (binding [*qualitative-delta* {:literal q :moved moved}]
                  (into nh (fire-rule kb rule-handle max-depth truncated))))
              []
              qs))))

(defn- rejoin-qualitative
  "Re-join every forward rule mentioning `calc` because a fact of that calculus just
  arrived, and record what they were joined over.

  The re-join is in full rather than at a trigger position because the arriving fact need
  not unify with the antecedent it enabled: a new `nonTangentialProperPart` fact licenses
  a `partOfRegion` antecedent, and the trigger index will never connect the two.  What it
  *is* narrowed by is the delta — the pairs whose entailment has moved since the last time
  these same rules were joined.  A pair that has not moved licenses exactly the firings it
  licensed then, and those were derived then.

  The baseline is recorded whether or not any rule fired, and whether or not any pair
  moved, because \"joined over\" is a claim about this network and not about the outcome.
  It is recorded **after** the join, from the value read before it: the join places
  conclusions as it goes, and a conclusion of this calculus is a datum in its own right
  that will take the next delta against exactly this baseline."
  [kb calc rules max-depth truncated]
  (let [deltas (into {} (map (fn [c] [c (qkb/join-delta kb calc c)]))
                     (calculus-contexts kb calc))
        moved  (update-vals deltas :moved)
        fired  (reduce (fn [nh rh]
                         (let [rsx (p/get-sentex (:records kb) rh)]
                           (if (and rsx (rules/forward-sentex? rsx))
                             (into nh (delta-fire-rule kb rh rsx moved max-depth truncated))
                             nh)))
                       []
                       rules)]
    (doseq [[c d] deltas] (qkb/note-joined kb calc c (:baseline d)))
    fired))

(defn- fire-rules-for
  "Fire every forward rule a newly asserted fact can trigger — **strict and
  defeasible alike**.  Candidate rules are keyed by the fact's predicate and its
  supertypes (specificity), and each fires at its own strength (`rule-view-of`
  reads `:defeasible` off the record): a bare rule confers :monotonic and is capped
  by its weakest antecedent, a `set/defaultRule` confers :default.

  A default conclusion is placed **unconditionally**, with defeat decided afterwards
  by `settle` from the recomputed belief state, so firing order affects only how
  expensively a datum is found, never *what* is derived: the result is the least
  fixpoint of a monotone immediate-consequence operator regardless of order.  A bare
  consequence of a default conclusion still arrives, because that conclusion lands on
  the agenda and triggers bare rules like any other new datum.  The depth guard
  applies equally — a default conclusion carries `1 + max` antecedent depth through
  `derive-conclusion`, so a default rule cannot outrun `:max-depth` any more than a
  bare one can, and its truncation reaches the run's `:truncated?` flag."
  [kb datum max-depth truncated]
  (let [fact     (:sentence (p/get-sentex (:records kb) datum))
        ffn      (nm/functor fact)
        preds    (tax/genls (:taxonomy kb) ffn)
        ;; the antecedent index is complete, so each candidate's own record decides
        ;; whether it may fire here: forward-capable is the only question
        rhs      (into #{} (mapcat #(p/rules-by-antecedent (:index kb) %)) preds)
        ;; A qualitative fact changes the *whole* network, so it can license an
        ;; entailment on any predicate of its calculus — including predicates the
        ;; trigger index would never connect it to, since a new `ntpp` fact licenses a
        ;; `partOfRegion` antecedent and the two are unrelated by genl.  Those rules go
        ;; to `rejoin-qualitative`, which re-joins them over the pairs that moved rather
        ;; than at a trigger position.  A *negative* fact reaches its calculus by the
        ;; predicate under the `not`: its own functor names nothing, and it narrows the
        ;; network by the complement of the denotation exactly as a positive one narrows
        ;; it by the denotation, so it too can entail a relation nobody stated — and the
        ;; arriving fact is the only thing that queues the re-join that finds one.
        ;;
        ;; Which is a symbol comparison, not a peel: the functor is in hand either way,
        ;; and only a `not` pays `body-under-not` (structural, on a record's already
        ;; canonical sentence — `sx/underlying-body` would rebuild and re-intern the
        ;; whole sentence to answer the same question).  This runs per datum for every
        ;; fact a chaining run touches, qualitative or not and prover or none.
        qcal     (qkb/calculus-for kb (if (= sx/not-functor ffn)
                                        (nm/functor (kb/body-under-not fact))
                                        ffn))
        qrhs     (when qcal
                   (into #{} (mapcat #(p/rules-by-antecedent (:index kb) %))
                         (:predicates qcal)))
        trigger  (if qrhs (remove qrhs rhs) rhs)
        forward? (fn [rsx] (and rsx (rules/forward-sentex? rsx)))]
    (into
     (reduce
      (fn [nh rh]
        (let [rsx (p/get-sentex (:records kb) rh)]
          (if-not (forward? rsx)
            nh
            (let [{:keys [antecedents consequent] :as rule} (rule-view-of kb rh rsx)
                  cpred (nm/functor consequent)]
              (reduce (fn [nh2 i]
                        (if-let [b0 (res/match1 kb (nth antecedents i) fact)]
                          (reduce (fn [nh3 state]
                                    (into nh3 (:new (derive-conclusion kb rule state max-depth truncated))))
                                  nh2
                                  (complete-antecedents kb antecedents i datum b0 cpred))
                          nh2))
                      nh
                      (range (count antecedents)))))))
      []
      trigger)
     (when (seq qrhs)
       (rejoin-qualitative kb qcal qrhs max-depth truncated)))))

(defn- process-datum
  "In a global chain, a rule datum fires if it is forward-capable — defeasible or
  not (a backward/inert rule never forward-chains).  A fact fires the rules keyed
  by it.

  `*qcn-contexts*` is bound **per datum**, and the scope is the point.  Which contexts a
  calculus has facts in is a function of the store, and a run changes the store — so
  caching it across the whole run would let a rule that concludes a qualitative relation
  go on reading the contexts as they were before.  Per datum is safe *because* a placed
  qualitative conclusion becomes a datum in its own right, and processing that datum
  re-joins every rule mentioning its calculus (`fire-rules-for`).  So a context enabled
  mid-datum is not lost, only deferred by one agenda step — which is what the fixpoint is
  for.

  The networks are resident on the KB and stamped with the change clock, so they need no
  cache of their own here — but they do need `observe/with-pin`, and for a reason the
  clock cannot supply.  A join is a lazy seq whose solutions are *placed* as they are
  taken, so the datum writes while it reads; pinning is what makes the whole step join
  against one network rather than against a network that moves under it."
  [kb datum max-depth truncated]
  (observe/with-pin
    (binding [*qcn-contexts* (atom {})]
      (let [sx (p/get-sentex (:records kb) datum)]
        (if (rules/rule? sx)
          ;; direction and defeasibility are read straight off the record — the sentex
          ;; is already in hand, and it is what the set/*Rule wrapper set.  A defeasible
          ;; rule fires here too, at :default (see fire-rules-for).
          (if (rules/forward-sentex? sx)
            (fire-rule kb datum max-depth truncated)
            [])
          (fire-rules-for kb datum max-depth truncated))))))

(defn chain
  "Semi-naive fixpoint forward chaining seeded with `seed`, strict and defeasible
  rules together on the one agenda.

  `opts` may carry an **`:on-progress`** callback, called about four times a second
  (`:progress-every-ms`) with
  `{:derived n :pending n}` — what the run has concluded, and how much agenda is left.  A
  fixpoint has no total to count towards (the agenda grows as it derives), so those two
  numbers are the honest reading of where a run is; both are O(1) to take.  The callback
  may **throw**, which aborts the run — the one interruption point chaining has, and how a
  loader cancels one.  What had already been derived stays: the conclusions are placed as
  they are made, so an aborted fixpoint is a KB holding a prefix of the run, not a corrupt
  one.

  Reporting happens at two points, and it takes both to keep a bar moving: at the agenda
  loop, which sees the run between datums, and at each rule firing (`*tick*`), which is
  inside the one datum that can run for minutes.  The remaining silent stretch is a single
  *unproductive* join — a match search that yields nothing for a long time never reaches a
  firing — which is bounded by the extent it is scanning rather than by the corpus."
  [kb seed opts]
  (let [{:keys [max-depth max-derivations on-progress progress-every-ms]}
        (merge default-chain-opts opts)
        interval  (* (long (or progress-every-ms default-progress-ms)) 1000000)
        truncated (atom false)
        ;; the run's own counters, off the loop vars so a report from inside a datum sees
        ;; the same numbers the loop does.  Chaining is single-threaded (the one-writer
        ;; contract), so a volatile is the whole of the synchronization needed.
        placed    (volatile! 0)
        pending   (volatile! (count seed))
        reported  (volatile! (System/nanoTime))
        report!   (fn [] (vreset! reported (System/nanoTime))
                    (on-progress {:derived @placed :pending @pending}))
        due?      (fn [] (>= (- (System/nanoTime) @reported) interval))]
    ;; the tick is bound whether or not anybody is listening: it is also how the run
    ;; counts what it derived, and the loop no longer sees that between datums.
    ;; The handle cache is engaged for the same scope, and for the reason that scope
    ;; exists: a fixpoint asks "is this conclusion already stored?" once per witness, so
    ;; a conclusion reached k ways is k walks of the trie to a handle this run minted
    ;; itself.  Nothing is removed from the store inside a run — `settle` runs after it —
    ;; so every entry stays true for as long as the cache is bound.
    (observe/with-handle-cache
      (binding [*tick* (fn [n]
                         (vswap! placed + n)
                         (when (and on-progress (due?)) (report!)))]
        (loop [agenda (into clojure.lang.PersistentQueue/EMPTY seed)]
          (if (or (empty? agenda) (>= @placed max-derivations))
            (do (vreset! pending (count agenda))
                (when on-progress (report!))
                {:derived @placed :truncated? (or @truncated (>= @placed max-derivations))})
            (let [d       (peek agenda)
                  new-hs  (process-datum kb d max-depth truncated)
                  agenda' (into (pop agenda) new-hs)]
              (vreset! pending (count agenda'))
              (when (and on-progress (due?)) (report!))
              (recur agenda'))))))))

(defn chain-all
  "One fixpoint from `seed`, strict and defeasible rules on the same agenda (there
  is no separate defaults phase — see `fire-rules-for`).

  Opens a new run in `chain-stats` — violations recorded during the run carry its
  id — and stashes the result there, warning when the run was truncated.  The ledger
  **accumulates** across runs rather than resetting per run, so a bulk load's drops
  stay observable one assert later; and because internal callers discard the
  `:truncated?` flag, the :warn log is how a depth-capped chain's lost conclusions
  surface."
  [kb seed opts]
  (swap! (:chain-stats kb) update :runs inc)
  (let [result (chain kb seed opts)]
    (swap! (:chain-stats kb) assoc :last result)
    (when (:truncated? result)
      (trove/log! {:level :warn :id ::chain-truncated
                   :msg "forward chaining was truncated (max-depth or max-derivations) — conclusions are missing"
                   :data result}))
    result))

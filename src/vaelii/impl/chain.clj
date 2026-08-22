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
            [vaelii.impl.inherit :as inherit]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.plan :as plan]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.qcn-kb :as qkb]
            [vaelii.impl.quasiquote :as quasiquote]
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
  verbatim.  See docs/inference.md, \"Incremental rule matching\".

  With the reference bound, a substituted antecedent that has a bound indexable
  argument **and a functor with sub-predicates** is read through
  `res/matches-hierarchical` instead (`join-matches`) — the same set by an argument
  lead rather than a trie walk per sub-predicate.  Binding this var to anything else
  switches that off, so the seam's caller sees every non-trigger antecedent."
  res/match-pattern)

(def ^:dynamic *suppress-duplicate-firings*
  "Whether a run generates each satisfying antecedent combination **once** rather than
  once per side that can trigger it (see `*agenda-arrivals*`).  On by default; bound
  **false** to enumerate every trigger, which is the reference side the oracles compare
  against (`witness_order_test`, `rete_oracle_test`).  A pure cost decision: the
  suppressed firings are duplicates of ones the run makes anyway, so the derived set
  and its supports are the same either way."
  true)

(def ^:dynamic *agenda-arrivals*
  "A mutable `{handle -> arrival}` map — the position at which each datum joined this
  run's agenda — or nil, and then nothing is suppressed.

  **This decides work, not belief.**  A rule `a(x,y) <- b1(x,z), b2(z,y)` is triggered
  by its `b1` datum at position 0 and by its `b2` datum at position 1, and both
  enumerate the same pair: the second runs the whole join, rebuilds the same
  conclusion, resolves the same placement contexts, and is thrown away by
  `jtms/has-justification?`.  Ordering the agenda's datums lets one of the two skip the
  work — the firing that survives is *identical* whichever side makes it (same
  bindings, same antecedent set, same justification), so the derived set and its
  supports are unchanged by construction.  Nothing here is read when belief is
  computed, and no tie-break anywhere keys on it: the engine's rule that belief never
  tie-breaks on a handle is untouched, because this is not consulted about belief.

  **Arrival order, not handle order**, and the difference is the whole correctness
  argument.  For a datum the run itself derives the two agree — handles are allocated
  in creation order and a new conclusion is enqueued as it is placed — but a datum put
  **back** on the agenda has an old handle and a fresh arrival: a fact revived from OUT,
  a fact newly matchable under a derived `genl` edge (`special/subsumption-seeds`), a
  seed list in whatever order `jtms/in-datums` produced.  Keyed on arrival, such a
  datum sorts *after* the partner that was already processed, so it is the one that
  enumerates the pair, and the pair is enumerated.  Keyed on the handle it would sort
  before it and the pair would be lost.

  A handle the run never enqueued has **no** arrival and is never suppressed against:
  nothing else will enumerate its combinations, so they are all made here.  That covers
  a sentex some other write placed while the run was going — a migrated twin the caller
  has not seeded yet — and every join run outside a chaining run at all.  A
  **disbelieved** trigger declines the filter outright, for the reason `arrival-admit`
  states.

  Bound by `chain` for the length of a run, like the handle cache and the dedup index,
  and it is the agenda that bounds its size.  A `java.util.HashMap` rather than an atom
  because the engine is single-writer and this is read once per candidate the join
  yields."
  nil)

;; ---- exceptWhen: evaluating the exception -------------------------------
;; The exception is **any closed level-6 query** once the rule's bindings are
;; substituted in.  Level 6 (`:solved`) is the full prover stack *minus* rule
;; backchaining, so an exception reaches through genl specificity, the genlCx
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
    open-world reading, and it matches `arg`, where an argument whose type is
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
  in `pctx`?  Run exactly like an exception — `provers/exception-holds?` over the
  query's conjuncts — so `unknown` and `exceptWhen` share one level-6 evaluator and
  cannot drift; a nested `thereExists` is dispatched to its prover from there.  When it
  holds, `S` is derivable, so `(unknown S)` is false and the firing is blocked.

  A conjunctive query is the same block-if-**all**-hold the exception's conjuncts are,
  and for the same reason: closure leaves each conjunct ground, so they share nothing
  and need no join."
  [kb unk bindings pctx]
  (provers/exception-holds? kb (sx/naf-query-conjuncts unk) bindings pctx))

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

(def ^:dynamic *declarations-cell*
  "Per-run cache of `inherit/declarations-exist?` — whether the KB declares any
  preservation at all — as a volatile holding the answer, or nil (unknown, read on the
  next ask); the var itself is nil outside a chaining run, where the gate reads the
  index.

  `preserving-antecedent?` is asked of every non-trigger antecedent of every firing
  attempt, and its first question is this one: two cardinality reads that answer false
  for nearly every KB there is.  Bound once by `chain`, like `*evaluatable-preds*`, and
  unlike it **invalidated** from inside the run: a run can *derive* a declaration, and
  every join after that placement must see it — the datum that placed it re-joins the
  rules it moved (`inherit/rejoin-rules`), and a datum arriving later triggers them
  afresh, both through this gate.  `derive-conclusion` resets the cache when a placed
  conclusion **roots** at a declaration functor (`placed-functor`, since the conclusion
  the join hands over may still be wearing an `ist` frame or a `not`), so the next ask
  pays the two reads once more and caches the true.  A declaration leaves only outside a
  run (`retract!`), so a cached true never goes stale inside one."
  nil)

(defn- declarations-exist?
  "The run's cached answer when a run has bound one (reading the index once per
  invalidation), else `inherit/declarations-exist?` live."
  [kb]
  (if-let [v *declarations-cell*]
    (if-some [x @v]
      x
      (vreset! v (inherit/declarations-exist? kb)))
    (inherit/declarations-exist? kb)))

(defn- placed-functor
  "The functor a conclusion literal roots at **once it is placed**, which is not always
  the functor it is written with.  An `(ist Ctx S)` names the context S goes into and
  places S (`place-conseq`), and a negation roots under its positive body's predicate
  (`kv/root-keys` — polarity lives in the record, so `(not (p a))` counts under `p` and
  never under `not`).  So neither `ist` nor `not` is ever the answer here, and a
  conclusion wearing either would otherwise be read as a functor no declaration uses."
  [c]
  (when (sequential? c)
    (let [c (if (= sx/ist-functor (nm/functor c)) (nth c 2 nil) c)
          f (nm/functor c)]
      (if (= sx/not-functor f) (nm/functor (kb/body-under-not c)) f))))

(defn- note-placed-declaration!
  "A placed conclusion roots at a preservation declaration's functor: forget the run's
  cached answer to whether any exist, so the next join asks again.

  Asked of every firing that reached placement, whether or not it minted a handle: a
  conclusion that dedups onto a stored sentex places a *justification*, which is what
  makes the declaration believed, so \"nothing new was created\" is not \"nothing
  changed\".  Only a cached **false** can go stale — a declaration leaves only outside a
  run (`retract!`) — so a run that has not yet answered the question, or has answered it
  yes, skips the scan."
  [conjuncts]
  (when-let [v *declarations-cell*]
    (when (and (false? @v)
               (some #(contains? inherit/declarations (placed-functor %)) conjuncts))
      (vreset! v nil))))

(defn- preserving-antecedent?
  "Does `ante` name a predicate carrying a preserved argument position, visible from
  `context`?  False for every literal in a KB that declares no preservation, at the
  cost of the gate in front of `inherit/positions` — read once per chaining run
  (`*declarations-cell*`, re-read after a derived declaration), so the per-antecedent
  cost there is a var deref and a symbol test.

  A negation is not one: preservation licenses claims and never refutations, which is
  the same line `inherit/ground-goal?` draws."
  [kb ante context]
  (and (sequential? ante) (seq ante)
       (let [f (nm/functor ante)]
         (and (symbol? f) (not= 'not f) (seq (nm/args ante))
              (declarations-exist? kb)
              (boolean (seq (inherit/positions kb f context)))))))

(defn- inheritance-withdrawn?
  "Was this firing licensed by an inherited claim the KB no longer licenses?

  A justification's antecedents cannot express that.  They name the claim that was
  stated, the declaration that licensed the move and the relation edges the reach
  travelled — and every one of them is still stored and believed when a **more specific
  contrary claim** arrives and undercuts what they licensed.  Nothing is defeated
  there: the general claim simply stops firing for that tuple (docs/inherit.md), so
  there is no label to read the withdrawal off.  The firing is blocked the way an
  excepted one is, and revived by the same machinery when the specific claim goes.

  Asked only of an antecedent the KB does **not** state at the bound tuple.  A stored
  claim is withdrawn by its own handle going, and asking `verdict` about one would
  block an ordinary firing over a pair the KB happens to hold in both polarities —
  which is a represented dilemma the chainer has never refused to fire on.

  In the conclusion's context, like every other re-check here: a specific claim that
  context cannot see is not one it should defer to, and everything the firing rests on
  is visible from there by construction, placement having required it.

  `bindings` is a delay, forced only once a preserved antecedent is found — every rule
  reaches here and almost none names one."
  [kb rsx bindings pctx]
  (let [as (filterv #(preserving-antecedent? kb % pctx) (:antecedent rsx))]
    (boolean
     (and (seq as)
          (some (fn [a]
                  (let [g (res/substitute a @bindings)]
                    (and (inherit/ground-goal? g)
                         (not-any? #(jtms/in? (:tms kb) (first %))
                                   (res/matches-visible kb g pctx))
                         (not= :for (inherit/verdict kb g pctx)))))
                as)))))

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

(defn- antecedent-hidden?
  "Does a believed visibility `except` hide one of `antes` from `pctx`?  A derivation
  resting on an antecedent the conclusion's context cannot see is invalid there.

  Asked per antecedent (`res/hidden-fn`) rather than against the materialized hidden set,
  because this runs once per placement and once per candidate justification, and a rule
  has two or three antecedents where a cone can hide thousands of handles.  A nil
  predicate is the gate — a KB that hides nothing from `pctx` pays a deref and returns
  here.  A rule handle among `antes` never spuriously matches: a rule is not an `except`
  target."
  [kb antes pctx]
  (if-let [hidden? (res/hidden-fn kb pctx)]
    (boolean (some hidden? antes))
    false))

(defn- rule-firing-blocked?
  "Is a firing of the rule stored at `rh` — settled bindings `bindings` (a delay),
  placed in `pctx` — blocked by something the *rule* carries: its `exceptWhen`
  exception, an `(unknown S)` antecedent whose `S` is now derivable, an **aggregate**
  antecedent whose count has moved, an **inherited** antecedent a more specific claim
  has undercut, or the qualitative network it joined on having become unsatisfiable?

  The context is the **conclusion's**, not the rule's: an exceptWhen query and a NAF
  literal are *about* the conclusion, and one invisible from where it lives has no
  business blocking it.  Nothing is cached: this re-runs the checks every time, which is
  what keeps blocking from drifting out of step with belief.

  Both re-decision paths come here — a firing that *was* placed and is now a
  justification, and one that was refused before it could become one — so the two cannot
  drift about what counts as blocked."
  [kb rh rsx bindings pctx]
  (boolean
   (or (when (or (rules/has-naf? rsx) (p/exception-rule? (:index kb) rh))
         (or (provers/exceptions-block? kb rh @bindings pctx)
             (and (rules/has-naf? rsx)
                  (naf-blocks? kb (rules/naf-antecedents rsx) @bindings pctx))))
       (post-join-withdrawn? kb rsx bindings pctx)
       (inheritance-withdrawn? kb rsx bindings pctx)
       (entailment-withdrawn? kb rsx pctx))))

(defn justification-excepted?
  "Is justification `j` currently blocked — by a visibility `except` hiding one of its
  antecedents, or by anything its rule carries (`rule-firing-blocked?`)?

  The conclusion's record names the placement context every check is evaluated in, and
  the informant names the rule."
  [kb j]
  (boolean
   (when-let [csx (p/get-sentex (:records kb) (:consequence j))]
     (let [pctx (:context csx)
           inf  (:informant j)]
       (or (antecedent-hidden? kb (:antecedents j) pctx)
           (when (integer? inf)
             (when-let [rsx (p/get-sentex (:records kb) inf)]
               (rule-firing-blocked? kb inf rsx
                                     (delay (settled-bindings kb (:bindings j) pctx))
                                     pctx))))))))

;; ---- forward chaining ---------------------------------------------------

;; **Deferred antecedents.**  A deferred (evaluable) literal — `lessThan`,
;; `greaterThan`, `evaluate`, `different` (`sentex/deferred-predicates`), and a
;; predicate the KB registered with `add-evaluatable` (`deferred-antecedent?`) — is not
;; a stored fact.  It is *computed* from the bindings the other antecedents produced,
;; which is why `vaelii.impl.sentex` holds a built-in back to the end of the canonical
;; antecedent order and `vaelii.impl.plan` pulls it forward only once its inputs are
;; bound.  Joining it with `match-pattern` therefore looks up a fact nobody ever
;; stored, finds nothing, and kills the whole join — silently, since an empty join is
;; indistinguishable from a rule that simply had nothing to fire on.  The backward
;; chainers never had that bug because they discharge every antecedent through
;; `provers/solve-goal`, where the evaluable provers live.  The join below goes to the
;; same registry rather than growing a second evaluator that could disagree with it.
;;
;; A **registered evaluatable** takes the same path, so `ask` agrees with `query` on a
;; forward rule with an evaluatable antecedent.  It differs from a built-in in one
;; respect: it is per-KB, so it is not in the static `deferred-predicates` set the
;; canonical order pins on, and `planned-join` pins it after its binders by cost instead
;; (`provers/evaluatable-est-override`) — which is what keeps the firing order-independent
;; whether the facts or the rule arrive first.

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
    ;; The unbound-input guard is for the built-in deferred literals, whose input/output
    ;; split `sentex/deferred-input-vars` knows statically.  A KB evaluatable's output
    ;; slot is the prover's (`add-evaluatable`'s `:result`), which is not in that map, so
    ;; a result-binding evaluatable's own output would read here as an unbound *input* and
    ;; throw spuriously.  Its readiness is left to the prover instead — `EvaluatableFn`
    ;; yields nothing until its inputs are ground — and `planned-join`'s `est-override`
    ;; orders it after their binders so it lands ground.
    (when (sx/deferred-literal? literal)
      (when-let [unbound (seq (sx/deferred-input-vars g))]
        (throw (ex-info (str "deferred antecedent " (pr-str g) " reached the join with unbound "
                             "input " (pr-str (vec unbound)) " — it is computed, not looked up, "
                             "so an earlier antecedent must bind its inputs")
                        {:type :unbound-deferred :literal literal :goal g :unbound (vec unbound)}))))
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
  network, and where its facts span contexts a `genlCx` closure besides, so it
  is cached for the length of a chaining run rather than recomputed per antecedent per
  binding.  Bound by `chain`; nil outside one, where it simply recomputes."
  nil)

(defn- calculus-contexts
  "The networks worth re-joining `calc` against — `qcn-kb/reader-contexts`, cached for
  the length of a chaining run.

  A network is what a **reader** sees, and a reader sees the whole `genlCx` cone
  above it, so the contexts that merely *hold* a fact are not the networks a forward
  rule may join on: a context inheriting two contexts composes what neither
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
  prover.  Nil is not free: `qkb/calculus-for` rebuilds the registered-calculus list per
  call, so a KB that opted into nothing still pays an `instance?` test per prover in the
  registry, here once per antecedent literal of every rule considered.  A constant in the
  registry's size and no store read, which is what makes it affordable on that path —
  not an absent cost.  The shape gate in front of it is the real saving, and it is
  arity-only: positive binary literals, a negated one being refuted by the network rather
  than entailed by it, and what a refutation rests on is the whole network rather than a
  support list."
  [kb ante]
  (when (and (sequential? ante) (= 3 (count ante)) (symbol? (first ante)))
    (qkb/calculus-for kb (first ante))))

;; ---- inherited antecedents: joining on a claim nobody stored -------------
;; `(transitiveInArg P n R)` makes a stored `(P … W …)` license `(P … A …)` for every A
;; in W's reach (docs/inherit.md).  Backward chaining discharges such an antecedent
;; through `TransitiveInArgProver`; forward chaining could not, and the reason was the
;; qualitative one — an inherited claim is not stored, so it has no handle for a
;; justification to rest on, and `sentexes-matching` and `ask` came back with different
;; answers about the same knowledge.
;;
;; Support closes it here too.  `inherit/solve-with-support` answers the antecedent by
;; the reach and hands back the handles the claim was **read from** — the claim that
;; was stated, the declaration licensing the move, and the relation edges the reach
;; travelled — so the conclusion is withdrawn when any of them goes, `why` names the
;; actual reasons, and the conclusion may only be placed where they can all be seen.
;;
;; **Union, not replacement**, and for the same reason it is on the qualitative side: a
;; stored claim keeps matching exactly as it does now, the inherited ones are added,
;; and the diagonal — a claim stated at the very tuple it is asked about — is dropped
;; from this path rather than handed a second justification resting on nothing new.

(defn- solve-preserving
  "Solve an antecedent by **preservation**, against the claims stored anywhere.  Each
  solution carries the handles the inherited claim rests on, so the firing's
  justification names them and retraction reaches them.

  The context is `'?ctx` throughout, exactly as the ordinary matcher's is: which claims
  exist is not the placement's question, and the reasons this hands back are what
  placement then reads to decide where the conclusion may live."
  [kb literal states]
  (let [af (nm/functor literal)]
    (for [{:keys [bindings handles matched]} states
          :let [g (res/substitute literal bindings)]
          {b :bindings sup :handles claim :claim} (inherit/solve-with-support kb g '?ctx)]
      ;; the claim satisfied the antecedent like any other match, and it may have done
      ;; so through a sub-predicate — so it is paired with the antecedent's functor and
      ;; `subsumption-links` reads the taxonomy edges *that* pairing rests on.  The
      ;; declaration and the reach edges are not paired: they are what licensed the
      ;; move, not facts that matched a pattern.
      {:bindings (merge bindings b) :handles (into handles sup)
       :matched  (conj matched [af claim])})))

(defn- mirrored-antecedent?
  "Is `ante` a literal the matcher answers through the **symmetric mirror** — a binary
  literal any of whose sub-predicates is declared `symmetric` (`res/raw-match`)?

  Such a position takes no arrival filter, and the reason is an asymmetry between the
  two ways a rule reaches a fact.  The join runs `*matcher*`, which probes both
  argument orders; the trigger runs `res/match1`, which is a plain unify and does not.
  So `(siblingOf ?y ?z)` joined under `?y = I3` finds the stored `(siblingOf I2 I3)`
  by its mirror, while that same fact arriving as a datum unifies only as
  `?y = I2, ?z = I3` and reaches a different firing.  Suppressing the join hit would
  hand the pair to a trigger that cannot make it.

  The sub-predicate closure rather than the functor alone, because `match-pattern`
  fans the functor first and mirrors each fanned literal on **its** own declaration.
  Driven from the declared symmetric predicates (a handful) tested against the closure,
  as `matches-hierarchical` does, rather than the closure scanned for a mark: a broad
  functor's closure is the whole type hierarchy, and this runs per join."
  [kb ante]
  (and (sequential? ante) (= 3 (count ante))
       (let [f (nm/functor ante)]
         (and (symbol? f) (not (sx/variable? f))
              (let [tx    (:taxonomy kb)
                    specs (res/sub-predicates kb f nil)]
                (boolean (some #(contains? specs %) (tax/props tx :symmetric))))))))

(defn- symmetric-mirror
  "The mirror of `fact` when the KB reads it as one — a binary literal whose own
  predicate is declared `symmetric`, and whose arguments differ — else nil.

  A symmetric fact is stored in one orientation (the canonical sort) and *means* both,
  which is why `res/raw-match` probes both when a join reaches it.  A trigger reaches it
  the other way round: the fact arrives and `res/match1` unifies it as written, so the
  combination that needs the mirror is enumerated by nobody, and the same two facts
  derive a conclusion or not depending on which arrived second.  Asked of the **fact**
  and once per datum: it is the fact's own declaration that makes its mirror true, and a
  super-predicate being symmetric says nothing about the sub the fact is stated at."
  [kb fact]
  (when (and (sequential? fact) (= 3 (count fact)))
    (let [f (nm/functor fact)]
      (when (and (symbol? f) (not (sx/variable? f))
                 (contains? (tax/props (:taxonomy kb) :symmetric) f))
        (let [m (sx/mirror-literal fact)]
          (when-not (= m fact) m))))))

(defn- trigger-bindings
  "The binding maps a datum makes at one antecedent position: what `fact` unifies to,
  and what its symmetric `mirror` unifies to when there is one and it binds differently.

  Two rather than one is what keeps a symmetric antecedent at the *trigger* position
  reading the same as it does at a join position, and with it the run's independence from
  arrival order.  Distinct, because an antecedent that binds both orientations the same
  way (a repeated variable, or a position the mirror does not reach) has made one firing,
  not two — and a duplicate would be a second justification for a conclusion the first
  already carries."
  [kb ante fact mirror]
  (let [b0 (res/match1 kb ante fact)
        b1 (when mirror (res/match1 kb ante mirror))]
    (cond
      (and b0 b1 (not= b0 b1)) [b0 b1]
      b0                       [b0]
      b1                       [b1]
      :else                    nil)))

(def ^:dynamic *evaluatable-preds*
  "Per-run cache of the KB's `add-evaluatable` predicate functors
  (`provers/evaluatable-preds`) — the ones forward chaining computes through the prover
  registry instead of looking up as stored facts, exactly as it does the built-in
  `sentex/deferred-predicates`.  Bound once per run by `chain`, since the registry is
  fixed for the run and rebuilding the set per antecedent would allocate on the hot join
  path.  Nil outside a run — the `solve-rule` `why-not` reaches through, say — where
  `deferred-antecedent?` reads the registry directly.  Empty for the common KB with no
  registered evaluatables."
  nil)

(defn- evaluatable-antecedent-preds
  "This KB's registered evaluatable functors, from the per-run cache when a chaining run
  has bound it, else read straight off the registry (`provers/evaluatable-preds`)."
  [kb]
  (or *evaluatable-preds* (provers/evaluatable-preds kb)))

(defn- deferred-antecedent?
  "Is `ante` a **computed** antecedent for `kb` — a built-in evaluable
  (`sentex/deferred-predicates`) or a predicate the KB registered with
  `add-evaluatable`?  Forward chaining discharges these through the prover registry
  (`solve-deferred`) rather than looking them up with `*matcher*`, so `ask` reaches the
  same evaluatable the query engine's leaf does and the two agree on a rule with an
  evaluatable antecedent.

  A registered evaluatable is *not* in canonical antecedent order's deferred set (that
  set is static, evaluatables are per-KB), so `planned-join` instead pins it after its
  binders with `provers/evaluatable-est-override` — which is why the ordering holds
  regardless of assertion order.

  Called per antecedent on the join hot path, so the registered-evaluatable arm is gated
  on a non-empty predicate set first: the common KB registers none, so this collapses to
  the built-in `sx/deferred-literal?` check with only a set-empty test added."
  [kb ante]
  (or (sx/deferred-literal? ante)
      (let [preds (evaluatable-antecedent-preds kb)]
        (and (seq preds)
             (sequential? ante) (seq ante)
             (contains? preds (first ante))))))

(defn- fanning-functor?
  "Does `g`'s functor have a fan for the argument lead to collapse — a sub-predicate
  closure wider than the functor itself, or a **variable** functor, which names no
  predicate and so puts every argument behind it at level 0 of the trie?

  The closure is reflexive, so `> 1` is \"something other than the functor is in it\".
  Read at the wildcard vantage, which is the one `join-matches` matches at: the global
  closure, memoized on the taxonomy generation (`tax/specs`), so this is a cached set
  and a `count` rather than a walk."
  [kb g]
  (let [f (first g)]
    (or (sx/variable? f)
        (> (count (res/sub-predicates kb f '?ctx)) 1))))

(defn- join-matches
  "The stored facts satisfying the substituted antecedent `g` at the wildcard context —
  `[handle bindings …]` pairs, the set `res/match-pattern` returns.

  Two readers answer the same question, and the choice between them is the one the
  query side already makes (`res/matches-visible`).  `*matcher*` is the reference: the
  count-aware trie, one walk per member of the functor's sub-predicate closure, and the
  seam the rete alpha matcher binds.  For a literal with a **bound indexable argument**
  — a type test `(animal ?x)` with `?x` already bound, the commonest non-trigger
  antecedent there is — that fan is `|specs|` trie walks to confirm one membership (364
  for `animal` on the starter, six figures under a `thing`-rooted antecedent on a large
  KB) per firing attempt, where `res/matches-hierarchical` leads from the argument's
  own postings: one predicate-agnostic slot read narrowed to the closure in memory, or
  one scoped read per spec when that side is smaller (`res/*lead-side*`).  Same belief
  filter, same polarity check, same symmetric mirror, same exceptWhen-meta skip, and the
  same `?ctx` binding — `matches_hierarchical_test` holds the two to the identical set.

  **The lead is for the fan, so a functor with no sub-predicates keeps the trie.**  A
  singleton closure is `match-pattern`'s own fast path — one cached set lookup and a
  single `raw-match`, whose `candidate-handles` already reads the argument roots for the
  shape the trie cannot narrow (a ground argument behind a variable) and the trie for the
  shapes it can.  There is no `|specs|` fan there to collapse, and the lead is not free:
  three volatiles, a pattern memo, two `prof/profiling?` derefs and `lead-agnostic?`'s
  own `count-with-arg` probe.  Measured over 2,000 firings of a binary join on `:memory`,
  the same 2,000 conclusions: 52,003 index reads through the lead against 48,003 through
  the trie, and the whole difference is the argument families.  `fanning-functor?` is the
  gate, and `join_lead_cost_test` measures at width 0 as well as at 4 and 16 so a lead
  taken over nothing fails there.

  The lead is taken only when the reference matcher is the one bound: a rete run keeps
  its seam, and `res/*hierarchical-retrieval*` false (the reference-retrieval sweep)
  keeps the trie everywhere, so the join is the reference under exactly the bindings
  the rest of the engine is."
  [kb g]
  (if (and res/*hierarchical-retrieval*
           (identical? *matcher* res/match-pattern)
           (res/lead-literal? g)
           (fanning-functor? kb g))
    (res/matches-hierarchical kb g '?ctx)
    (*matcher* kb g '?ctx)))

(defn- join-antecedent
  "Extend the partial join `states` ({:bindings :handles :matched}) by one antecedent.

  `admit` is the arrival filter on the handles this antecedent yields — a
  `(fn [handle] -> boolean)` from `complete-antecedents`, or nil for no suppression
  (`*agenda-arrivals*`).  **Three** positions decline it, and the rule is the same one
  each time: the join reaches a satisfier no trigger can, so there is nothing to order
  it against.  A **qualitative** antecedent draws its handles from what a network
  entails rather than from the fact that satisfied it; an **inherited** one is
  satisfied by a claim nobody stored, whose handles name the stated claim, the
  declaration and the reach edges rather than the tuple that matched; and a
  **mirrored** one is reachable by the join and not by the trigger
  (`mirrored-antecedent?`).  The first two decline it structurally — the filter is
  applied to `hit` alone, and both arrive by their own `concat`.  Declining is always
  safe — it re-derives a duplicate the TMS already rejects — where suppressing wrongly
  loses a firing.

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
  [kb ante states admit]
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

    (deferred-antecedent? kb ante)
    (mapcat (fn [{:keys [bindings handles matched]}]
              (map (fn [b] {:bindings b :handles handles :matched matched})
                   (solve-deferred kb ante bindings)))
            states)

    :else
    (let [af    (nm/functor ante)
          calc  (qualitative-antecedent kb ante)
          keep? (when (and admit (nil? calc) (not (mirrored-antecedent? kb ante))) admit)
          hit   (mapcat (fn [{:keys [bindings handles matched]}]
                          (for [[h b2] (join-matches kb (res/substitute ante bindings))
                                :when (or (nil? keep?) (keep? h))]
                            {:bindings (merge bindings b2) :handles (conj handles h)
                             :matched  (conj matched [af h])}))
                        states)]
      (if calc
        (distinct (concat hit (solve-qualitative kb calc ante states)))
        (if (preserving-antecedent? kb ante '?ctx)
          (distinct (concat hit (solve-preserving kb ante states)))
          hit)))))

(defn- planned-join
  "Order `antecedents` by estimated fan-out under the bindings already in hand (`b0`),
  then join them left to right from `seed`.  Reordering a conjunction changes only how
  fast the answer is reached, never the answer set — and justification dedup is
  set-based (`jtms/has-justification?`), so the reordered `:handles` still dedup — so
  this is a pure cost decision, the same one `res/planned-antecedents` makes for the
  backward chainers.  `plan/order` pins the operational literals exactly as canonical
  antecedent order did: the deferred (evaluable) and `unknown` (NAF) literals never
  outrun what binds them, and the recursive literal stays put (`consequent-pred`).  A
  KB-registered evaluatable is not in that static set, so it is pinned by cost instead —
  the `:est-override` below reports it maximally unselective until its inputs are bound.
  Antecedents are substituted with `b0` before planning so the trigger's bindings make
  the estimates exact, mirroring the backward path.

  The **post-join** literals are withheld entirely (`rules/post-join-literals`): an
  aggregate and everything reading its output are evaluated per placement context, so
  a join that ran them would either take the census in the wrong context or reach a
  comparison whose input nothing here can bind.

  `admit` is the arrival filter (`join-antecedent`), nil for a join that suppresses
  nothing.  It is per **handle** rather than per position, so the reordering above
  neither reads it nor disturbs it."
  [kb antecedents b0 consequent-pred seed admit]
  (let [subbed (mapv #(res/substitute % b0) antecedents)
        post   (set (rules/post-join-literals subbed))
        ;; A registered evaluatable is not in `plan/order`'s static deferred set, so it is
        ;; pinned after its binders by cost instead — computed, so maximally unselective
        ;; until its inputs are bound.  Nil (no override) for the common KB with none, and
        ;; it never disturbs the index model the other antecedents are ranked by.
        est    (provers/evaluatable-est-override (evaluatable-antecedent-preds kb))]
    (reduce (fn [states ante] (if (post ante) states (join-antecedent kb ante states admit)))
            seed
            (plan/order kb subbed '?ctx {:consequent-pred consequent-pred :est-override est}))))

(defn- arrival-admit
  "The filter `complete-antecedents` puts on the handles the join yields, or nil when
  there is nothing to suppress — no ledger bound (outside a chaining run), a trigger the
  run never enqueued, or a trigger that is **not believed**.

  That last one is the asymmetry between the two ways a rule reaches a fact, and it
  is not optional.  A datum triggers on `res/match1`, which is a plain unify; the join
  finds facts through `*matcher*`, which is belief-filtered.  So an OUT datum — a
  spelling superseded by an equality merge, a defeated default — still fires its rules
  and still draws conclusions, while no *other* trigger's join can find it.  Its
  combinations are enumerable here and nowhere else, so here they are all made.

  **Admit a candidate whose arrival is at or before the trigger's**, which is semi-naive
  delta evaluation written for an agenda: every satisfying combination is enumerated by
  the trigger holding the *latest* arrival among its facts, and by no other, so a
  conclusion reached k ways costs k firings rather than k times the number of positions
  that could have started them.  A handle with no arrival is admitted — see
  `*agenda-arrivals*` for why that is the safe answer and not a gap.

  `<=` rather than `<` at every position, which admits one combination twice: the
  **self-join**, where one fact satisfies two positions of the same rule and so ties
  with itself.  Both of its triggers enumerate it, they build the identical
  justification, and the dedup rejects the second — a duplicate attempt for a shape a
  rule rarely has, against carrying each antecedent's original position through the
  cost planner's reordering to break the tie."
  [kb trigger-handle]
  (when-let [^java.util.Map arrivals *agenda-arrivals*]
    (when-let [at (.get arrivals trigger-handle)]
      (when (jtms/in? (:tms kb) trigger-handle)
        (let [at (long at)]
          (fn [h] (let [a (.get arrivals h)] (or (nil? a) (<= (long a) at)))))))))

(defn- complete-antecedents
  "Enumerate {:bindings :handles} completions of a rule fired at position
  `trigger-idx` by `trigger-handle`, joining the other antecedents from facts in
  any context, in cost order (`planned-join`).

  The other antecedents are joined only over facts that reached this run's agenda no
  later than the trigger did (`arrival-admit`), so a combination both sides could
  enumerate is enumerated by one of them.  The filter goes here, on the handles the
  join yields, rather than in the matcher: `*matcher*` is `rete`'s seam and has to keep
  returning the identical set.

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
        handle-only? (not (deferred-antecedent? kb trigger-ante))
        to-join      (if handle-only?
                       (vec (keep-indexed (fn [j a] (when (not= j trigger-idx) a)) antecedents))
                       (vec antecedents))
        seed         [{:bindings b0
                       :handles  (if handle-only? [trigger-handle] [])
                       ;; the trigger is a match like any other, and it is the one most
                       ;; likely to have subsumed: `fire-rules-for` reaches a rule
                       ;; through the arriving fact's *supertypes*
                       :matched  (if handle-only? [[(nm/functor trigger-ante) trigger-handle]] [])}]]
    ;; a *deferred* trigger draws no handle at all, so there is no arrival to order the
    ;; rest of the join against and nothing is suppressed
    (planned-join kb to-join b0 consequent-pred seed
                  (when handle-only? (arrival-admit kb trigger-handle)))))

(defn solve-rule
  "Full join of a rule's antecedents against current facts (used when a rule is
  added), in cost order.  The seeded arity starts from `b0` instead of the empty
  binding map, which is how `why-not` reconstructs a firing backwards from its
  conclusion; `consequent-pred` (the rule's consequent functor, nil if unknown) lets
  the planner keep the recursive literal in place."
  ([kb antecedents] (solve-rule kb antecedents {} nil))
  ([kb antecedents b0] (solve-rule kb antecedents b0 nil))
  ([kb antecedents b0 consequent-pred]
   ;; no trigger, so no arrival to order against: a full join suppresses nothing
   (planned-join kb (vec antecedents) b0 consequent-pred
                 [{:bindings b0 :handles [] :matched []}] nil)))

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

(defn- mint-rule
  "Store the rule a **generator** firing stamped out (docs/generators.md), justified by
  the firing, and return its handle in the newly-created vector `place-conclusion`
  returns.

  One thing separates this from a rule somebody asserted, and it is the whole point of
  minting rather than macro-expanding: the mint is **derived**, so it is justified
  rather than marked a premise, and the ordinary relabel un-believes it the moment what
  licensed it goes.  Both chainers ask belief of a rule before using it
  (`res/rule-believed?`), so an un-believed mint stops firing without anything having to
  hunt it down and delete it.

  Everything else is what the assert door does, because a rule is a rule whichever door
  it came through: the same check list (`checks/rule-violation`, read through
  `checks/check-rule!` so the two cannot drift), the same rule postings
  (`special/index-rule-sentex`), and the direction the *stamped* rule's own
  `set/*Rule` wrapper set — which rides in the sentence and so survives substitution
  untouched.

  Returned as a new handle so the agenda takes it: a minted rule is a datum, and
  `process-datum` joins a forward-capable one over the facts already stored, exactly as
  it does for a rule somebody typed.  That is what makes a generator's two arrival
  orders agree — facts first or generator first, the same rules exist and have seen the
  same facts — without a retroactive sweep of its own.

  A refused mint is **dropped and recorded**, never thrown, for the reason every check
  on this path is a value: an exception escaping a firing would leave the fixpoint half
  computed, and which rule fired first would decide what the KB believes."
  [kb rule sentence pctx all-antes depth bindings strength]
  ;; A stamped rule concluding a conjunction is polycanonicalized exactly as an asserted
  ;; one is (`rules/expand-consequent`) — one rule per conjunct, each keyed by its own
  ;; consequent predicate.  Checked before any of them is stored, for the reason
  ;; `core/assert` checks its conjuncts first: a mapv is not a transaction, and a mint
  ;; that half-landed would leave the KB holding part of a rule nobody wrote.
  (let [minted (rules/expand-consequent sentence)]
    (if-let [v (some #(checks/rule-violation kb % pctx) minted)]
      (do (violations/report kb [(assoc v :sentence sentence :context pctx
                                        :rule (:rule-handle rule))])
          [])
      (into []
            (mapcat
             (fn [one]
               (let [[h s new?] (kb/find-or-create-sentex kb one pctx)]
                 (when new? (special/index-rule-sentex kb h s))
                 (jtms/ensure-node (:tms kb) h depth)
                 (when-not (jtms/has-justification? (:tms kb) (:name rule) all-antes h)
                   (let [jid  (p/next-id (:records kb))
                         ;; content order is bought here, inside the dedup guard, for
                         ;; `place-fact-conclusion`'s reason: the question above is
                         ;; set-keyed and only the record being written needs an order
                         just (jtms/->just jid (:name rule) (kb/antecedent-order kb all-antes)
                                           h bindings strength)]
                     (p/put-justification (:records kb) just)
                     (jtms/add-justification (:tms kb) just)))
                 (if new? [h] []))))
            minted))))

(defn- place-fact-conclusion
  "Persist/justify a rule conclusion `conseq` in context `pctx` at justification
  `strength` (:monotonic / :default); return the handles newly created (for
  enqueueing) — the conclusion itself, plus a copy in each context its predicate is
  declared to lift into.

  The definitional constraints — arg types, disjointness, functionality — hold of
  *derived* content as much as of asserted content; a rule that concludes
  `(cat Rex)` where `(dog Rex)` is believed and the two are declared disjoint has
  concluded something the KB says cannot be.  They are checked here, on the
  derivation path, exactly as `assert-one` checks them on the assert path.  So does
  stratification, for the one conclusion that can break it: a derived `genl` /
  `genlCx` edge that would close a cycle through negation.

  A failure is **dropped and recorded**, never thrown: chaining is a fixpoint and
  must not abort halfway through it, and an exception escaping a rule firing would
  make the resulting belief set depend on which rule happened to fire first.  The
  conclusion is skipped (no sentex, no justification) and the violation lands in the
  KB's `violations` atom, readable with `core/violations`.

  Dropping rather than arbitrating is deliberate, and docs/nmtms.md holds the reason:
  an argument constraint convicts by the **absence** of a path from the argument's types
  to the constraint type, so there is no second sentex to weigh the conclusion against
  and nothing for a defeat class to compare.  A nogood needs two sides; this has one."
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
                ;; **The content sort is paid here and nowhere earlier.**  `all-antes`
                ;; arrives in the order the join built it; the record about to be
                ;; written is the one thing that must not inherit it
                ;; (`kb/antecedent-order` says what reads it).  The dedup question just
                ;; above is keyed on the antecedents **as a set** (`jtms/just-key`), so
                ;; it answers the same either way — and ordering before the guard priced
                ;; a printed sentence per antecedent per *firing* where the record being
                ;; written is per *justification*.
                just (jtms/->just jid (:name rule) (kb/antecedent-order kb all-antes)
                                  h bindings strength)]
            (p/put-justification (:records kb) just)
            (jtms/add-justification (:tms kb) just)))
        ;; Everything a conclusion means beyond itself, in the order `core/assert-one`
        ;; runs the same list — the three ways it merges, the copy a decontextualized
        ;; predicate takes, and what the argument constraints entail — because each is a
        ;; claim about the predicate rather than about how the sentence arrived.
        (let [;; A rule concluding one of the three equality relations merges exactly as
              ;; an asserted one does: the closure learns the edge, migration restates
              ;; every sentex the edge displaces, and the twins are new content this run
              ;; has to see.  Without it the conclusion would be stored and believed while
              ;; the closure never learned it — and `recover`, which replays the store,
              ;; would then disagree with the running KB about what it entails.  Reached by
              ;; name rather than by the `:derived?` flag `genl` carries, because
              ;; `integrate-transitive` discards what an arm returns and here the return
              ;; value is the work: the twins and the violations.  **After the
              ;; justification above**, not beside `derived-sentex-added`: migration
              ;; justifies each twin by the equality edges it rests on and takes only the
              ;; ones it believes, so a line earlier the conclusion is a node nothing
              ;; supports and the merge writes nothing.
              eq   (when (and new? (kb/equality-sentence? conseq))
                     (special/integrate-equality-sentex kb s h))
              ;; A *derived* second value for a functional predicate merges exactly as an
              ;; asserted one does.  It has to be here as well as in `assert-one`, because
              ;; `functional-problem` does not refuse a symbol clash (it derives an
              ;; equality instead): without this a rule concluding `(motherOf Tom
              ;; MrsSmith)` alongside `(motherOf Tom Mary)` would leave two values of a
              ;; functional predicate believed and unreconciled.
              fnl  (when new? (special/derive-functional-equalities kb conseq pctx h))
              ;; ...and the declaration's own side of the same inference: a rule
              ;; concluding `(functional P)` reaches P's stored facts exactly as an
              ;; asserted one does, or which values a slot reconciles would depend on
              ;; whether the declaration was written or derived
              fex  (when new? (special/equate-existing kb conseq))
              ;; ...and the edge's side of it: a derived `genl` edge between predicates
              ;; brings stored sub-predicate facts under a `functional` mark above them,
              ;; as an asserted one does
              fed  (when new? (special/equate-under-edge kb conseq))
              ;; ...and the antisymmetric merge, in the same three arrival orders a rule
              ;; can reach it by — a derived converse, a derived declaration, a derived edge
              asym (when new? (special/derive-antisymmetric-equalities kb conseq pctx h))
              axe  (when new? (special/antisym-equate-existing kb conseq))
              axd  (when new? (special/antisym-equate-under-edge kb conseq))
              ;; nil when nothing merged, which is every conclusion on a KB that states
              ;; no equality and every re-derivation on one that does — and a fixpoint
              ;; re-derives the same conclusion on every round of every defaults pass, so
              ;; this is the arm that must cost nothing rather than a little
              mig  (when (or eq fnl fex fed asym axe axd)
                     (merge-with into {:new [] :superseded [] :violations []}
                                 eq fnl fex fed asym axe axd))
              ;; The spellings those merges retired, applied here rather than left to the
              ;; settle that follows.  A supersession *starts* when migration says so and
              ;; reaches the reconcile only as its `extra` (`special/supersession-map`),
              ;; so a merge whose entries nobody hands over displaces nothing at all and
              ;; the KB believes both spellings until something restarts it.  It is the
              ;; same call `assert` makes before it chains, and it is what makes the twins
              ;; below seeds rather than an optimization: the retired spelling stops
              ;; matching the moment this runs, so the restatement has to be on the agenda
              ;; or a rule that had not yet reached the original fires on neither.
              _    (when (seq (:superseded mig))
                     (special/refresh-supersessions kb (:superseded mig)))
              ;; A decontextualized predicate is a claim about the predicate, so the lift
              ;; runs on content a rule concluded exactly as it runs on content a caller
              ;; asserted (`assert-one`).  Unconditionally, not only for a new
              ;; conclusion: a re-derivation is how a conclusion that was already
              ;; stored — and so was skipped by the retroactive sweep, or arrived before
              ;; the declaration did — picks its copy up.  The copy is a new datum in a
              ;; context that did not have it, so it is enqueued like the conclusion
              ;; itself.
              lift (special/deduce-lifts kb conseq h pctx)
              ;; The argument constraints entail of a *derived* conclusion exactly what
              ;; they entail of an asserted one.  Drawn only for a new conclusion, like
              ;; the checks above: a re-derivation adds a justification, not content, and
              ;; whatever the sentence entailed was entailed when it was first placed.
              args (special/deduce-arg-types kb (:entailments adm) h pctx)
              ;; ...and a conclusion that *is* a declaration reaches back over the stored
              ;; facts, as an asserted one does.
              back (special/entail-existing kb conseq h)
              ;; ...and a derived `genl` edge between predicates brings stored
              ;; sub-predicate facts under the declarations above them, as an asserted
              ;; one does
              down (special/entail-under-edge kb conseq)]
          (violations/report kb (concat (:violations mig) (:violations lift)
                                        (:violations args) (:violations back)
                                        (:violations down)))
          (-> (if new? [h] [])
              (into (:new mig))
              (into (:new lift))
              (into (:new args))
              (into (:new back))
              (into (:new down))
              ;; a *derived* genl edge makes stored facts matchable at a supertype
              ;; they did not have, exactly as an asserted one does — same seeds, or
              ;; the fixpoint would depend on which rule fired first
              (into (special/subsumption-seeds kb conseq))
              ;; and a derived genlCx edge widens what a rule can see, for the
              ;; same reason and with the same remedy
              (into (special/visibility-seeds kb conseq))))))))

(defn- place-conclusion
  "Place one firing's conclusion, whatever kind of thing it is.

  A conclusion that **is a rule** is a generator's mint (`mint-rule`,
  docs/generators.md); everything else is a fact (`place-fact-conclusion`).  The split
  is here rather than at the call sites because both of them — a fresh firing and a
  released refusal — must make it the same way, and because every arm of the fact path
  is about a fact: argument types, the functional merge, the decontextualized lift,
  subsumption seeds.  None of them means anything said of a rule.

  `all-antes` is the firing's antecedent handles **in whatever order the caller holds
  them**; both arms sort it by content (`kb/antecedent-order`) at the point they write a
  justification, and neither reads a position before that.  A released refusal hands over
  a vector that is already sorted, which the sort returns unchanged — the key is a
  function of the handle, so re-sorting is idempotent."
  [kb rule conseq pctx all-antes depth bindings strength]
  (if (rules/rule-sentence? (peek (sx/peel-rule-wrapper conseq)))
    (mint-rule kb rule conseq pctx all-antes depth bindings strength)
    (place-fact-conclusion kb rule conseq pctx all-antes depth bindings strength)))

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
  otherwise a context believes `(ancestorOf Tom Bob)` on the strength of a
  `(genl fatherOf parentOf)` edge some sibling theory asserted and it cannot see.
  Feeding the supporters' contexts to `maximal-common-descendant-contexts` beside the
  rule's and the facts' makes that structural: every placement it returns sees every
  edge by construction, so there is nothing left to filter, and the firing's three
  ingredients — rule, facts, taxonomy — are treated alike.

  The join itself stays global (`complete-antecedents`, any context on purpose): which
  facts *exist* is not the placement's question, and narrowing the join would drop
  firings placement accepts."
  [kb links vantage]
  ;; the widest-bottleneck route (reasoning/26): a firing that climbed the genl closure
  ;; rests on the *strongest* path relating the two functors, not the shortest, so its
  ;; conclusion is capped at that path's floor.  `supporter-class` is the live JTMS
  ;; defeat-class of each edge supporter, read here where the tms is in hand.
  (let [supporter-class #(jtms/defeat-class (:tms kb) %)]
    (reduce (fn [acc [ff af]]
              (if-let [hs (tax/reach-support (:taxonomy kb) :genl ff af vantage supporter-class)]
                (into acc hs)
                (reduced nil)))
            []
            links)))

(defn- visibility-support
  "A witness for each context `pctx` had to see to hold the firing: the `genlCx` edge
  handles along one path per ingredient context (`tax/reach-support`), deduplicated
  where two ingredients share a stretch of the cone.

  The `genl` half above and this one are the same claim about two relations.  A
  placement is the maximal context that **sees** the rule, the facts and the edges the
  match climbed, and every one of those sightings is a `genlCx` reachability some
  ordinary sentex supports and somebody can take back.  Naming the sighted contexts and
  not the edges that reach them would leave the conclusion standing in a context that
  can no longer see its own reasons, and the same KB built without the edge derives
  nothing — belief as a function of arrival order, which is the invariant
  docs/nmtms.md opens with.

  **The ordinary firing pays one `=` per ingredient and reads no closure**: a rule and
  its facts in the placement's own context reach it reflexively, and a reflexive reach
  rests on nothing.  A supporter with no recorded context is seen from everywhere and
  is skipped for the same reason.

  One path, one supporter per edge, exactly as `subsumption-support` names one: a
  justification is a conjunction of supports rather than a proof that no other support
  exists, so a second route re-derives at a fresh handle when the named one goes
  (`special/resubsumption-seeds` does the same office for `genl`)."
  [tax pctx ctxs]
  (if (every? #(or (nil? %) (= pctx %)) ctxs)
    []
    (into []
          (comp (remove #(or (nil? %) (= pctx %)))
                (distinct)
                (mapcat #(tax/reach-support tax :genlCx pctx % nil))
                (map first)
                (distinct))
          ctxs)))

(defn- exception-aware-placements
  "Placement candidates for `handles` while one of them is hidden somewhere.

  Assertion contexts alone are no longer sufficient in that case: an exception can
  hide a supporter at its own context while a meta-exception restores it in only one
  descendant cone.  Enumerate the contexts that structurally see every assertion,
  retain the readers that see every exact supporter, then keep only their maximal
  elements.  `excepted-anywhere?` is the coarse gate, so the ordinary placement path
  still takes no cone walk when none of this firing's supporters is targeted."
  [kb handles contexts]
  (let [tax (:taxonomy kb)]
    (if (some #(res/excepted-anywhere? kb %) handles)
      (let [common  (tax/common-descendants tax contexts)
            visible (filter (fn [ctx]
                              (every? #(res/supporter-visible? kb % ctx) handles))
                            common)]
        (tax/maximal-contexts tax visible))
      (tax/maximal-common-descendant-contexts tax contexts))))

(defn- placement-ingredients
  "Where a firing's conclusion may live, and which taxonomy supporters it names getting
  there: `[placement-contexts {placement-context [edge-handle]}]`.  Both relations are
  in that handle list — the `genl` edges the match subsumed through, and the `genlCx`
  edges the placement sees its ingredients over.

  An **`(ist Ctx S)` consequent names its own context**, and that is an escape hatch
  rather than a computed placement, so there is nothing to derive — the target is fixed
  and the only question is whether it can reproduce the subsumption, asked from `Ctx`
  itself so the edges it names are the ones it can see.  No witness there, no placement.
  The rule and the facts are **not** ingredients of that placement, so the conclusion
  does not rest on `Ctx` seeing them; it rests on `Ctx` seeing the `genl` supporters it
  was held to, and those are the contexts witnessed.

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
  [kb rule raw-c ist? links fact-handles fact-ctxs]
  (let [tax (:taxonomy kb)]
    (if ist?
      (let [c  (when (nm/context? (second raw-c)) (second raw-c))
            hs (when c (subsumption-support kb links c))]
        (if (and c hs)
          [[c] {c (into (mapv first hs) (visibility-support tax c (keep second hs)))}]
          [nil nil]))
      (let [ingredients (cons (:context rule) fact-ctxs)
            supporters  (cons (:rule-handle rule) fact-handles)
            base        (exception-aware-placements kb supporters ingredients)]
        (if (empty? links)
          ;; no subsumption to witness, so the whole support map is the visibility one —
          ;; and it is empty for the firing whose rule and facts are where the conclusion
          ;; lands, which is nearly all of them
          [base (reduce (fn [m b]
                          (let [vs (visibility-support tax b ingredients)]
                            (if (seq vs) (assoc m b vs) m)))
                        {} base)]
          (let [seeing (reduce (fn [m b]
                                 (if-let [hs (subsumption-support kb links b)]
                                   (assoc m b (into (mapv first hs)
                                                    (visibility-support
                                                     tax b (concat ingredients (keep second hs)))))
                                   m))
                               {} base)]
            (if (seq seeing)
              ;; `seeing` is the placement filter as well as the support map, and a
              ;; subsumed firing always names at least one `genl` edge, so no entry of it
              ;; is empty and the two readings cannot disagree
              [(filterv seeing base) seeing]
              (when-let [hs (subsumption-support kb links nil)]
                (let [ectxs (concat ingredients (keep second hs))
                      ps    (tax/maximal-common-descendant-contexts tax ectxs)
                      ehs   (mapv first hs)]
                  [ps (reduce (fn [m p]
                                (assoc m p (into ehs (visibility-support tax p ectxs))))
                              {} ps)])))))))))

;; ---- a refused firing is remembered as bindings --------------------------
;;
;; `place-conseq` declines to place a firing whose block condition already holds.  That
;; is the right call for the placement — the conclusion would be swept on the same
;; settle pass — but such a firing leaves **no trace**: no justification, no node,
;; nothing in `jtms/blocked`.  `settle` decides a pass is productive by asking whether
;; the blocked set moved, and reads a release off the justifications that were blocked
;; and are not any more, so both are blind to a firing that was never allowed to become
;; one, and the conclusion stays suppressed after the exception releases.  Belief then
;; depends on whether the block arrived before or after the facts, which is the
;; invariant docs/nmtms.md opens with.
;;
;; So the refusal is recorded, one level earlier and in the same shape: where the
;; blocked set holds justification ids, this holds `[rule-handle, bindings]` — enough to
;; re-ask the same level-6 question, and enough to place the conclusion from if the
;; answer moved.  Re-evaluating k recorded refusals costs k queries, in place of a join
;; over the whole fact extent.
;;
;; **Two of the four refusal reasons are recorded**, and the two that are not are not
;; oversights:
;;
;;   held exception    recorded — re-askable from the bindings alone
;;   `naf-blocks?`     recorded — likewise, and the same evaluator
;;   post-join failure not recorded — an aggregate is a *value* that moved, which is
;;                     `settle/aggregate-recheck-rules`' business: a queued aggregate
;;                     rule is re-joined whatever the blocked set did, so its firings
;;                     are found without a record
;;   `except`-hidden   not recorded — a visibility `except` moves what a context can
;;                     see rather than what the rule concludes, and no trigger queues
;;                     the rule on one; recording under a trigger that never fires
;;                     would be a set that grows and is never read
;;
;; The record is a **work list, never an answer**: it says which firings to re-ask, and
;; every entry is re-decided from scratch when it is read (`refusal-state`), exactly as
;; `exception-blocked-set` re-decides a candidate justification.  It is keyed on
;; content, so two refusals of the same rule at the same bindings from different passes
;; are one entry and arrival order cannot be read back out of it.  Nothing in it is a
;; nogood and nothing in it reaches `contradictions`: nothing was believed and nothing
;; conflicts, the rule simply did not fire.

(def max-refusals-per-rule
  "How many refused firings one rule's record keeps before it stops keeping them
  individually.

  One entry per refused firing is bounded by what a rule did **not** derive, and a rule
  excepted on a common condition can refuse far more than it places — so unlike blocking
  it is not bounded by the store.  Past this many entries the rule's record collapses to
  `:overflow` and it takes the coarse fallback instead: a queued overflowed rule forces a
  productive settle pass and is re-joined over its extent, which finds the same
  releases at the cost the record exists to avoid.  Correct on both sides of the line,
  and the line is stated in docs/exceptions.md."
  4096)

(defn- record-refusal!
  "Remember that a firing of `rule` was refused: the conclusion it would have placed,
  where, what it rests on, and the bindings the block condition was asked under.

  `:handles` are the antecedent *facts* alone, so the re-derivation recomputes the
  conclusion's depth exactly as a fresh firing would; `:antes` is the full justification
  antecedent list, rule handle and taxonomy supporters — `genl` and `genlCx` — included.

  `:max-depth` is the depth bound the **run that refused it** was configured with, kept
  so a later `release-refusal!` honours that bound rather than the default — the release
  runs in a settle with no run config in scope, so the bound has to travel with the
  entry.  It joins the entry's identity, so a firing refused under two different bounds is
  two entries; both release idempotently, and in practice a KB's runs share one bound."
  [kb rule conseq pctx antes handles bindings max-depth]
  (let [rh    (:rule-handle rule)
        entry {:conseq conseq :pctx pctx :antes antes :handles handles :bindings bindings
               :max-depth max-depth}]
    (swap! (:refused kb)
           (fn [m]
             (let [cur (get m rh)]
               (cond
                 (= :overflow cur)                        m
                 (nil? cur)                               (assoc m rh #{entry})
                 (contains? cur entry)                    m
                 (>= (count cur) max-refusals-per-rule)   (assoc m rh :overflow)
                 :else                                    (assoc m rh (conj cur entry))))))))

(defn- refusal-reason
  "Why a completed firing may not be placed in `pctx`, or nil — `:post-join`,
  `:exception`, `:naf` or `:hidden`, in the order they are cheapest to decide.

  Reading the rule *view* rather than the record: `:excepts` and `:naf` are already in
  hand on the firing path, and fetching them again per firing is what the view exists to
  avoid.  `bindings` is nil when a post-join literal had no answer."
  [kb rule antes bindings pctx]
  (cond
    (nil? bindings)                                                 :post-join
    (some #(exception-holds? kb % bindings pctx) (:excepts rule))    :exception
    (naf-blocks? kb (:naf rule) bindings pctx)                       :naf
    (antecedent-hidden? kb antes pctx)                               :hidden))

(def ^:dynamic *report-no-placement?*
  "Whether a completed firing that finds no placement context files a `:no-placement`
  entry.  True wherever content arrives, which is every path a caller drives: a firing
  that did everything but conclude is silent otherwise, and it is the commonest
  first-session mistake.

  **False for the re-chain a teardown owes** (`core/settle-after-teardown!`).  That pass
  re-asks firings the removal already swept, to learn which of them a surviving route
  still licenses — so one it cannot place is a restatement of the retraction rather than a
  diagnosis of the KB, and the caller who took the wiring away is the last person who
  needs telling.  Filing one per killed firing would also cost the ledger its real
  entries, which cap at 1000, and a `:warn` line apiece."
  true)

(defn- place-conseq
  "Place one ground conclusion literal `raw-c` from a firing: resolve its placement
  contexts — an `(ist Ctx S)` names its own, else the maximal contexts that see the
  rule and all antecedent facts — and place it in each unless the rule's exception or a
  NAF antecedent blocks it there.  Returns the newly created handles.  A firing with no
  placement context is recorded like any other dropped conclusion, and one refused by a
  re-checkable block condition is recorded as a refusal (see above).

  `links` are the firing's subsumptions (`subsumption-links`); the `genl` supporters
  witnessing them are an **ingredient of the placement** (`placement-ingredients`), not
  a filter on it, and they join the antecedent list.  So do the `genlCx` supporters
  the placement sees its ingredients over: a placement is a claim about the cone, and
  the conclusion may not outlive the edges that claim rests on."
  [kb rule raw-c handles all-antes facts links depth max-depth bindings]
  (let [ist?        (and (sequential? raw-c) (= sx/ist-functor (first raw-c)))
        conseq      (if ist? (nth raw-c 2) raw-c)         ; (ist Ctx S) concludes S ...
        fact-ctxs   (map :context facts)
        [placements support] (placement-ingredients kb rule raw-c ist? links handles fact-ctxs)]
    (if (empty? placements)
      ;; The join completed — every antecedent matched — and then the conclusion
      ;; evaporated: no context sees everything the firing rests on (sibling
      ;; contexts with no common descendant, the taxonomy it climbed included), or
      ;; an ist consequent named something that is not a context or an edge it cannot
      ;; see.  "Possibly none" is a legitimate outcome of
      ;; maximal-common-descendant-contexts, but a silent one reads as "the rule fired",
      ;; so it is recorded like any other dropped conclusion — naming the subsumption
      ;; when there was one, since "your context cannot see that genl edge" is a
      ;; different thing to go and fix from "your facts are in sibling contexts".  The
      ;; contexts that *would* have taken it but for the edges are recomputed here, on
      ;; the drop path only, because that difference is the whole diagnosis.
      ;; ...unless the pass is a teardown's re-chain, which is asking rather than being
      ;; told: `*report-no-placement?*` says why.
      (do (when *report-no-placement?*
            (violations/report kb
                               [{:violation :no-placement :sentence conseq :rule (:rule-handle rule)
                                 :detail (cond-> {:rule-context  (:context rule)
                                                  :fact-contexts (vec (distinct fact-ctxs))
                                                  :message
                                                  ;; the remedy, not only the diagnosis: this
                                                  ;; fires on the commonest first-session
                                                  ;; mistake — facts asserted into a context
                                                  ;; with no edge to the one holding the rule
                                                  ;; — where the reader has a rule that did
                                                  ;; everything but conclude, and a message
                                                  ;; that named the shortfall without naming
                                                  ;; the relation that closes it
                                                  (if (seq links)
                                                    (str "completed firing has no placement context — "
                                                         "no context sees the rule, all antecedent facts, "
                                                         "and the genl edges the match subsumed through.  "
                                                         "Add the genlCx edges that put one context "
                                                         "above all of them (:rule-context and "
                                                         ":fact-contexts below name what has to be seen, "
                                                         ":subsumed the edges)")
                                                    (str "completed firing has no placement context — "
                                                         "no context sees the rule and all antecedent facts.  "
                                                         "Add the genlCx edges that put one context "
                                                         "above both (:rule-context and :fact-contexts "
                                                         "below name what has to be seen)"))}
                                           (seq links)
                                           (assoc :subsumed (mapv first links)
                                                  :would-place
                                                  (vec (when-not ist?
                                                         (tax/maximal-common-descendant-contexts
                                                          (:taxonomy kb)
                                                          (cons (:context rule) fact-ctxs))))))}]))
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
                      ;; the taxonomy supporters — `genl` and `genlCx` alike — are per
                      ;; placement, so the antecedent list
                      ;; is too — and it is this list, not `all-antes`, that the `except`
                      ;; check reads, since `justification-excepted?` re-runs that check
                      ;; over the *stored* justification's antecedents and the two must
                      ;; not disagree about what the firing rests on.
                      ;;
                      ;; **Arrival order here, content order at the point of storing.**
                      ;; The stored vector must be `kb/antecedent-order`'s — the join
                      ;; yields its handles in trigger order, which is the agenda's, so
                      ;; every report that reads a stored justification would otherwise
                      ;; say which side arrived first.  But that order is bought with a
                      ;; printed sentence per antecedent, and nothing between here and
                      ;; the store reads a position: `refusal-reason` reaches the list
                      ;; only through `antecedent-hidden?`, which is a `some` over it,
                      ;; and the dedup below it is set-keyed (`jtms/has-justification?`).
                      ;; So the sort moves to the two places that keep something — the
                      ;; refusal record here, the justification in `place-conclusion` —
                      ;; and a firing that is refused outright or that re-derives a
                      ;; conclusion over support already justifying it stops paying for a
                      ;; vector it throws away.  How many firings that is depends on the
                      ;; rule set and can be none: a self-joining transitive closure
                      ;; reaches each pair by a different intermediate, so every one of
                      ;; its firings is a distinct justification and stores.
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
                                       bindings)
                            ;; the post-join literals may have bound a consequent
                            ;; variable the join left open
                            c (when bindings
                                (cond-> conseq (seq post) (res/substitute bindings)))]
                        (if-let [why (refusal-reason kb rule antes bindings pctx)]
                          (when (or (= :exception why) (= :naf why))
                            ;; a refusal entry is content the ledger keeps and
                            ;; deduplicates by value, and `release-refusal!` hands its
                            ;; `:antes` straight to `place-conclusion` — so it is
                            ;; ordered here, exactly as a stored justification is
                            (record-refusal! kb rule c pctx (kb/antecedent-order kb antes)
                                             handles bindings max-depth)
                            nil)
                          (place-conclusion kb rule c pctx antes depth bindings
                                            (:strength rule))))))
            placements))))

(defn- derive-conclusion
  "Record one rule firing at the rule's own justification strength (`:strength` on the
  rule view — a bare rule confers :monotonic and so caps the conclusion at its
  weakest antecedent, a `set/defaultRule` confers :default).  The justification is placed
  in the *maximal* contexts that see the rule and all antecedent facts (via
  genlCx); returns {:new [handles]} for any newly created sentexes.  The rule
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
            ;; ...and **not** a generator's head.  The rule it stamps out keeps its own
            ;; free variables by construction — they are the stamped rule's, which is
            ;; the whole scoping rule (docs/generators.md) — so skolemizing here would
            ;; freeze a pattern into constants and store a rule that matches one tuple.
            ;; A head existential *inside* the stamped rule skolemizes when that rule
            ;; fires, against its own handle, which is the only witness that means
            ;; anything.
            free      (when-not (rules/rule-sentence? (peek (sx/peel-rule-wrapper raw0)))
                        (let [f (free-consequent-vars raw0)]
                          (if-let [post (seq (:post-join rule))]
                            (seq (remove (into #{} (mapcat sx/deferred-output-vars) post) f))
                            f)))
            raw       (if free (skolem/skolemize-conclusion kb rule raw0 bindings free) raw0)
            ;; a ground `(Quasiquote T)` in the fired head constructs and reifies its
            ;; mention here (docs plan) — a no-op unless quasiquotation is declared
            raw       (quasiquote/reduce-in-conclusion kb raw)
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
            new       (vec (mapcat #(place-conseq kb rule % handles all-antes facts links
                                                  depth max-depth bindings)
                                   conjuncts))]
        ;; a firing is the finest unit of work the fixpoint has, so it is where a long
        ;; datum reports from — including a firing that placed nothing, since a join
        ;; grinding through matches that all turn out blocked is exactly the stretch that
        ;; otherwise looks hung
        (when *tick* (*tick* (count new)))
        ;; a placed preservation declaration changes what every later join may inherit
        (note-placed-declaration! conjuncts)
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

;; ---- reading the refusal record back ------------------------------------

(defn refusals
  "What is recorded against rule `rh`: a set of refusal entries, `:overflow`, or nil.
  `settle` reads this to decide which firings a queued rule owes a re-ask."
  [kb rh]
  (get @(:refused kb) rh))

(defn drop-refusal!
  "Retire one entry.  A refusal is dead when it fires, when its rule goes, or when the
  antecedents behind its bindings are no longer believed — the bindings are a snapshot,
  and a refusal must not resurrect a firing whose support left.  An `:overflow` record
  holds no entries to drop."
  [kb rh entry]
  (swap! (:refused kb)
         (fn [m]
           (let [cur (get m rh)]
             (if (set? cur)
               (let [cur' (disj cur entry)]
                 (if (empty? cur') (dissoc m rh) (assoc m rh cur')))
               m)))))

(defn refusal-state
  "Re-decide one recorded refusal of rule `rh`, from scratch: `:dead` when there is no
  longer a firing to make, `:blocked` when the condition that refused it still holds,
  `:free` when it does not and the conclusion is owed a placement.

  Nothing remembers the previous answer — the record says which firings to re-ask and
  never what the answer is, exactly as `exception-blocked-set` re-decides every
  candidate justification it looks at.  Blocking would otherwise drift from belief.

  The judgement is `rule-firing-blocked?`, the same one a placed firing's justification
  is re-decided by, plus the visibility `except` check the justification path also runs.
  Bindings are settled to the representatives `pctx` now elects first, for the reason
  `settled-bindings` records: a snapshot asks about a spelling a merge has retired, and
  the honest empty that comes back reads as *not excepted*."
  [kb rh entry]
  (let [rec (:records kb)
        tms (:tms kb)
        rsx (p/get-sentex rec rh)]
    (if-not (and rsx (rules/rule? rsx) (rules/forward-sentex? rsx)
                 (every? (fn [h] (and (p/get-sentex rec h) (jtms/in? tms h)))
                         (:antes entry)))
      :dead
      (let [pctx (:pctx entry)]
        (if (or (antecedent-hidden? kb (:antes entry) pctx)
                (rule-firing-blocked? kb rh rsx
                                      (delay (settled-bindings kb (:bindings entry) pctx))
                                      pctx))
          :blocked
          :free)))))

(defn rule-firing-report
  "Per forward rule in the KB, what it did with itself: how many firings it **placed**,
  how many it **refused** and why, or whether it did nothing at all.  The read behind the
  chaining funnel (docs/web.md) — the ontological engineer's *which of my rules actually
  do anything*.

  Rules are enumerated off the antecedent roster (`:rule-antecedents`) unioned through the
  rule index, so this costs `O(rules)`, never a scan of the fact extent.  Everything else
  is read from what a run already leaves standing — `jtms/dependents` on a rule handle is
  every firing it licensed, and the refusal ledger (`refusals` / `refusal-state`, each
  entry re-decided against *current* belief) is what it completed but did not place — so
  the funnel needs no per-run instrumentation: the stored ledger and the justification
  graph answer it, and a counter beside them would only restate what they already hold.

  Each row is `{:rule :sentence :believed? :placed :refused :refusals :status}`.
  `:placed` is the firing count. `:refused` is `:overflow` when the ledger capped the rule,
  else the entry count. `:refusals` is one map per recorded refusal — its live `:state`
  (`:blocked` / `:dead` / `:free`, re-decided now) and, for one that still blocks, the
  `:reason` (`:post-join` / `:exception` / `:naf` / `:hidden`), plus the `:conseq` it could
  not place and the `:context`. `:status` is `:fires` (placed at least one), `:blocked`
  (placed none, refused at least one), or `:silent` (no antecedent set ever completed —
  nothing placed and nothing refused)."
  [kb]
  (let [rec (:records kb)
        tms (:tms kb)
        idx (:index kb)
        rule-hs (into (sorted-set)
                      (mapcat #(p/rules-by-antecedent idx %))
                      (keys @(:rule-antecedents kb)))]
    (into []
          (keep (fn [rh]
                  (when-let [rsx (p/get-sentex rec rh)]
                    (when (rules/forward-sentex? rsx)
                      (let [placed  (count (jtms/dependents tms rh))
                            ref     (refusals kb rh)
                            over?   (= :overflow ref)
                            rview   (delay (rule-view-of kb rh rsx))
                            entries (when (set? ref)
                                      (mapv (fn [e]
                                              (let [st (refusal-state kb rh e)]
                                                {:state   st
                                                 :reason  (when (= :blocked st)
                                                            (refusal-reason
                                                             kb @rview (:antes e)
                                                             (when (:bindings e)
                                                               (settled-bindings kb (:bindings e) (:pctx e)))
                                                             (:pctx e)))
                                                 :conseq  (:conseq e)
                                                 :context (:pctx e)}))
                                            ref))
                            exc?    (some #(= :exception (:reason %)) entries)]
                        {:rule      rh
                         :sentence  (if-let [vm (:varmap rsx)]
                                      (sx/originalize (:sentence rsx) vm)
                                      (:sentence rsx))
                         :believed? (boolean (jtms/in? tms rh))
                         :placed    placed
                         :refused   (if over? :overflow (count entries))
                         :refusals  entries
                         ;; the exceptWhen queries that block it, so a blocked-by-exception
                         ;; row can name the exception rather than only its category — forced
                         ;; only when a refusal actually rested on one (`@rview` is already
                         ;; realized by then)
                         :excepts   (when exc? (vec (:excepts @rview)))
                         :status    (cond (pos? placed)              :fires
                                          (or over? (seq entries))   :blocked
                                          :else                      :silent)}))))
                rule-hs))))

(defn release-refusal!
  "Re-derive the refused firing `entry` of rule `rh` and retire the entry, or retire it
  without deriving anything when its support has left.  Returns the handles the
  re-derivation created, for the caller to put back on the agenda.

  **`place-conclusion` with the recorded bindings, never a fresh join** — that is the
  whole cost argument: re-deriving k recorded refusals is k placements, where seeding
  `chain` with the rule handle joins it over the whole fact extent.  The conclusion, its
  placement context and its antecedent list are the ones the refused firing computed, so
  the justification is the one that firing would have made; the depth is recomputed from
  the antecedent facts, as a fresh firing would compute it.

  Re-decided here rather than trusted from the caller's scan: the sweep runs in between,
  and a refusal whose support it collected must not be placed on the strength of an
  answer taken before it ran."
  [kb rh entry]
  (case (refusal-state kb rh entry)
    :blocked []
    :dead    (do (drop-refusal! kb rh entry) [])
    :free    (let [rule  (rule-view kb rh)
                   depth (inc (reduce max 0 (map #(jtms/depth (:tms kb) %) (:handles entry))))
                   ;; the bound the refusing run was configured with, kept on the entry;
                   ;; the default is the fallback for an entry a rebuild re-recorded
                   ;; before this field existed, never the silent ceiling it was
                   bound (:max-depth entry (:max-depth default-chain-opts))]
               (drop-refusal! kb rh entry)
               (if (> depth bound)
                 []
                 (vec (place-conclusion kb rule (:conseq entry) (:pctx entry) (:antes entry)
                                        depth (:bindings entry) (:strength rule)))))))

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
                           ;; forward-capable *and believed*: the antecedent index posts
                           ;; on storage, so a defeated or un-believed rule (a defeated
                           ;; mint, a rule concluded by a retracted rule) is still a
                           ;; candidate here, and firing it lands the firing's
                           ;; unconditional side effects — a `:no-placement`/`:disjoint`
                           ;; report against a rule the KB does not believe, `:monotonic`
                           ;; skolem bookkeeping — for a conclusion that only labels OUT.
                           ;; The trigger path refuses it on the record (`fire-rules-for`'s
                           ;; `forward?`); the qualitative re-join must too.
                           (if (and rsx (rules/forward-sentex? rsx) (res/rule-believed? kb rh))
                             (into nh (delta-fire-rule kb rh rsx moved max-depth truncated))
                             nh)))
                       []
                       rules)]
    (doseq [[c d] deltas] (qkb/note-joined kb calc c (:baseline d)))
    fired))

(defn- symmetric-rejoin-rules
  "The forward rules to re-join because `fact` is a `(symmetric P)` **declaration**.

  The matcher mirrors a literal only once its predicate is declared, so the pairs a
  `(sibOf ?a ?b)` antecedent reaches change the moment the declaration lands — and the
  facts that would have triggered those firings have already arrived, so nothing else
  will enumerate them.  Without this, the same four sentences derive a conclusion or not
  depending on whether the declaration came last: 6 of the 24 orderings, and the whole
  of the difference is that a stored fact means its mirror too.

  `genls(P)`, not `specs`: `mirrored-antecedent?` asks whether *any sub-predicate* of an
  antecedent's functor is symmetric, so declaring `sibOf` moves an antecedent on
  `relatedTo` above it as well as one on `sibOf` itself.  Answered by a symbol compare
  for every datum that is not one of these declarations."
  [kb fact]
  (when (and (sequential? fact) (= 2 (count fact)) (= 'symmetric (nm/functor fact)))
    (let [p (first (nm/args fact))]
      (when (and (symbol? p) (not (sx/variable? p)))
        (not-empty
         (into #{} (mapcat #(p/rules-by-antecedent (:index kb) %))
               (tax/genls (:taxonomy kb) p)))))))

(defn- rejoin-in-full
  "Re-join in full every forward rule the arriving datum moved a preserved predicate
  for, or newly declared symmetric.

  In full rather than at a trigger position, and the reason is the qualitative one: the
  arriving sentence need not unify with the antecedent it enabled.  `(genl chihuahua
  dog)` licenses a `largerThan` antecedent, and no walk from `genl` reaches
  `largerThan` — the predicate-keyed trigger index cannot connect the two.  Nor is a
  claim on the predicate itself enough on its own: `(largerThan dog cat)` unifies with
  the antecedent at the one tuple it is *stated* at, and the tuples it licenses are
  reached by joining rather than by matching.

  Bounded by the rules carrying an antecedent on a declared predicate, which is none
  for every KB that declares no preservation and none for nearly every KB that does.
  The symmetric caller is bounded the same way — by the rules with an antecedent over
  the predicate just declared — and is reached only by a declaration datum."
  [kb rules max-depth truncated]
  (reduce (fn [nh rh]
            (let [rsx (p/get-sentex (:records kb) rh)]
              ;; forward-capable *and believed*, for the reason `rejoin-qualitative` and
              ;; `fire-rules-for`'s `forward?` state: the index posts on storage, so an
              ;; un-believed rule reaches here and its firing's side effects land though
              ;; the conclusion only labels OUT.
              (if (and rsx (rules/forward-sentex? rsx) (res/rule-believed? kb rh))
                (into nh (fire-rule kb rh max-depth truncated))
                nh)))
          []
          rules))

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
        ;; read once per datum, not per candidate position: what makes the mirror true is
        ;; the fact's own `symmetric` declaration, and every position asks the same fact
        mirror   (symmetric-mirror kb fact)
        ;; a positive fact's predicate and its supertypes; a negative fact's one
        ;; `[:not pred]` key (`rules/antecedent-key`), negation taking no subsumption fan
        preds    (rules/trigger-keys (:taxonomy kb) fact)
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
        ;; The same shape one layer over, and the same reason: a sentence can move what
        ;; a preserved predicate licenses without being on that predicate — a `genl`
        ;; edge, a fact on the relation, the declaration, `(transitive R)` — and a
        ;; claim that *is* on it reaches the antecedent only at the tuple it is stated
        ;; at.  `inherit/rejoin-rules` reads the declarations to say which rules those
        ;; are, and answers nil after two cardinality reads for a KB that declares
        ;; none.
        prhs     (inherit/rejoin-rules kb fact)
        ;; And one layer over again, for the matcher rather than for a prover: a
        ;; `(symmetric P)` datum changes which pairs a P antecedent reaches, and the facts
        ;; it reaches them over have already arrived.  A symbol compare for every datum
        ;; that is not such a declaration.
        srhs     (symmetric-rejoin-rules kb fact)
        trigger  (cond->> rhs
                   qrhs (remove qrhs)
                   prhs (remove prhs)
                   srhs (remove srhs))
        ;; forward-capable *and believed*: the antecedent index posts on storage, so a
        ;; rule whose support has gone is still a candidate here and is refused on its
        ;; record rather than by the lookup (`res/rule-believed?`)
        forward? (fn [rh rsx] (and rsx (rules/forward-sentex? rsx)
                                   (res/rule-believed? kb rh)))]
    (into
     (reduce
      (fn [nh rh]
        (let [rsx (p/get-sentex (:records kb) rh)]
          (if-not (forward? rh rsx)
            nh
            ;; The trigger match runs over the record's own antecedents, and the
            ;; chainer's view — which re-derives them beside the NAF and post-join
            ;; literals and probes the exception roster — is built only once a
            ;; position unifies.  A candidate is any rule with an antecedent on the
            ;; datum's predicate or a supertype of it, and for a broad type most of
            ;; them unify at none of their positions; the view is a per-firing cost,
            ;; not a per-candidate one.
            (let [antecedents (:antecedent rsx)
                  cpred       (nm/functor (:consequent rsx))
                  rule        (delay (rule-view-of kb rh rsx))]
              (reduce (fn [nh2 i]
                        (reduce
                         (fn [nh3 b0]
                           (reduce (fn [nh4 state]
                                     (into nh4 (:new (derive-conclusion kb @rule state max-depth truncated))))
                                   nh3
                                   (complete-antecedents kb antecedents i datum b0 cpred)))
                         nh2
                         (trigger-bindings kb (nth antecedents i) fact mirror)))
                      nh
                      (range (count antecedents)))))))
      []
      trigger)
     (concat
      (when (seq qrhs) (rejoin-qualitative kb qcal qrhs max-depth truncated))
      (when (seq prhs) (rejoin-in-full kb prhs max-depth truncated))
      (when (seq srhs) (rejoin-in-full kb srhs max-depth truncated))))))

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
          ;; rule fires here too, at :default (see fire-rules-for).  Belief is asked
          ;; here as well as there: a rule reaches the agenda as a *datum* when it is
          ;; asserted or derived, and a derived one can arrive already defeated.
          (if (and (rules/forward-sentex? sx) (res/rule-believed? kb datum))
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
        due?      (fn [] (>= (- (System/nanoTime) @reported) interval))
        ;; the agenda's own order, recorded so a firing both sides could make is made
        ;; once (`*agenda-arrivals*`).  A fresh map per run rather than an outer one
        ;; reused, unlike the two caches beside it: these are positions in *this*
        ;; agenda, and a nested run (an `:on-progress` callback may start one) has
        ;; its own.
        arrivals  (when *suppress-duplicate-firings* (java.util.HashMap.))
        arrived   (volatile! 0)
        arrive!   (fn [hs]
                    (when arrivals
                      (doseq [h hs] (.put ^java.util.Map arrivals h (vswap! arrived inc)))))]
    ;; the tick is bound whether or not anybody is listening: it is also how the run
    ;; counts what it derived, and the loop no longer sees that between datums.
    ;; The handle cache is engaged for the same scope, and for the reason that scope
    ;; exists: a fixpoint asks "is this conclusion already stored?" once per witness, so
    ;; a conclusion reached k ways is k walks of the trie to a handle this run minted
    ;; itself.  Nothing is removed from the store inside a run — `settle` runs after it —
    ;; so every entry stays true for as long as the cache is bound.
    ;; The justification dedup index rides the same scope for the sibling question —
    ;; "does this conclusion already hold this justification?", also asked once per
    ;; witness — and the same argument covers it: nothing removes a justification
    ;; inside a run, and the two paths that do (`jtms/retract!`, `jtms/sweep!`) clear
    ;; it themselves.  It is scoped to this KB's TMS, so a nested run over another KB
    ;; (an `:on-progress` callback may start one) gets its own index, not this one.
    ;; The arrival ledger is the third thing on that scope, and it is the agenda's own
    ;; order rather than a cache of anything — a datum is stamped as it is enqueued,
    ;; before any datum behind it is processed, so the trigger of a pair is always the
    ;; one the ledger sorts later.
    (observe/with-handle-cache
      (jtms/with-dedup-cache (:tms kb)
        (binding [*tick* (fn [n]
                           (vswap! placed + n)
                           (when (and on-progress (due?)) (report!)))
                  ;; the fourth thing on this scope, and the sibling of the handle cache
                  ;; above it: a per-functor verdict on whether that cache is authoritative
                  ;; (the store held nothing under the functor when the run began), so a
                  ;; novel conclusion of a chain-only predicate skips the trie walk that
                  ;; would only reconfirm the cache's own miss (`kb/find-sentex-handle`).
                  ;; A fresh map per run, like `arrivals`: it is a claim about *this*
                  ;; run's store, and a nested run gets its own.  Armed only for a bulk
                  ;; frontier (`kb/chain-authority-min-frontier`) — an incremental assert's
                  ;; one-fact seed concludes too little to repay the probe, so it stays nil
                  ;; and `find-sentex-handle` walks the trie exactly as it did pre-optimization.
                  kb/*chain-authoritative-functors* (when (>= (count seed)
                                                              kb/chain-authority-min-frontier)
                                                      (java.util.HashMap.))
                  ;; The KB's registered evaluatables, read once: the registry is fixed
                  ;; for a run, and forward chaining reads this set on the hot join path to
                  ;; treat an `add-evaluatable` predicate as a computed antecedent
                  ;; (`deferred-antecedent?`).  A nested run over another KB rebinds it to
                  ;; that KB's set.  Empty for the common KB with none.
                  *evaluatable-preds* (provers/evaluatable-preds kb)
                  ;; Whether the KB declares any preservation, read on the first join
                  ;; that asks and forgotten when a firing places a declaration
                  ;; (`note-placed-declaration!`) — per run, and a fresh cell per run
                  ;; for the reason `arrivals` is.
                  *declarations-cell* (volatile! nil)
                  *agenda-arrivals* arrivals]
          (arrive! seed)
          (loop [agenda (into clojure.lang.PersistentQueue/EMPTY seed)]
            (if (or (empty? agenda) (>= @placed max-derivations))
              (do (vreset! pending (count agenda))
                  (when on-progress (report!))
                  {:derived @placed :truncated? (or @truncated (>= @placed max-derivations))})
              (let [d       (peek agenda)
                    new-hs  (process-datum kb d max-depth truncated)
                    _       (arrive! new-hs)
                    agenda' (into (pop agenda) new-hs)]
                (vreset! pending (count agenda'))
                (when (and on-progress (due?)) (report!))
                (recur agenda')))))))))

(defn rerecord-refusals!
  "Rebuild the refusal record by re-firing every rule that can refuse a firing.
  Returns the chain result, or nil for a KB where no rule carries a re-checkable block
  condition.

  `recover`'s half of the record.  A refused firing left no justification, so nothing in
  the store holds it and replaying the stored justifications cannot bring it back — the
  record is derived state and is rebuilt the way blocking is, by re-deciding rather than
  by reading.  Re-firing is what re-decides it: a firing that can be placed is placed and
  deduped by `has-justification?`, and one that is refused re-records.

  Run **after** the settle that establishes belief, since a refusal is a claim about what
  the KB believes, and `relabel` deliberately lands unblocked.  `!` because it discards
  the record it replaces.

  Re-fires at the **default** depth bound — `(chain kb live nil)` carries no run config —
  so the rebuilt entries record that default rather than whatever bound each original run
  set.  A run's `:max-depth` is transient live-session config no store holds, exactly as
  `recover` resets derivation depths to 0 (a bound only governs *future* chaining), so a
  KB chained under a non-default bound rebuilds its refusals, and releases them, at the
  default.  The recovered KB is internally consistent at that default; docs/exceptions.md
  states the one narrow case it can differ from the live session in."
  [kb]
  (when-let [roster (seq (p/exception-rules (:index kb)))]
    (reset! (:refused kb) {})
    (let [live (filterv (fn [rh]
                          (let [rsx (p/get-sentex (:records kb) rh)]
                            (and rsx (rules/rule? rsx) (rules/forward-sentex? rsx)
                                 (jtms/in? (:tms kb) rh))))
                        roster)]
      (when (seq live) (chain kb live nil)))))

(defn chain-all
  "One fixpoint from `seed`, strict and defeasible rules on the same agenda (there
  is no separate defaults phase — see `fire-rules-for`).

  Opens a new run in `chain-stats` — violations recorded during the run carry its
  id — and stashes the result there, warning when the run was truncated.  The ledger
  **accumulates** across runs rather than resetting per run, so a bulk load's drops
  stay observable one assert later; and because internal callers discard the
  `:truncated?` flag, the :warn log is how a depth-capped chain's lost conclusions
  surface.

  At `:debug` every run says what it did, truncated or not — the run is the boundary a
  log statement belongs at, and without one a chain that concluded nothing, a chain that
  concluded forty thousand things and a chain still joining are the same silence to
  somebody watching a load."
  [kb seed opts]
  (swap! (:chain-stats kb) update :runs inc)
  (let [started (System/nanoTime)
        result  (chain kb seed opts)]
    (swap! (:chain-stats kb) assoc :last result)
    ;; the counting is inside the payload, which Trove builds as a delay: a run that is
    ;; not being watched pays the `nanoTime` above and nothing else
    (trove/log! {:level :debug :id ::chain-run
                 :data (assoc result
                              :run  (:runs @(:chain-stats kb))
                              :seed (count seed)
                              :ms   (quot (- (System/nanoTime) started) 1000000))})
    (when (:truncated? result)
      (trove/log! {:level :warn :id ::chain-truncated
                   :msg "forward chaining was truncated (max-depth or max-derivations) — conclusions are missing"
                   :data result}))
    result))

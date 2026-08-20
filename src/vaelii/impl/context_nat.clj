;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.context-nat
  "The structural genlCx producer for reified-NAT contexts — docs/context-nat.md.

  A `(contextArgSubrelation F pos R)` declaration says two `F`-contexts identical except
  at argument `pos` are ordered by the sub-relation `R` on that argument.  This namespace
  reads the declarations and the context NATs of `F` from the store and **materializes**
  the `genlCx` edges they entail: for two siblings whose `pos` arguments stand in `R`, the
  more specific one (its argument `R`-below the other's) is deduced to `genlCx` the more
  general, as a **justified** sentex in CxUniverse.  So the edge belief-follows for free —
  retract a context (its `termOfUnit` map), the declaration, or the `R`-evidence, and the
  ordinary JTMS relabel withdraws it.  It is never a premise anyone asserted.

  `R` is resolved by a **bounded** oracle, because the producer runs on the assert
  maintenance path and a genlCx edge feeds the taxonomy closure a relabel loop reads — so
  a prover search is out (docs/naf.md): either a registered pure structural comparator
  (the datetime one, keyed on `subintervalOf` over `DatetimeFn` terms) answers it, or a
  believed stored `(R a b)` fact does.  A comparator answer is a pure function of the two
  expressions, already carried by the `termOfUnit` antecedents, so it needs no extra
  supporter; a stored fact contributes its own handle so defeating it withdraws the edge.

  Materialization reuses the derived-sentex pattern `special/deduce-lift` uses:
  `find-or-create-sentex`, then `special/derived-sentex-added` to reach the genlCx closure
  and post the re-check triggers, then a JTMS justification under the
  `contextArgSubrelation` informant."
  (:require [vaelii.impl.datetime :as datetime]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.nat :as nat]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.special :as special]))

(def ^:private universal-context 'CxUniverse)

;; ---- the bounded R oracle -------------------------------------------------

(def ^:private comparators
  "Registered pure structural comparators, `{sub-relation → (fn [a b] boolean)}`.  A
  comparator answers `R` between two structural argument terms by reading their shape — no
  store read, no proof — so the producer may call it inside the relabel loop.  Each is a
  total predicate that returns `false` for terms it does not apply to, so it composes with
  the stored-fact fallback: `datetime/subinterval?` answers a pair of `DatetimeFn` terms
  and declines anything else."
  {'subintervalOf datetime/subinterval?})

(defn- comparator-holds?
  "True iff a registered comparator for `r` answers that `a` is `R`-below `b`."
  [r a b]
  (boolean (when-let [f (get comparators r)] (f a b))))

(defn- r-evidence
  "The belief the relationship `a` `R`-below `b` rests on: `::pure` when a comparator
  answers it (a pure function of the two expressions, already carried by the `termOfUnit`
  antecedents), the handle of a believed `(R a b)` fact when one does, or `nil` when the
  relationship does not hold and no edge should be made.

  When several believed `(R a b)` facts stand — the same ground relation in different
  contexts — the supporter is chosen **content-keyed**, not by whichever the retrieval
  yielded first: sorting by context before taking one keeps the edge's justification off
  the insertion/index order of the facts (a handle tie-break would break order
  independence), the determinism `dedup-constant` uses.  The facts share the ground
  sentence `(R a b)`, so their context is what distinguishes them."
  [kb r a b]
  (cond
    (comparator-holds? r a b) ::pure
    :else (some->> (kb/sentexes-matching kb (list r a b) '?ctx)
                   (sort-by :context)
                   first
                   :id)))

;; ---- reading the declarations and the context NATs ------------------------

(defn any-context-subrelations?
  "Cheap gate: does the KB declare any `contextArgSubrelation`?  The producer is a no-op
  otherwise — one O(1) functor count per assert, the shape `nat/any-corresponding-predicates?`
  has."
  [kb]
  (pos? (p/count-with-functor (:index kb) 'contextArgSubrelation)))

(defn- subrelation-declarations
  "Believed `(contextArgSubrelation F pos R)` declarations as `[F pos R handle]`, kept
  where `(pred? F)` — all of them, or only those for one function."
  [kb pred?]
  (for [sx  (kb/sentexes-matching kb '(contextArgSubrelation ?f ?pos ?r) '?ctx)
        :let [[_ f pos r] (:sentence sx)]
        :when (pred? f)]
    [f pos r (:id sx)]))

(defn- context-nats-of
  "Every believed context NAT whose expression head is `f`, as `[k expr termOfUnit-handle]`."
  [kb f]
  (for [sx  (kb/sentexes-matching kb '(termOfUnit ?k ?e) universal-context)
        :let [[_ k e] (:sentence sx)]
        :when (and (nat/reified-context-symbol? k) (sequential? e) (= f (first e)))]
    [k e (:id sx)]))

(defn- sibling-key
  "The identity of a context NAT's sibling group under argument `pos`: its expression with
  the ordered argument masked, so two contexts share a key iff they agree on every *other*
  argument (the dimension) and differ only where `R` orders them.  `pos` is 1-based over
  the function's arguments, hence the expression index `pos` (index 0 is the functor)."
  [expr pos]
  (assoc (vec expr) pos '_))

;; ---- materialization ------------------------------------------------------

(defn- materialize-edge!
  "Deduce `(genlCx sub super)` in CxUniverse, justified by `antes`, unless a violation
  refuses it (a genlCx edge over two `cx/` contexts is admissible except a self-edge, which
  the caller already excludes).  Idempotent: a second call with the same antecedents adds
  no justification, and a different route adds another supporter of the one edge."
  [kb sub super antes]
  (let [edge (list 'genlCx sub super)]
    (when-not (special/inadmissible kb edge universal-context)
      (let [[h2 s2 new?] (kb/find-or-create-sentex kb edge universal-context)]
        (when new? (special/derived-sentex-added kb s2 h2))
        (let [depth (inc (reduce max 0 (map #(jtms/depth (:tms kb) %) antes)))
              antes (vec antes)]
          (jtms/ensure-node (:tms kb) h2 depth)
          (when-not (jtms/has-justification? (:tms kb) 'contextArgSubrelation antes h2)
            (let [jid  (p/next-id (:records kb))
                  just (jtms/->just jid 'contextArgSubrelation antes h2 {} :monotonic)]
              (p/put-justification (:records kb) just)
              (jtms/add-justification (:tms kb) just))))
        h2))))

(defn- order-group!
  "Materialize every genlCx edge within one sibling group under declaration `[pos R declH]`:
  for each ordered pair of siblings whose `pos` arguments stand in `R`, the sub `genlCx` the
  super.  `nats` is `[k expr termOfUnit-handle]` for the group's members."
  [kb pos r declH nats]
  (doseq [[ksub esub th-sub] nats
          [ksup esup th-sup] nats
          :when (not= ksub ksup)
          :let  [asub (nth esub pos nil)
                 asup (nth esup pos nil)
                 ev   (r-evidence kb r asub asup)]
          :when ev]
    (materialize-edge! kb ksub ksup
                       (cond-> [th-sub th-sup declH]
                         (not= ::pure ev) (conj ev)))))

(defn- reconcile-function
  "Materialize the structural genlCx edges for every declaration of function `f`, over all
  of `f`'s context NATs grouped into siblings."
  [kb f]
  (doseq [[_ pos r declH] (subrelation-declarations kb #(= f %))
          :let [groups (group-by #(sibling-key (second %) pos) (context-nats-of kb f))]
          [_ nats] groups]
    (order-group! kb pos r declH nats)))

(defn reconcile-genlCx!
  "The structural-genlCx maintenance a just-asserted `sentence` in `context` calls for,
  scoped to what could have changed:

  - a `(contextArgSubrelation F …)` declaration reconciles all of `F`'s contexts;
  - a fact stored into a `cx/` context reconciles that context's function — its arrival, or
    the mint of a new context beside it, is what creates a sibling pair to order.

  A no-op — one functor count — on a KB that declares no `contextArgSubrelation`.  Both
  arrival orders reach the same fixpoint: a declaration arriving after the contexts sweeps
  them (`reconcile-function`), and a context arriving after a declaration is swept when it
  is stored into.  Idempotent, so re-running orders the same edges without duplicating."
  [kb sentence context]
  (when (any-context-subrelations? kb)
    (cond
      (and (sequential? sentence) (seq sentence)
           (= 'contextArgSubrelation (first sentence)))
      (reconcile-function kb (second sentence))

      (nat/reified-context-symbol? context)
      (when-let [e (nat/nat-expression kb context)]
        (when (sequential? e) (reconcile-function kb (first e)))))))

(defn reconcile-revivals!
  "Rebuild the structural genlCx edges for **every** declared `contextArgSubrelation`
  function — the build direction a belief *revival* needs, which `reconcile-genlCx!` (only
  ever called from the assert choke-point) cannot serve.

  Belief of a `contextArgSubrelation` declaration — or of a stored `(R a b)` evidence fact
  — can flip OUT→IN with no assert: retracting a monotonic defeater above it revives it.
  The JTMS revives a *justification that already exists*, but an edge the producer never
  built (because the declaration was OUT when the contexts were stored) has no
  justification to revive, so the edge would stay absent.  A teardown therefore re-runs the
  producer once its belief has settled, and the withdraw direction the JTMS already handles
  meets a build direction here.

  Idempotent (`materialize-edge!` adds no duplicate justification) and **local**: scoped to
  the declared context functions, each reconciled only over its own contexts — bounded by
  the context-NAT population, never the whole graph.  Behind the **free** in-memory
  `contextDenotingFunction` gate first — a KB with no `cx/` context to order pays neither
  the `any-context-subrelations?` functor-count index read nor anything else, so the retract
  hot path is untouched on every KB that declares no context function
  (`assert_cost_test`)."
  [kb]
  (when (and (nat/any-context-denoting-functions? kb) (any-context-subrelations? kb))
    (doseq [f (distinct (map first (subrelation-declarations kb (constantly true))))]
      (reconcile-function kb f))))

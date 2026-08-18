;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.asp.label
  "Brave/cautious classification of a settled tie, and materializing one labeling as
  a specialization context.

  ## What this adds over `in?`

  The TMS answers *what do I believe*. After `settle` arbitrates a default/default
  tie, one side is IN and the other OUT — but that answer flattens two very different
  situations. A belief can be IN because every consistent way of resolving the
  contradictions keeps it, or because the solver had two equally good options and
  picked one. `in?` cannot tell them apart; both read as \"believed\".

  Brave/cautious classification separates them by asking the solver for *all* optimal
  answer sets rather than one:

  | class | in every optimum | in some optimum | meaning |
  |---|---|---|---|
  | `:true` | yes | yes | forced — no consistent labeling gives it up |
  | `:supportable` | no | yes | arbitrary — the current belief is one of several |
  | `:false` | no | no | excluded — no consistent labeling holds it |

  `:supportable` is the interesting one, and it is invisible from the TMS alone. In a
  Nixon diamond both sides are `:supportable`: whichever the TMS committed to, the
  other was equally available.

  ## Concert with the TMS

  Two rules keep these from drifting apart from belief.

  **Classification reads the recorded program, never a recomputed one.** Resolving a
  tie erases its own evidence — the defeated side stops matching, so the nogood is no
  longer derivable from the KB. `core/last-program` holds what the solver was
  actually asked (see the KB record).

  **Labeling reads the TMS, not a fresh solve.** `label-context` materializes the
  labeling the engine *committed to*, taken from `jtms/in?`, rather than re-solving
  and hoping for the same answer set back. A re-solve would usually agree, and
  \"usually\" is not a property worth building on.

  So the invariants hold by construction, and `asp_label_test` pins them:

      :true        ⊆ believed        (cautious holds in the committed model)
      :false       ∩ believed = ∅    (excluded holds in no model, including that one)
      :supportable — either way, by definition

  ## Requirements

  Classification needs a real ASP backend; `local-solver` produces one labeling and
  cannot enumerate optima. With no backend reachable, `classify` reports every
  contested assumption as `:supportable` — honest (each *is* one of several options)
  and never overclaims `:true`."
  (:require
   [vaelii.core :as v]
   [vaelii.impl.asp.edge :as edge]
   [vaelii.impl.asp.solver :as solver]
   [vaelii.impl.jtms :as jtms]
   [vaelii.impl.naming :as nm]
   [vaelii.impl.protocols :as p]
   [vaelii.impl.solve :as solve]))

;; `classify-program` lives in `asp.edge` (below core), so `settle` can stamp the
;; classification onto the TMS as belief settles.  Re-exported here for the KB-level
;; callers, which reach it at this layer.
(def classify-program edge/classify-program)

(defn classify
  "Classify the tie `kb` last settled — which of its beliefs were forced, which were
  an arbitrary pick, and which were excluded.

  Returns `{:true #{handle} :supportable #{handle} :false #{handle}}`, all empty when
  no tie has been arbitrated (nothing contested means nothing to be uncertain about)."
  [kb]
  (if-let [program (v/last-program kb)]
    (classify-program program)
    {:true #{} :supportable #{} :false #{}}))

;; ---- the dilemma bridge -------------------------------------------------
;;
;; Everything above classifies a tie the engine *arbitrated*.  The engine does not
;; arbitrate a plain rebuttal: a coexisting P/¬P pair at :default is a represented
;; dilemma, both sides stay IN, and `settle` builds no Program (docs/exceptions.md).
;; So `last-program` is nil in exactly the cases classification is interesting for.
;;
;; What `contradictions` reports is nevertheless the material a Program is made from —
;; that is the point of handing back both sides with their justifications rather than
;; picking one.  These turn it back into that shape, for a caller who asks.

(defn program-of-dilemma
  "The `Program` an application builds to rank one reported dilemma: the two contested
  handles, the nogood between them, and what each side asserts.

  `contradictions`' promise turned back into the shape the solver machinery takes.
  The engine declines to arbitrate; the machinery is still right here for a caller
  that wants to."
  [{:keys [nogood priority sentence sides]}]
  (solve/program nogood
                 [{:nogood nogood :priority priority :sentence sentence}]
                 (into {} (map (juxt :handle #(select-keys % [:sentence :context]))) sides)))

(defn- sides-content
  "What each side of each dilemma asserts, keyed by handle."
  [dilemmas]
  (into {} (mapcat (fn [d] (map (juxt :handle #(select-keys % [:sentence :context]))
                                (:sides d))))
        dilemmas))

(defn dilemma-program
  "One `Program` covering **every** dilemma `kb` currently reports, or nil if it
  reports none.

  All of them together rather than one at a time, because dilemmas can share a datum:
  a handle contested in two nogoods must be given up (or kept) once, consistently, and
  only a solver holding both constraints at once can do that.  Solving them
  separately would let the same datum be believed by one answer and not the other,
  which is not a labeling of anything."
  [kb]
  (when-let [ds (seq (v/contradictions kb))]
    (solve/program (into #{} (mapcat :nogood) ds)
                   (mapv #(select-keys % [:nogood :priority :sentence]) ds)
                   (sides-content ds))))

(defn- labeling-solver
  "The solver the labeling solve must use: the **ASP edge solver whenever a backend is
  reachable**, and only otherwise the one installed on the KB.

  This deliberately bypasses `(:solver kb)`, and the reason is that a labeling and its
  classification are two answers about one program that have to agree.  Classification
  needs to enumerate optimal answer sets, which only ASP does, so `classify-program`
  goes straight to the backend and ignores the installed solver.  If the labeling then
  came from `local-solver`, the two would be answering from different search
  procedures — and they diverge in practice, not just in principle.  Measured on two
  nogoods sharing a member, where greedy spends two defeats and the optimum spends
  one:

      stub  defeats {2,3} -> labels {1}      classification {:true {2,3} :false {1}}
      ASP   defeats {1}   -> labels {2,3}

  The stub's labeling keeps an assumption that holds in *no* optimum and drops two
  that hold in *every* one.  Committing to that would materialize an impossible world
  and globally defeat the atoms classification calls forced.

  With no backend the two degrade together and stay consistent for free:
  `classify-program` reports every contested assumption `:supportable` and claims
  nothing, so any labeling the stub produces satisfies a classification that asserts
  no `:true` and no `:false`."
  [kb]
  (if (solver/available?) edge/edge-solver @(:solver kb)))

(defn- check-agrees
  "Throw unless `labeled` is consistent with `classification` — the invariant that
  makes a labeling *of* a classification rather than merely alongside one:

      :true  ⊆ labeled          (holds in every optimum, so it must be kept)
      :false ∩ labeled = ∅      (holds in no optimum, so it must not be)

  Checked rather than assumed because the two come from separate solves, and a
  disagreement is exactly the failure this design is most exposed to.  `:fixed` is
  excluded from the first: it is known-true background that is assumed by every model
  and never an assumption the labeling chooses over."
  [program labeled classification]
  (let [forced   (remove (:fixed program) (:true classification))
        missing  (remove labeled forced)
        excluded (filter labeled (:false classification))]
    (when (or (seq missing) (seq excluded))
      (throw (ex-info "labeling disagrees with its own brave/cautious classification"
                      {:type :labeling-inconsistent
                       :missing-true (vec missing)
                       :kept-false   (vec excluded)
                       :labeled      (vec labeled)
                       :classification classification})))))

(defn- solved-labeling
  "The assumptions one optimal answer set keeps — `program`'s assumptions minus what
  the labeling solver gives up.

  **Sourced from the solve, not from the TMS**, which is the opposite of
  `label-context` below and for a reason that is the same principle either way:
  report what actually decided it.  A tie `settle` arbitrated was decided by the
  engine, so the TMS holds the answer and re-solving risks disagreeing with the
  engine's own belief.  A dilemma `settle` declined was decided by nobody — **both
  sides are IN** — so reading current belief would copy both halves of the
  contradiction into the labeling and recreate the dilemma one level down.  Here the
  solve is the only thing that decides."
  [kb program]
  (let [{:keys [defeat]} (solve/solve (labeling-solver kb) program)
        given-up (set defeat)]
    (into #{} (remove given-up) (:assumptions program))))

(defn label-dilemmas
  "Classify the dilemmas `kb` currently holds, then materialize one optimal labeling
  of them into `ctx`.  Returns
  `{:context ctx :handles [h ...] :classification {...} :program p}`; the handles are
  empty when the KB holds no dilemma.

  The four steps run in an order this fixes so a caller cannot get it wrong — in
  particular **classification is taken before materialization**, because materializing
  entrenches.  What it writes are ordinary assertions, and an assertion is evidence:
  the recorded side lands in a second nogood against its rival, so a tie that
  classifies `:supportable` on both sides classifies `:true`/`:false` once labeled.
  That is what recording a choice means, not a bug — but it means the classification
  has to be read first, and making one call do both is how that stops being something
  to remember.

  The Program is recorded in `kb`'s `:program` slot, so `last-program` and `classify`
  answer about this labeling afterwards.  `settle` never writes that slot for a
  dilemma (it builds no Program for one), so nothing is being overwritten.

  **`ctx` sees `base`, and the labeling is recorded by strengthening.**  Each kept
  assumption is re-asserted inside `ctx` at `:monotonic`, so `ctx` is a real world: the
  uncontested background is inherited through `genlCx` (reachable with `ask` /
  `lookup` at level 3 and above — note `query` is context-exact and will not show it),
  and the contested atoms are decided within it.  Nothing needs to be said about the
  side that lost: the strengthened copy out-ranks it, and `decide-nogood` defeats the
  strictly weaker member.

  **This commits, and the commitment is global.**  Belief in this TMS is a property of
  a datum, not of a datum-in-a-context, so strengthening inside `ctx` defeats the
  losing side *everywhere* — the base KB's dilemma stops being reported and the loser
  goes OUT for every context, not just under `ctx`.  Measured on the Nixon diamond:
  `contradictions` 1 → 0.  That is a deliberate choice of semantics (docs/labeling.md):
  a labeling you can query as a world is worth more than one you can only read, and
  the engine's refusal to arbitrate is preserved where it matters — it still refuses
  *on its own*, and only commits when a caller writes the imperative.

  So rival labelings are compared **sequentially**, not side by side: retract the
  returned handles, which revives the dilemma, then label again.  Holding two at once
  needs belief to be relative to a context, which is what an ATMS's per-datum
  assumption labels give you and what the TMS does not have today.

  Additive, so no `!`: this creates a context and asserts into it, and retracting the
  returned handles undoes it — including the commitment."
  [kb ctx base]
  (if-let [program (dilemma-program kb)]
    (let [classification (classify-program program)
          keep-set       (solved-labeling kb program)]
      ;; the two came from separate solves; refuse to commit if they disagree
      (check-agrees program keep-set classification)
      (reset! (:program kb) program)
      (v/assert kb (list 'genlCx ctx base) base {:strength :monotonic})
      {:context ctx
       :program program
       :classification classification
       :handles (into [] (keep (fn [h]
                                 (when-let [s (v/sentex kb h)]
                                   ;; :monotonic is the whole mechanism — a copy at
                                   ;; :default would merely tie with the side it is
                                   ;; supposed to beat, and report a second dilemma
                                   ;; instead of deciding the first
                                   (v/assert kb (:sentence s) ctx {:strength :monotonic})
                                   (v/handle-of kb (:sentence s) ctx))))
                      ;; sorted by content, never by handle: handles are allocated in
                      ;; assertion order, so iterating them would make *which* copy is
                      ;; created first depend on the order the knowledge arrived — the
                      ;; content-key built once per member, not per comparison
                      (nm/sort-by-content-key #(solve/content-key program %) compare keep-set))})
    ;; nothing contested: no program, no context, nothing to record.  Minting an empty
    ;; labeling context would assert that a choice was made where none was.
    {:context ctx :program nil :handles []
     :classification {:true #{} :supportable #{} :false #{}}}))

(defn label-context
  "Mint `ctx` as a specialization of `base` holding the labeling the engine committed
  to, and return `ctx`.

  The labeling is read from the TMS — the contested assumptions it currently believes
  — not from a fresh solve, so the context is guaranteed to say what the engine
  actually decided rather than what a second solve might have chosen.

  `ctx` sees `base` through `genlCx`, so it inherits the whole KB; what it adds
  is an explicit, queryable record of one arbitration. Two labelings of the same tie
  can therefore be built as sibling contexts and compared.

  **This entrenches the labeling, so classify before you label.** What it writes are
  ordinary assertions, and an assertion is evidence: the recorded side now sits in a
  second nogood against its rival, which makes defeating the rival strictly cheaper
  than defeating the record. A tie that classified as `:supportable` on both sides
  will classify as `:true`/`:false` afterwards. Belief does not move — the losing
  side was already OUT — but it stops *looking* arbitrary, because it no longer is:
  something now asserts the choice. Retracting the returned handles restores the
  open tie.

  Additive, so no `!`: this creates a context and asserts into it, and retracting the
  handles it returns undoes it."
  [kb ctx base]
  (let [tms (:tms kb)
        program (v/last-program kb)
        ;; content order, as `label-dilemmas` orders the same set: `:assumptions` is
        ;; a handle set, and hash iteration would mint the copies — and return the
        ;; `:handles` a caller retracts — in an order that tracks assertion order
        believed (nm/sort-by-content-key #(solve/content-key program %) compare
                                         (filter #(jtms/in? tms %) (:assumptions program)))]
    (v/assert kb (list 'genlCx ctx base) base {:strength :monotonic})
    {:context ctx
     :handles (into [] (keep (fn [h]
                               (when-let [s (p/get-sentex (:records kb) h)]
                                 (v/ist kb ctx (:sentence s)))))
                    believed)}))

;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.solve
  "The seam to an external solver (ultimately an ASP/clingo backend) for assigning
  truth at the *edges* — the defeasible nodes that a set of soft, prioritized
  contradictions leaves genuinely undecided.

  Design constraints (see docs/nmtms.md):

  * Most of the KB is monotonic / default-true with no conflict; only the edges are
    contested, so a Program covers just the contested defeasible nodes.
  * Known-true content (:monotonic) is never sent — it is the fixed
    background the solver assumes, not something it decides.
  * Contradictions are *soft and prioritized*: a solve never fails.  Instead the
    solver reports which contradictions it could not satisfy (their sentences are
    the result), highest priority first.

  * **A solve is order-independent.**  Which side of a tie loses may not depend on
    when anything was asserted — see `content-key`.  This is the engine-wide
    invariant (docs/nmtms.md): the same knowledge, given in any order, must yield
    the same beliefs.

  A `Program` is a self-contained description a real backend renders to ASP.  This
  namespace ships only a deterministic local *stub* solver; a real backend is a
  future plug-in registered with `core/set-solver`."
  (:require [clojure.set :as set]
            [vaelii.impl.naming :as nm]))

(defprotocol Solver
  (solve [solver program]
    "Assign truth to `program`'s contested assumptions.  Return
       {:defeat   #{handle ...}   ; assumptions to disbelieve
        :violated [nogood ...]}   ; contradictions left unsatisfiable (the result)"))

(defrecord Program
           [assumptions        ; #{handle} — contested defeasible nodes (never known-true)
            fixed              ; #{handle} — known-true background referenced by a contradiction
            contradictions     ; [{:nogood #{handle} :priority int :sentence any}]
            content])          ; {handle {:sentence s :context c}} — what each assumption SAYS

(defn nogood-members
  "Every handle a nogood involves — its positive members (`:nogood`, forbidden to hold
  together) and its negated members (`:neg`, forbidden to be *absent* together, e.g. an
  at-least-one requirement).  `:neg` is optional and usually absent."
  [ng]
  (into (set (:nogood ng)) (:neg ng)))

(defn program
  "Build a solver Program for a set of `contested` handles and the `nogoods` among
  them.  Contradiction members that are not contested are `fixed` — known-true
  background that is assumed, never decided.

  `content` maps each contested handle to what it asserts.  A solver needs it to
  break ties on *what a datum says* rather than on its handle; a real ASP backend
  needs it to name atoms stably across runs."
  [contested nogoods content]
  (let [contested (set contested)
        relevant  (filterv #(seq (set/intersection (nogood-members %) contested)) nogoods)
        fixed     (into #{} (comp (mapcat nogood-members) (remove contested)) relevant)]
    (->Program contested fixed relevant (select-keys content contested))))

(defn content-key
  "A stable total order on contested assumptions, derived from **what they assert**.

  Handles are allocated in assertion order, so ordering by handle makes the outcome
  of a tie depend on the order the knowledge arrived — the Nixon diamond would elect
  the pacifist or the non-pacifist purely according to which was typed first.  That
  is the order-dependence this exists to remove: the content of a sentex is the same
  whenever it is asserted, so a content-keyed choice is stable.

  The choice it produces is still *arbitrary* — two equally-specific defaults give
  no principled winner, and a real ASP backend would enumerate both answer sets.
  Arbitrary but stable is the contract; arbitrary and order-dependent is a bug."
  [program handle]
  ;; the print vars are bound off: an ambient *print-length* (a REPL's, typically)
  ;; would elide the very content — and the last-resort handle — that makes this key
  ;; total, and the arbitration would fall back to arrival order
  (binding [*print-length* nil *print-level* nil *print-meta* false]
    (pr-str [(get-in program [:content handle :sentence])
             (get-in program [:content handle :context])
             handle])))                              ; last resort: identical content

(def local-solver
  "A deterministic stub standing in for a real answer-set solver: satisfy
  contradictions highest-priority first by defeating the contested member with the
  greatest `content-key`; a contradiction none of whose live members is contested is
  unsatisfiable and is reported as violated.  A real ASP backend replaces this
  without touching callers.

  Greedy, one contradiction at a time — it does not optimize globally, so two
  overlapping *pairs* can cost two defeats where a real backend would spend one on
  the shared member (docs/nmtms.md).  What it must not do is spend a defeat on a
  nogood that is already satisfied; see the first `cond` branch."
  (reify Solver
    (solve [_ {:keys [assumptions contradictions] :as program}]
      (loop [defeated #{}
             violated []
             ;; sort by priority, then by content — a stable order over the whole
             ;; contradiction list, not just within one nogood, since an earlier
             ;; choice constrains later ones.  The content half is the members'
             ;; content-keys, sorted and then compared **structurally** rather than
             ;; re-`pr-str`ed: each key is already a `*print-length*`-guarded string,
             ;; but a `pr-str` of the *list* of them would elide under an ambient
             ;; `*print-length*` and drop the tie back onto arrival order.
             ;; keyed once per nogood, not once per comparison: the key maps
             ;; `content-key` over every member and sorts them, so a plain `sort-by`
             ;; would re-run that per comparison — `nm/sort-by-content-key` decorates it once.
             ngs (nm/sort-by-content-key
                  (fn [ng]
                    [(- (:priority ng))
                     (vec (sort (map #(content-key program %)
                                     (concat (:nogood ng) (:neg ng)))))])
                  nm/compare-form
                  contradictions)]
        (if (empty? ngs)
          {:defeat defeated :violated violated}
          (let [{:keys [nogood neg] :as ng} (first ngs)
                live      (remove defeated nogood)
                present   (remove defeated neg)      ; `:neg` members still believed
                choosable (filter assumptions live)]
            (cond
              ;; Satisfied as soon as ONE member is out — a nogood is a conjunction
              ;; that must not hold in full.  Testing `(<= (count live) 1)` instead is
              ;; the same test for a *pair* and wrong for anything wider: a
              ;; three-member nogood with one member already defeated still has two
              ;; live, so it would be decided a second time and a second datum
              ;; disbelieved to satisfy a constraint that already holds.  The engine
              ;; only builds pairs today, which is why this was invisible.
              (< (count live) (count nogood)) (recur defeated violated (rest ngs))
              ;; The `:neg` half is an at-least-one: any member still believed
              ;; satisfies it, a fixed member (outside `assumptions`) permanently so.
              ;; Only with every member defeated is it violated — and defeating more
              ;; cannot restore presence, so there is nothing to choose.
              (and (seq neg) (seq present)) (recur defeated violated (rest ngs))
              (empty? choosable)  (recur defeated (conj violated ng) (rest ngs)) ; cannot satisfy
              :else (recur (conj defeated (last (sort-by #(content-key program %) choosable)))
                           violated (rest ngs)))))))))

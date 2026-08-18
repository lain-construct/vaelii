;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.asp.edge
  "The real ASP backend behind `vaelii.impl.solve/Solver` — the edge solver.

  `solve.clj` describes *what* an edge solve is: most of the KB is monotonic or
  default-true with no conflict, so only the contested defeasible nodes are sent,
  known-true content is fixed background, and contradictions are soft and
  prioritized so a solve never fails.  This namespace renders that `Program` to
  ASPIF and reads an answer set back.

  ## The encoding

  Each contested assumption is a **choice atom**: true means believed, false means
  defeated.  Known-true (`:fixed`) members of a contradiction are *not* atoms —
  they hold by assumption, which is exactly what makes them background.

  A contradiction `#{h1 h2 ...}` becomes a violation atom derived from its
  contested members:

      v :- a_h1, a_h2, ...

  and a **weak** constraint minimizing `v`.  Weak rather than hard is the whole
  point: an unsatisfiable contradiction costs, it does not make the program UNSAT,
  so it comes back in `:violated` instead of throwing.

  A nogood carrying `:hard true` (a `set/hardConstraint` rule ground by
  `solve-context`) is instead a **hard integrity constraint**

      :- a_h1, a_h2, ...

  with no violation atom and no minimize term: a model satisfying its whole body is
  excluded outright.  That is what makes graph 3-coloring plain satisfaction rather
  than optimality-proving over soft violations — an adjacency clash is never
  tradeable.  Soft nogoods (the default) keep the minimize path above.

  In practice `:violated` comes back empty, and that is correct rather than a gap.
  An irreducible known-true clash never reaches a solver: `core/settle`'s
  `decide-nogood` classifies it as *hard* and reports it directly, and
  `solve/program` drops any nogood with no contested member.  What does arrive
  always has a contested member, and defeating that member always satisfies it.
  The `:doomed` path below is therefore defensive — it costs nothing and stays
  correct if nogoods ever grow beyond today's `S` vs `(not S)` pairs.

  ## The objective, most significant first

  Higher ASPIF minimize priorities dominate lower ones, so the levels are:

  | level | minimizes | why |
  |---|---|---|
  | `2 + rank(p)` | violation atoms | satisfy contradictions, caller priority first |
  | `1` | defeated assumptions | give up as little belief as possible |
  | `0` | a content-keyed weight | break remaining ties *stably* |

  Caller priorities are mapped through their ascending rank rather than used as
  levels directly, so any integers work and none can collide with the two levels
  below.

  ## Determinism

  A tie between equally-good answer sets has no principled winner, but it must not
  depend on assertion order — the engine-wide invariant in docs/nmtms.md.  Atom ids
  are allocated in `solve/content-key` order, and level 0 weights defeating the
  greatest content-key most cheaply, mirroring the stub's choice.  Same knowledge
  in any order, same answer set.

  ## Availability

  `edge-solver` degrades rather than fails: with no clingo and no clasp reachable
  it delegates to `solve/local-solver`, so installing it is always safe."
  (:require
   [vaelii.impl.asp.aspif :as aspif]
   [vaelii.impl.asp.atoms :as atoms]
   [vaelii.impl.asp.solver :as solver]
   [vaelii.impl.naming :as nm]
   [vaelii.impl.solve :as solve]))

;; Objective levels.  Violations sit above both, at 2 + the rank of the caller's
;; priority; these two are the fixed floor.
(def ^:private level-defeat-count 1)
(def ^:private level-tiebreak 0)

(defn- descriptor
  "The contradiction descriptor `atoms/intern-contradiction!` interns: a
  sentence-shaped value carrying the involved handles, so a witness atom can be
  read back without a secondary lookup."
  [{:keys [nogood sentence]}]
  (list 'contradiction sentence :involved (mapv (fn [h] [:sentex h]) (sort nogood))))

(defn translate
  "Render `program` to ASPIF.  Returns

      {:aspif      text or nil          ; nil when there is nothing to solve
       :table      the atom table
       :by-label   {label nogood}       ; violation atom -> the contradiction
       :assumptions [handle ...]        ; in content-key order
       :doomed     [nogood ...]}        ; all-fixed, unsatisfiable without solving

  `:tiebreak?` (default true) emits the level-0 content-keyed objective that makes
  the optimum unique.  Solving for *one* labeling wants it — an arbitrary choice
  still has to be a stable one.  Enumerating optima wants it **off**: it is an
  arbitrary preference, not a semantic constraint, and leaving it in collapses every
  tie to a single answer set, which would report a genuinely open choice as forced.
  `label/classify-program` is the caller that turns it off.

  `:keep-belief?` (default true) emits the level-1 objective that minimizes defeated
  assumptions — keep as much belief as possible.  Turning it **off** makes the solve
  plain *satisfaction* rather than optimization: with no minimize term clingo stops at
  the first model instead of proving cost-optimality over the choice atoms, which is
  the difference between finishing and not at scale (a 10k-node graph 3-coloring).  A
  caller turns it off only when the program's hard constraints already pin what must be
  chosen (e.g. a hard at-least-one), so \"keep as much as possible\" adds nothing."
  ([program] (translate program {}))
  ([{:keys [assumptions contradictions] :as program}
    {:keys [tiebreak? keep-belief?] :or {tiebreak? true keep-belief? true}}]
   (let [ordered   (nm/sort-by-content-key #(solve/content-key program %) compare assumptions)
         ;; the nogoods too: `settle` hands them in arrival order, and every emission
         ;; below — the violation-atom interning, the constraints, the minimize and
         ;; show statements — walks this seq, so an unsorted one renders two logically
         ;; identical programs as different ASPIF text and (without the tiebreak) two
         ;; different first-found optima for one KB.  The key is a COMPARABLE STRUCTURE
         ;; (a vector `compare` orders directly), not a printed string, and it is built
         ;; ONCE per nogood here — not by the sort's key fn, which `sort-by` re-invokes
         ;; on every comparison.  The old key `(pr-str [ … ])` did both: it re-rendered
         ;; the whole nogood, re-`content-key`'d every member, O(n log n) times over the
         ;; nogood set, grounding the w7 3-colouring ~12× slower than arrival order did.
         contradictions (let [ck #(solve/content-key program %)]
                          (->> contradictions
                               (map (fn [ng]
                                      [[(vec (sort (map ck (concat (:nogood ng) (:neg ng)))))
                                        (:priority ng)
                                        (boolean (:hard ng))]
                                       ng]))
                               (sort-by first)
                               (mapv second)))
         n         (count ordered)
         table     (atoms/new-table)
         ;; Allocate in content-key order so atom ids never depend on assertion order.
         atom-of   (into {} (map (fn [h] [h (atoms/intern-sentex! table h)])) ordered)
         ;; Sorted by atom id — and therefore by content, since that is how atoms were
         ;; allocated.  A nogood's members are sets, so an unsorted body would put
         ;; literals in hash order and render two logically identical programs as
         ;; different text.  `pos` are members forbidden to hold together (`:nogood`);
         ;; `neg` are members forbidden to be absent together (`:neg`, e.g. an
         ;; at-least-one), emitted as default-negated literals.
         pos       (fn [ng] (sort-by atom-of (filter assumptions (:nogood ng))))
         neg       (fn [ng] (sort-by atom-of (filter assumptions (:neg ng))))
         involved  (fn [ng] (concat (pos ng) (neg ng)))
         ;; A fixed `:neg` member is an assumed-true one: its default-negated literal
         ;; is false, so the body can never hold and the nogood constrains nothing.
         ;; Dropping only the member instead would *tighten* the constraint — models
         ;; nothing forbade would be excluded, or penalized.
         vacuous?  (fn [ng] (not-every? assumptions (:neg ng)))
         grounded  (remove vacuous? contradictions)
         doomed    (filterv (comp empty? involved) grounded)
         live      (remove (comp empty? involved) grounded)
         ;; A `:hard` nogood is an integrity constraint (no witness atom, no minimize);
         ;; the rest are soft, minimized violations.
         hard-live (filter :hard live)
         soft-live (remove :hard live)
         ;; Caller priorities become levels by ascending rank, clear of 0 and 1.
         levels    (into {} (map-indexed (fn [i p] [p (+ 2 i)]))
                         (sort (distinct (map :priority soft-live))))
         v-atoms   (mapv (fn [ng] [ng (atoms/intern-contradiction! table (descriptor ng))]) soft-live)
         stmts     (concat
                    ;; believed-or-defeated
                    (map (fn [h] (aspif/choice (atom-of h))) ordered)
                    ;; hard: forbid any model in which the whole (signed) body holds
                    (map (fn [ng] (aspif/constraint
                                   (concat (mapv atom-of (pos ng))
                                           (mapv #(- (atom-of %)) (neg ng)))))
                         hard-live)
                    ;; v :- the whole signed body holds — every `:nogood` member true
                    ;; and every `:neg` member absent, the same body the hard branch
                    ;; forbids.  Positive members alone would emit a `:neg`-only
                    ;; nogood's witness as an unconditional fact: always violated,
                    ;; never steering.
                    (mapcat (fn [[ng v]]
                              [(aspif/rule v (concat (mapv atom-of (pos ng))
                                                     (mapv #(- (atom-of %)) (neg ng))))
                               (aspif/minimize (levels (:priority ng)) [[v 1]])])
                            v-atoms)
                    ;; keep as much belief as possible: a defeated atom is a false one.
                    ;; Off ⇒ plain satisfaction (no optimization to prove) — see the docstring.
                    (when (and keep-belief? (seq ordered))
                      [(aspif/minimize level-defeat-count
                                       (mapv (fn [h] [(- (atom-of h)) 1]) ordered))])
                    ;; stable tiebreak: cheapest to defeat is the greatest content-key
                    (when (and tiebreak? (seq ordered))
                      [(aspif/minimize level-tiebreak
                                       (map-indexed (fn [i h] [(- (atom-of h)) (- n i)]) ordered))])
                    ;; labels are how the answer set comes back
                    (map (fn [h] (aspif/show (atom-of h) (atoms/label-of-atom table (atom-of h))))
                         ordered)
                    (map (fn [[_ v]] (aspif/show v (atoms/label-of-atom table v))) v-atoms))]
     {:aspif       (when (seq stmts) (aspif/render stmts))
      :table       table
      :by-label    (into {} (map (fn [[ng v]] [(atoms/label-of-atom table v) ng])) v-atoms)
      :assumptions ordered
      :doomed      doomed})))

(defn- interpret
  "Read `result`'s answer set back into the `Solver` contract."
  [{:keys [table by-label assumptions doomed]} result]
  (let [true-labels (set (:atoms result))
        defeated    (into #{} (remove #(true-labels (atoms/label-of-atom table (atoms/atom-of-sentex table %))))
                          assumptions)
        violated    (into (vec doomed)
                          (keep by-label)
                          (sort true-labels))]
    {:defeat defeated :violated violated}))

(defn kept-of
  "The chosen-true assumption handles of one `:label` answer set, read back through
  translation `t`'s atom table — the single-answer-set counterpart to `interpret`'s
  defeat set (kept = assumptions − defeated).  `solve-context`'s `:one` mode reads a
  labeling with it.  An `:unsat` result carries no true labels, so this returns `#{}`
  (nothing kept)."
  [{:keys [table assumptions]} result]
  (let [true-labels (set (:atoms result))]
    (into #{} (filter #(true-labels (atoms/label-of-atom table (atoms/atom-of-sentex table %))))
          assumptions)))

(defn- handles-of
  "The assumption handles behind `labels` — a solver's answer set, as label strings."
  [table labels]
  (into #{} (keep #(some->> (atoms/atom-of-label table %)
                            (atoms/sentex-id-of-atom table)))
        labels))

(defn classify-program
  "Classify `program`'s assumptions into `:true` / `:supportable` / `:false` by
  brave/cautious reasoning over its optimal answer sets — in every optimum, in some,
  in none.

  `:fixed` handles are reported `:true`: known-true background is assumed by every
  model, which is what makes it background rather than something the solver decides.
  With no ASP backend every contested assumption is genuinely one of several options,
  so it is reported `:supportable` and nothing is claimed forced or excluded.

  Below `vaelii.core` on purpose — the classification is a property of the encoding and
  the backend, not of any KB — so `settle` can stamp it onto the TMS as belief settles.
  `asp.label` re-exports it for the KB-level callers that predate the move."
  [{:keys [assumptions fixed] :as program}]
  (let [base {:true (set fixed) :supportable #{} :false #{}}]
    (cond
      (empty? assumptions) base
      (not (solver/available?)) (assoc base :supportable (set assumptions))
      :else
      (let [{:keys [aspif table]} (translate program {:tiebreak? false})
            {:keys [cautious brave]} (solver/classify-both aspif)
            in-every (handles-of table (:atoms cautious))
            in-some  (handles-of table (:atoms brave))]
        {:true        (into (set fixed) (filter in-every) assumptions)
         :supportable (into #{} (filter #(and (in-some %) (not (in-every %)))) assumptions)
         :false       (into #{} (remove in-some) assumptions)}))))

(defn enumerate-optima
  "Every optimal answer set of `program`, each as the **set of its chosen-true
  assumption handles** — the raw material for materializing one labeling context per
  answer set (docs/solving.md).

  Uses the solver's `:all-optima` mode over the **tiebreak-off** encoding, so genuinely
  tied optima come back as distinct witnesses rather than collapsing to one.  A witness's
  atom labels are mapped back through `handles-of`.

  Returns:
  * `[]`        — no assumptions (nothing to decide; the caller makes no labeling);
  * `nil`       — no ASP backend (enumeration needs one; the caller reports that);
  * `[#{h} …]`  — one handle-set per optimum otherwise.

  With assumptions but no nogoods every choice can be kept, so the single optimum keeps
  them all; a `functional`/`disjoint`/`¬` clash is what splits the optima apart."
  [{:keys [assumptions] :as program}]
  (cond
    (empty? assumptions)      []
    (not (solver/available?)) nil
    :else
    (let [{:keys [aspif table]} (translate program {:tiebreak? false})
          {:keys [witnesses]}   (solver/solve aspif :all-optima)]
      ;; distinct: two optimal *models* can project to the same set of chosen
      ;; assumptions (they differ only in violation atoms), and those are one labeling
      (into [] (distinct) (map #(handles-of table %) witnesses)))))

(def edge-solver
  "An ASP-backed `solve/Solver`.  Install with `(core/set-solver kb edge-solver)`.

  Falls back to `solve/local-solver` when no ASP backend is reachable, so this is
  safe to install unconditionally; check `(solver/available?)` if you need to know
  which one will run."
  (reify solve/Solver
    (solve [_ program]
      (let [{:keys [aspif] :as t} (translate program)]
        (cond
          ;; nothing contested — only the structurally hopeless remain
          (nil? aspif)             {:defeat #{} :violated (vec (:doomed t))}
          (not (solver/available?)) (solve/solve solve/local-solver program)
          :else
          (let [result (solver/solve aspif :label)]
            (if (= :unsat (:status result))
              ;; every contradiction is soft, so this should be unreachable; if the
              ;; encoding ever regresses, degrade rather than lie about belief.
              (solve/solve solve/local-solver program)
              (interpret t result))))))))

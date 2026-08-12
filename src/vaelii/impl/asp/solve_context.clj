;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.asp.solve-context
  "Solving as a **persistent, inert** artifact: `assumptionRules` define choices, a
  solve grounds them (scoped to a base context), enumerates the optimal answer sets,
  and materializes **each one as its own labeling context** — a `genlContext` child of
  the base holding the chosen truth values as inert sentexes.  `classify` then gathers
  brave/cautious over those labelings.

  The two imperatives `(do/label Base Into)` and `(do/classify Into)` route here.

  ## Why inert, and why per-answer-set

  Belief in this KB is global (one JTMS, not an ATMS): a *believed* `(not head)` in a
  context that sees the base would defeat the base's `head` everywhere — so only one
  labeling could ever exist (the `do/labeling` global-commit).  Materializing the truth
  values **inert** (`core/assert-inert` — stored and indexed but not a JTMS premise)
  sidesteps that entirely: an inert sentex is never IN, so it is invisible to the
  belief-filtered nogood scan, forms no contradiction, and moves no belief.  Every
  answer set therefore coexists as its own context, the base KB is untouched, and the
  result **persists in the records** for inspection.

  ## What persists, and what does not

  The **answer** persists: the labeling contexts and the classification, as inert
  sentexes in the records.  The **grounding** — the menu of candidate choice heads —
  never does.  A grounding is derived solver working state, recomputable from the
  assumptionRules and the base's believed facts; an inert copy would carry no
  justification linking it back to what produced it, so it would rot silently the
  moment the base moved.  The Program keys on program-local ids (see `build`), and
  `label` returns the menu as `:choices` for a caller who wants to see it.

  And what persists is **replaced on re-run**, never accreted: `label` clears a
  previous run's artifacts under the same `Into` before writing (see `clear-run!`),
  and `classify` clears its own previous classification.  Truth values from two
  different groundings unioned into one context assert nothing at all.

  ## MVP scope (docs/solving.md)

  Constraints are the engine's own contradictions among the **direct** ground choice
  heads — a `(not X)`/`X` pair, a `functional` predicate given two values, or a
  `disjoint` type clash.  Choices do **not** propagate through ordinary rules yet
  (that is provenance-propagation / full clingo grounding, the named follow-ups)."
  (:require [clojure.set :as set]
            [clojure.string :as str]
            [vaelii.core :as v]
            [vaelii.impl.asp.edge :as edge]
            [vaelii.impl.asp.solver :as solver]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.solve :as solve]))

;; ---- context naming and ownership ----------------------------------------
;; `Into` is a context name (ends in "Context") that seeds the run's artifact
;; names: labelings are numbered `<base>1Context`, `<base>2Context`, …, and the
;; classification lands in `<base>ClassContext`.  The names are for humans;
;; **ownership is recorded, never inferred from a name**: each labeling context
;; carries an inert `(labelingOf <ctx> <Into> <i>)` marker, and rediscovery reads
;; the markers back through the term index.  So a user context that happens to be
;; named `<base><i>Context` is neither read by `classify` nor swept by a re-run —
;; a name pattern would make both mistakes, and with a destructive sweep the
;; second one is data loss.

(defn- base-name [ctx] (str/replace (name ctx) #"Context$" ""))
(defn- ctx-sym [& parts] (symbol (str (apply str parts) "Context")))
(defn- class-context [into]    (ctx-sym (base-name into) "Class"))
(defn- labeling-context [into i] (ctx-sym (base-name into) i))

(defn- marker?
  "Is this stored sentence a `labelingOf` ownership marker?"
  [sentence]
  (and (seq? sentence) (= 'labelingOf (first sentence))))

(defn- labeling-contexts
  "The labeling contexts a prior `label` created for `into`, in labeling order —
  read from the `(labelingOf <ctx> <Into> <i>)` marker each one carries, through
  the term index.  Exact ownership, no name pattern (see the naming comment)."
  [kb into]
  (->> (v/find-sentexes kb into)
       (keep (fn [s]
               (let [f (:sentence s)]
                 (when (and (marker? f) (= into (nth f 2 nil)))
                   [(nth f 3 0) (second f)]))))
       (sort-by first)
       (mapv second)))

(defn- free-labeling-contexts
  "Labeling context names for `n` answer sets: `<base><i>Context` counting up from 1,
  skipping any name an unrelated context already occupies — in the hierarchy, or
  with a non-empty extent.  A re-run's own previous contexts were cleared just
  before this runs, so they do not block their own slots; a user context that
  happens to share the naming is never written into (the marker keeps it out of
  rediscovery, this keeps it out of materialization)."
  [kb into n]
  ;; `into` names the Into context here (as everywhere in this ns), so this body
  ;; must not touch clojure.core/into
  (let [existing (set (v/contexts kb))
        taken?   (fn [c] (or (existing c) (pos? (v/count-in-context kb c))))]
    (->> (iterate inc 1)
         (map #(labeling-context into %))
         (remove taken?)
         (take n)
         vec)))

;; ---- replace-on-rerun ----------------------------------------------------

(defn- clear-context!
  "Retract everything in or about `ctx`: its extent and any sentex that mentions it
  — the labeling truth values and their marker, the `genlContext` edge that hangs it
  under a base, a stale classification.  The term index makes that one lookup
  (`find-sentexes`), and `retract!` tears an inert sentex down directly.

  Guarded: if anything in the extent is *believed*, `ctx` is not a solve artifact —
  everything a solve writes into its contexts is inert by construction — and nothing
  is touched.  The sweep must never destroy knowledge, whatever a context is named."
  [kb ctx]
  (when (not-any? #(v/in? kb (:id %)) (v/sentexes-in-context kb ctx))
    (doseq [s (v/find-sentexes kb ctx)]
      (v/retract! kb (:id s)))))

(defn- clear-run!
  "Remove every artifact a previous `(do/label _ Into)` / `(do/classify Into)` left:
  the numbered labeling contexts and the classification.
  Replace-on-rerun is what keeps a run from accreting across groundings — an inert
  `(head)` beside an inert `(not head)` in one context asserts nothing — and
  retracting the `genlContext` edges is what drops a surplus stale context (a run
  that shrank from three labelings to two) out of the hierarchy, so `classify`
  cannot sweep it back in."
  [kb into]
  (doseq [ctx (concat (labeling-contexts kb into) [(class-context into)])]
    (clear-context! kb ctx)))

;; ---- grounding: assumptionRules × visible facts → choice heads -----------

(defn- assumption-rules
  "Every **believed** `assumptionRule` visible from `base` — scoped to `base` and its
  genlContext up-closure, never the whole KB.  `sentexes-in-context` reads storage, so
  the belief question is asked here, as both chainers ask it: a defeated or superseded
  assumptionRule must not mint choice heads.  `rule-believed?` rather than `jtms/in?`
  so an `:inert` rule stays available — this run is the fourth consumer of a rule's
  firing beside the three chainers, and it reads rules by the same rule they do."
  [kb base]
  (for [ctx (distinct (cons base (v/context-up kb base)))
        s   (v/sentexes-in-context kb ctx)
        :when (and (rules/assumption? s) (res/rule-believed? kb (:id s)))]
    s))

(defn- ground-heads
  "The distinct ground choice heads: each assumptionRule's antecedents proved over the
  facts believed in `base` (a scoped, belief-filtered join), its head substituted with
  each solution's bindings.  MVP assumes a positive head literal.

  A rule's `exceptWhen` guard is honored per binding, evaluated in `base` — grounding
  is a fourth consumer of a rule's firing beside the three chainers, and it makes the
  same decision they do (docs/exceptions.md): a choice the exception holds of is not
  offered.  That is what makes an exception the way to say \"this candidate is already
  ruled out\" declaratively, instead of the caller pre-filtering the menu."
  [kb base]
  (distinct
   (for [rsx (assumption-rules kb base)
         :let [ante  (vec (rules/antecedents (:sentence rsx)))
               head  (rules/consequent (:sentence rsx))
               guard (provers/rule-guard kb rsx base)]
         binding (v/prove kb ante base)
         :when (or (nil? guard) (guard binding))]
     (res/substitute head binding))))

;; ---- constraints among the heads (MVP: direct only) ----------------------

(defn- negation-pair? [s1 s2]
  (or (= s1 (list 'not s2)) (= s2 (list 'not s1))))

(defn- functional-clash?
  "Two heads of a `functional` predicate that agree on the first argument but differ
  on the value — the constraint that makes `functional color` mean 'at most one'."
  [kb s1 s2]
  (and (sequential? s1) (sequential? s2)
       (= 3 (count s1)) (= 3 (count s2))
       (= (first s1) (first s2))
       (= (second s1) (second s2))
       (not= (nth s1 2) (nth s2 2))
       (v/has-prop? kb :functional (first s1))))

(defn- disjoint-clash?
  "Two unary type memberships of the same individual whose types are disjoint."
  [kb s1 s2]
  (and (sequential? s1) (sequential? s2)
       (= 2 (count s1)) (= 2 (count s2))
       (= (second s1) (second s2))
       (not= (first s1) (first s2))
       (v/disjoint? kb (first s1) (first s2))))

(defn- clash? [kb s1 s2]
  (or (negation-pair? s1 s2)
      (functional-clash? kb s1 s2)
      (disjoint-clash? kb s1 s2)))

(defn- pairs [xs]
  (let [v (vec xs)]
    (for [i (range (count v)), j (range (inc i) (count v))] [(v i) (v j)])))

(defn- positive-core
  "A head's positive body — a `(not X)` unwrapped to X, else the head itself."
  [s]
  (if (and (seq? s) (= 'not (first s))) (second s) s))

(defn- clash-key
  "The bucket a head can clash within: the first argument of its positive body.  A
  negation pair, a functional clash, and a disjoint clash all require the two heads to
  agree on that argument, so heads with different keys can never clash — which turns the
  O(n²) all-pairs scan into O(Σ bucket²), flat when buckets are small (a node's three
  colours, say).  A head with no argument buckets under nil."
  [s]
  (let [p (positive-core s)]
    (when (and (sequential? p) (> (count p) 1)) (nth p 1))))

(defn- nogoods
  "The nogoods the auto-clash detectors find among the candidate heads (keyed by their
  program-local ids): one per clashing pair, uniform priority.  Heads are bucketed by
  `clash-key` and only compared within a bucket — the full pairwise `clash?` restricted
  to pairs that could possibly clash, so a 3-coloring's 30k choice heads cost O(nodes)
  rather than O(heads²).  The bucketing is content-derived and each bucket is sorted, so
  the nogood set is order-independent."
  [kb head->id]
  (for [bucket (vals (group-by (comp clash-key key) head->id))
        [[s1 _] [s2 _]] (pairs (sort-by (comp pr-str key) bucket))
        :when   (clash? kb s1 s2)]
    {:nogood #{(head->id s1) (head->id s2)}
     :priority 1
     :sentence (list 'contradicts s1 s2)}))

;; ---- constraint rules: a conjunctive nogood over facts + choice heads -----
;; A `set/hardConstraint` / `set/softConstraint` rule's body is a nogood template
;; mixing background facts and choice-head patterns.  Grounding it is a JOIN: the
;; background literals against the facts believed in `base`, the choice literals against
;; the ground choice heads.  Each satisfying binding yields the set of choice-head ids it
;; used — a model choosing all of them together is forbidden (hard) or penalized (soft).
;; This is what lets a constraint relate two *different* individuals (edge adjacency),
;; which the direct-clash detectors above — always one shared individual — cannot.

(defn- constraint-rules
  "Every **believed** constraint rule visible from `base` — scoped to `base` and its
  genlContext up-closure, and belief-filtered, like `assumption-rules`: a defeated or
  superseded constraint must not go on forbidding models."
  [kb base]
  (for [ctx (distinct (cons base (v/context-up kb base)))
        s   (v/sentexes-in-context kb ctx)
        :when (and (rules/constraint? s) (res/rule-believed? kb (:id s)))]
    s))

(defn- choice-arg-index
  "Index the ground choice heads for join lookup:
     :by-pred {pred [head …]}                 — every head of a predicate
     :by-arg  {[pred pos val] #{head …}}      — heads with `val` at 1-based arg `pos`
  A partially-ground choice literal is matched by intersecting the `:by-arg` sets for its
  ground argument positions (`literal-heads`) — so an edge×colour probe is a couple of
  set reads, not a scan of every head."
  [heads]
  (reduce
   (fn [idx head]
     (let [pred (first head)]
       (reduce (fn [idx [i a]]
                 (update-in idx [:by-arg [pred (inc i) a]] (fnil conj #{}) head))
               (update-in idx [:by-pred pred] (fnil conj []) head)
               (map-indexed vector (rest head)))))
   {}
   heads))

(defn- literal-heads
  "The choice heads a (partially ground) choice literal `lit` can match, via `idx` —
  intersect the `:by-arg` sets for its ground argument positions; with no ground
  argument, every head of the predicate."
  [idx lit]
  (let [pred   (first lit)
        ground (for [[i a] (map-indexed vector (rest lit))
                     :when (not (sx/variable? a))]
                 [pred (inc i) a])]
    (if (seq ground)
      (reduce set/intersection (map #(get-in idx [:by-arg %] #{}) ground))
      (get-in idx [:by-pred pred] []))))

(defn- join-choice-literals
  "Extend binding `b` (and its accumulated choice-head-id set `ids`) across the choice
  literals `chs`, matching each against `idx`.  Returns `[[binding ids] …]`."
  [idx head->id chs b ids]
  (if (empty? chs)
    [[b ids]]
    (let [lit (res/substitute (first chs) b)]
      (mapcat (fn [head]
                (when-let [b2 (res/unify lit head b)]
                  (join-choice-literals idx head->id (rest chs) b2 (conj ids (head->id head)))))
              (literal-heads idx lit)))))

(defn- neg-choice-lit?
  "A `(not <choice-literal>)` body literal — a choice head required to be *absent*.  A
  conjunction of these is an at-least-one requirement: `(not c1) (not c2) (not c3)`
  forbids a model in which all three are false, i.e. forces at least one true."
  [choice-preds l]
  (and (seq? l) (= 'not (first l)) (sequential? (second l))
       (choice-preds (first (second l)))))

(defn- ground-constraint-body
  "Join `body` over the facts believed in `base` (background literals) and the ground
  choice heads (positive choice literals — predicate in `choice-preds`), carrying any
  *negated* choice literals `(not <choice>)` through as a set of choice-head ids
  required-absent.  Returns `[[#{pos-ids} #{neg-ids} marker] …]`, one per satisfying
  binding.

  Background literals are solved together through the ordinary conjunctive prover
  (`v/prove`, belief-filtered and cost-planned); each solution is extended across the
  positive choice literals against the choice-head index, and the negated choice
  literals are grounded and looked up.  Literals are classified by predicate — a body
  predicate naming a choice head is a choice literal, everything else a background fact
  — the modeling contract for a constraint body.  Negated *background* literals are out
  of scope."
  [kb base body consequent choice-preds head->id idx]
  (let [neg?        #(neg-choice-lit? choice-preds %)
        neg-chs     (filterv neg? body)
        rest-body   (remove neg? body)
        choice-lit? #(and (sequential? %) (choice-preds (first %)))
        bg  (remove choice-lit? rest-body)
        chs (filter choice-lit? rest-body)]
    (for [bgb     (if (seq bg) (v/prove kb (vec bg) base) [{}])
          [b ids] (join-choice-literals idx head->id chs bgb #{})
          :let    [neg-ids (into #{} (keep #(head->id (res/substitute (second %) b))) neg-chs)]
          ;; every negated choice literal must name a real choice head, else it can never
          ;; be false-together and the requirement it guards is vacuous for this binding
          :when   (and (= (count neg-ids) (count neg-chs))
                       (or (seq ids) (seq neg-ids)))]
      [ids neg-ids (res/substitute consequent b)])))

(defn- constraint-nogoods
  "Ground every constraint rule visible from `base` into nogoods, one per satisfying
  binding of its body.  A positive body yields a `:nogood` (those choice heads forbidden
  to hold together); a negated-choice body yields a `:neg` (forbidden to be absent
  together — an at-least-one).  A `set/hardConstraint` rule's nogoods carry `:hard true`
  (an integrity constraint — a violating model is excluded outright); a
  `set/softConstraint` rule's are minimized like the auto-detector's."
  [kb base head->id]
  (let [choice-preds (into #{} (map first) (keys head->id))
        idx          (choice-arg-index (keys head->id))]
    (for [rsx (constraint-rules kb base)
          :let [body   (vec (rules/antecedents (:sentence rsx)))
                conseq (rules/consequent (:sentence rsx))
                hard?  (= :hard (rules/constraint-of rsx))]
          [ids neg-ids marker] (ground-constraint-body kb base body conseq choice-preds head->id idx)]
      (cond-> {:nogood ids :priority 1 :sentence (list 'contradicts marker)}
        (seq neg-ids) (assoc :neg neg-ids)
        hard?         (assoc :hard true)))))

;; ---- the program ---------------------------------------------------------

(defn- build
  "Ground the choices **in memory**, detect the constraints among them (both the direct
  auto-clashes and the ground constraint-rule bodies), and build the Program.  Returns
  `{:program p :head->id {sentence id}}` or nil when there are no choices to make — and
  writes nothing, so a solve that goes on to fail (no backend) has no side effects to
  undo.

  The ids are program-local, minted over the content-sorted heads — never KB handles.
  Nothing needs more: `solve/content-key` orders by sentence + context, and an atom
  label is only ever read back within the solve that minted it.  Storing the menu
  instead (the old design) left write-only sentexes nothing maintained — see the ns
  docstring, \"What persists, and what does not\"."
  [kb base]
  (let [heads (sort-by pr-str (ground-heads kb base))]
    (when (seq heads)
      (let [head->id (into {} (map-indexed (fn [i s] [s (inc i)])) heads)
            content  (into {} (map (fn [[s id]] [id {:sentence s :context base}])) head->id)
            ngoods   (concat (nogoods kb head->id)
                             (constraint-nogoods kb base head->id))
            program  (solve/program (set (vals head->id)) ngoods content)]
        {:program program :head->id head->id}))))

;; ---- do/label: one inert labeling context per optimal answer set ---------

(defn- one-optimum
  "One answer set as `[kept-set]`, or nil with no ASP backend — the single-labeling
  counterpart to `edge/enumerate-optima`, split by phase for a caller that wants to time
  grounding against solving.

  `keep-belief?` chooses the objective: on, the solve minimizes defeated assumptions
  (one *optimal* answer, keeping as much belief as possible); off, it is plain
  satisfaction (one *satisfying* answer, no optimization), which is the difference
  between finishing and not at scale.  Tiebreak is always off here — its per-atom
  objective is its own scaling wall, and singling out one of many valid answers is not
  wanted; the content-keyed program is order-independent and clingo deterministic, so
  one solve is a stable answer regardless.  Returns `{:optima [#{ids}] :translate-ms t
  :solve-ms t}`, or `{:optima nil}`."
  [program keep-belief?]
  (if-not (solver/available?)
    {:optima nil}
    (let [ta         (System/nanoTime)
          translated (edge/translate program {:tiebreak? false :keep-belief? keep-belief?})
          tb         (System/nanoTime)
          result     (solver/solve (:aspif translated) :label)
          tc         (System/nanoTime)]
      {:optima      [(edge/kept-of translated result)]
       :translate-ms (/ (- tb ta) 1e6)
       :solve-ms     (/ (- tc tb) 1e6)})))

(defn label
  "Ground the `assumptionRules` visible from `Base` (honoring their `exceptWhen`
  guards), detect the constraints among the ground choice heads — the direct
  auto-clashes *and* every `set/hardConstraint` / `set/softConstraint` rule's body
  ground into a nogood — and solve.

  **`mode` (an optional third argument, default `:all`) picks how many worlds:**

    * `:all` — enumerate **every** optimal answer set and materialize each as its own
      inert labeling context: a `genlContext` child of `Base` named
      `<Into-base><i>Context` (skipping any slot an unrelated context occupies) holding
      `(head)` for a chosen-true choice, `(not head)` for a chosen-false one, and its
      `labelingOf` ownership marker.  The worlds coexist and persist for `do/classify` to
      aggregate; base belief is untouched.  This is the studying-many-worlds mode, and it
      is infeasible where the optima are astronomically many (a large graph coloring has
      too many valid colorings to enumerate).
    * `:one` — commit to **one** optimal answer set via a single `:label` solve
      (minimizing defeated assumptions — keep as much belief as possible), and return it
      in the result **without persisting anything**.  The solving mode: it wants an
      answer, not an artifact, so it is feasible at scale (one solve, no enumeration, no
      materialization).  `Into` is accepted for a uniform imperative shape but unused.
    * `:sat` — `:one`, but plain **satisfaction** rather than optimization: no
      keep-belief objective, so clingo stops at the first model instead of proving
      cost-optimality over the choice atoms.  For a program whose hard constraints
      already pin what must be chosen (a graph coloring's hard at-least-one), \"keep as
      much as possible\" is redundant and the optimization is a scaling wall — `:sat`
      finishes where `:one` does not.  Same shape as `:one` (returns one labeling,
      persists nothing).

  **Replace-on-rerun (`:all` only).**  A previous `:all` run's artifacts under `Into`
  are cleared before new ones are written, so re-running after the base moved converges
  instead of accreting.  A run that grounds *no* choices clears too.  The one exception
  is `:no-backend` — nothing was computed, so the previous artifact is left standing.

  The grounding is never stored; `:choices` is the menu in content order (see `build`).
  Phase timings (`:ground-ms` = grounding the Program, `:translate-ms` = rendering ASPIF,
  `:solve-ms` = the solve) ride the result for a profiling caller.

  Returns `{:base :into :choices [..] :labelings [{:context :true [..] :false [..]}]
  :count n}` (`:context` nil in `:one` mode, which persists nothing).  `:count 0` with
  `:reason` when there is nothing to solve or no ASP backend."
  ([kb base into] (label kb base into :all))
  ([kb base into mode]
   (let [t0    (System/nanoTime)
         built (build kb base)
         t1    (System/nanoTime)]
     (if-let [{:keys [program head->id]} built]
       (let [id->head (zipmap (vals head->id) (keys head->id))
             all-ids  (set (vals head->id))
             choices  (vec (sort-by pr-str (keys head->id)))
             single?  (contains? #{:one :sat} mode)
             {:keys [optima translate-ms solve-ms]}
             (if single?
               (one-optimum program (= mode :one))     ; :sat ⇒ keep-belief off (plain SAT)
               (let [ta (System/nanoTime), o (edge/enumerate-optima program)]
                 {:optima o :solve-ms (/ (- (System/nanoTime) ta) 1e6)}))
             timing   {:ground-ms (/ (- t1 t0) 1e6) :translate-ms translate-ms :solve-ms solve-ms}
             labeling (fn [chosen] {:true  (vec (map id->head chosen))
                                    :false (vec (map id->head (remove (set chosen) all-ids)))})]
         (cond
           (nil? optima)
           (merge {:base base :into into :count 0 :choices choices
                   :reason :no-backend :labelings []} timing)

           ;; :one / :sat — return the single labeling, persist nothing
           single?
           (merge {:base base :into into :count 1 :choices choices
                   :labelings [(assoc (labeling (first optima)) :context nil)]} timing)

           ;; :all — materialize each optimum as its own inert labeling context
           :else
           (do
             (clear-run! kb into)
             (let [ctxs (free-labeling-contexts kb into (count optima))]
               (merge {:base base :into into :count (count optima) :choices choices
                       :labelings
                       (vec (map-indexed
                             (fn [i chosen]
                               (let [ctx    (nth ctxs i)
                                     l      (labeling chosen)
                                     truths (:true l)
                                     falses (:false l)]
                                 ;; a genlContext edge so the labeling shows under Base in the tree;
                                 ;; monotonic because it is a real structural edge, not a solve result
                                 (v/assert kb (list 'genlContext ctx base) base {:strength :monotonic})
                                 ;; the ownership marker rediscovery reads (see labeling-contexts)
                                 (v/assert-inert kb (list 'labelingOf ctx into (inc i)) ctx)
                                 (doseq [s truths] (v/assert-inert kb s ctx))
                                 (doseq [s falses] (v/assert-inert kb (list 'not s) ctx))
                                 (assoc l :context ctx)))
                             optima))}
                      timing)))))
       (do (when-not (contains? #{:one :sat} mode) (clear-run! kb into))
           {:base base :into into :count 0 :choices []
            :reason :no-choices :labelings []})))))

;; ---- do/classify: gather brave/cautious over the labelings ---------------

(defn- polarity-table
  "One labeling context's extent as a map from choice head to the polarity it
  records — `:true` for `(head)`, `:false` for `(not head)`; the ownership marker
  is skipped.  **One extent read per context**: reading the whole extent once per
  labeling and answering every (context, head) probe from the map keeps classify's
  store traffic linear rather than quadratic in the solve's size.  A head absent from
  the map (nil) is a labeling that says nothing about it, which classifies as
  `:supportable` below."
  [kb ctx]
  (into {}
        (keep (fn [{:keys [sentence]}]
                (cond
                  (marker? sentence) nil
                  (and (seq? sentence) (= 'not (first sentence))) [(second sentence) :false]
                  :else [sentence :true])))
        (v/sentexes-in-context kb ctx)))

(defn classify
  "Gather brave/cautious over the labelings a prior `(do/label _ Into)` produced, and
  record the result as inert sentexes in `<Into-base>ClassContext`.  A choice head is

    * `(forced H)`      — `(head)` in **every** labeling (a cautious/skeptical consequence),
    * `(excluded H)`    — `(not head)` in every labeling,
    * `(supportable H)` — otherwise (a brave/credulous consequence only).

  Pure aggregation over the persisted labeling contexts — no solver, no whole-KB scan,
  and **one extent read per labeling** (`polarity-table`), with everything after in
  memory.  Its own previous classification is cleared first (replace-on-rerun,
  same discipline as `label`): a stale classification describes labelings that no
  longer exist.  Returns `{:class-context :forced [..] :supportable [..] :excluded [..]}`,
  or `:count 0` `:reason :no-labelings` when `label` was never run for `Into`."
  [kb into]
  (let [labelings (labeling-contexts kb into)]
    (if (empty? labelings)
      {:into into :count 0 :reason :no-labelings
       :forced [] :supportable [] :excluded []}
      (let [tables (mapv #(polarity-table kb %) labelings)
            heads  (distinct (mapcat keys tables))
            klass  (class-context into)
            classify-one
            (fn [s]
              (let [ps (map #(get % s) tables)]
                (cond (every? #(= :true %) ps)  :forced
                      (every? #(= :false %) ps) :excluded
                      :else                     :supportable)))
            grouped (group-by classify-one heads)]
        (clear-context! kb klass)
        (doseq [[k ss] grouped, s ss]
          (v/assert-inert kb (list (symbol (name k)) s) klass))
        {:into into :class-context klass :count (count labelings)
         :forced      (vec (:forced grouped))
         :supportable (vec (:supportable grouped))
         :excluded    (vec (:excluded grouped))}))))

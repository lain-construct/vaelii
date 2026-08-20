;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.taxonomy
  "Cached transitive closures for the two transitivity relations at the heart of
  common-sense reasoning:

    genl    relates unary *types*    (genl dog animal)   — the type hierarchy
    genlCx  relates *contexts*       (genlCx CxA CxB)     — context inheritance

  Transitivity is not done with rules (too central, too hot); instead we store the
  **direct adjacency** of each relation and answer the reflexive-transitive up/down
  closure *on demand*.  `genls` is ancestors-incl-self, `specs` is descendants-
  incl-self.

  We deliberately do **not** materialize the full closure.  A materialized closure
  is Θ(V²) for a deep hierarchy — a 10k-node `genl` chain stores ~50M pairs — so
  building it incrementally makes a bulk load quadratic no matter how clever each
  insert is: the representation itself is the cost.  Storing only the O(V+E)
  adjacency makes a closure read O(reachable-subgraph) and an insert the adjacency
  write plus a depth repair — O(1) for an edge arriving parent-before-child, and
  proportional to the *descendants* of the node `raise-depth` lifts for one arriving
  child-first, so that order is quadratic in the hierarchy and `*defer-depths?*` is
  the trade written for it.  Reads are memoized per closure
  *generation* (bumped on every edge change), so a shallow hierarchy — where the
  reachable subgraph is tiny — still answers each repeat read in O(1).

  - **Insertion** records the edge in `:fwd` / `:rev` and, so cycle checks stay
    cheap, maintains a topological `:depth` potential (`edge x→y ⇒ depth[x] >
    depth[y]`).  No closure is touched.
  - **Deletion** drops the edge from the adjacency and prunes any node left with no
    edge.  Depths are left as loose upper bounds — a deletion only relaxes the
    ordering, so the invariant survives untouched.
  - **Cycle safety.** `genl?` / `sees?` answer reachability with an early-exit walk
    pruned by `:depth`: a real path `x → … → y` has strictly decreasing depth, so
    `depth[x] ≤ depth[y]` rejects the pair in O(1).  `wff` rejects `genl` /
    `genlCx` cycles up front, so the closures stay acyclic; `reach` guards with a `seen` set
    regardless, so a stray cycle terminates rather than being subtly wrong.

  `closures` (the from-scratch materialized build) survives as the **reference
  implementation** the on-demand reads are tested against — the oracle test in
  `taxonomy_test` compares `genls` / `specs` for every node against it after every
  random edit.

  Context semantics: (genlCx Sub Super) means Sub *sees* Super's assertions, so a
  context K sees a sentex in context Y iff Y is in genls-of-contexts(K).

  ## Edges are supported, and support is belief-sensitive

  A relation is `{:support {[a b] {handle ctx}} :edges #{[a b]} :fwd {} :rev {}
  :nodes #{} :depth {} :gen n}`.  `:support` records **every sentex that asserts an
  edge**, keyed by handle with the asserting sentex's context as the value — handle
  and context enter and leave together, so they cannot desync; a nil context means
  the writer had none to record (a probe) and the edge constrains everywhere.
  `:edges` is the *active* set the closures are computed from — an edge with
  no believed supporter is not in it.  That distinction is what keeps three things
  right:

  - **Belief.** A defeated `(genl dog animal)` leaves the closure, so `isa?` cannot
    outrun belief.  Matching is belief-sensitive everywhere in the engine, the
    taxonomy included; `refresh-beliefs` reconciles after a relabel.
  - **Reference counting.** The same edge asserted in two contexts is two sentexes.
    Retracting one must not remove the edge while the other still asserts it.
  - **Idempotence.** Re-asserting an edge that is already active is a no-op —
    `activate` returns early rather than touching the adjacency at all.

  ## Equality is the third supported relation, and it is not a partial order

  `rewriteOf` / `sameAs` / `equals` all feed one **equivalence** closure, so it is
  stored as a partition — member → class, class → members and representative —
  rather than as up/down closures.  It shares the `:support` discipline above and
  nothing else: insertion is a union, and deletion can *split* a class, which no
  union-find can undo, so it rebuilds the affected class from its surviving edges.
  See the section below and docs/equality.md.

  The same belief discipline reaches the five flat caches too — `disjoint`, the
  disjoint metatypes and their members, the predicate properties, `inverse`, and the
  declared arities.
  They carry no per-claim `:support` record of their own; their supporters are
  reference-counted in the shared `:cache-support` map, and `refresh-beliefs`
  reconciles each cache entry against belief exactly as `refresh-relation` does for
  genl — an entry is active iff some supporter is stored *and* believed.  So a
  defeated `(disjoint dog cat)` stops constraining, a defeated `(functional P)` stops
  merging, and a defeated `(inverse P Q)` stops answering the swapped goal, the way a
  defeated genl edge leaves the closure.  See docs/taxonomy.md."
  (:require [clojure.set :as set]
            [vaelii.impl.caches :as caches]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.strength :as strength]))

(defn- term-key
  "A total order on terms keyed on **content only**.  Representative choice may never
  key on a handle: handles are allocated in assertion order, so that would smuggle
  arrival order back into belief (docs/nmtms.md — it was a real bug in the Nixon
  diamond).  The class name is a second key so a symbol and a string that print
  alike still order deterministically."
  [t]
  (if (nil? t) ["" ""] [(str t) (.getName (class t))]))

(defn- term-min [terms]
  ;; keyed once per term, not twice per comparison: `term-key` allocates two strings, so
  ;; a plain reduce rebuilds it on both operands at every step.  Tie keeps the later, as
  ;; the reduce did (a tie is two terms that print alike under the same class anyway).
  (second (reduce (fn [a b] (if (neg? (long (compare (first a) (first b)))) a b))
                  (map (fn [t] [(term-key t) t]) terms))))

(defn- reach
  "Reflexive-transitive reachable set from `start` over adjacency `adj` (a fn
  node → neighbours).  Guards with a `seen` set, so a cyclic `adj` terminates."
  [start adj]
  (loop [seen (transient #{start}), stack [start]]
    (if-let [n (peek stack)]
      (let [fresh (remove #(get seen %) (adj n))]
        (recur (reduce conj! seen fresh) (into (pop stack) fresh)))
      (persistent! seen))))

(defn- reachable?
  "Is `tgt` in the reflexive-transitive reach of `src` over adjacency map `adj`,
  given topological potentials `depth` and the component map `scc`?

  `depth` is a potential over the **condensation** — the DAG of strongly connected
  components — so it obeys `edge x→y ⇒ depth[x] ≥ depth[y]`, strictly when `x` and
  `y` lie in different components and by equality inside one.  `scc` maps a node to
  its component's representative, and holds an entry **only for a node in a
  non-trivial component**; an acyclic relation (which `genl` always is, and
  `genlCx` usually is) has an empty one and pays a nil check.

  Three O(1) consequences make this cheap in the overwhelmingly common case:

  - same component ⇒ mutually reachable, by definition.  No walk at all.
  - otherwise a real path `src → … → tgt` must leave `src`'s component, so it
    strictly descends at least once: `depth[src] ≤ depth[tgt]` ⇒ unreachable.  For a
    hierarchy built roughly parent-before-child — the load order of a taxonomy — the
    node being checked against is always shallower, so the pair is rejected outright.
  - during the walk, a neighbour *below* `tgt`'s depth cannot lie on a path to it, and
    neither can one *level* with it in a different component (that path would have to
    descend too), so both are pruned — and a neighbour level with it in `tgt`'s own
    component answers true outright.

  Depths are only ever grown, never shrunk (deletion leaves them loose), so the
  invariant — hence soundness — holds regardless of edit history.  A missing depth is
  treated as `-1` (below everything): a non-node `tgt` is unreachable, a non-node
  `src` reaches only itself.

  **`depth` may be nil**, meaning no usable potential: a deferred batch insert whose
  `local-lift` broke an edge above it, or an edge that closed a cycle, leaves the
  relation `:loose?` until `restore-depths` runs.  The pruning is then dropped and the
  walk is plain — the same answer, paid for by visiting `src`'s whole reach instead of
  a prefix of it.  Pruning with a potential that is no longer sound would answer
  *false* for a real path, which here means `genl?` silently losing a subtype and
  `sees?` silently losing a context.

  Walking unpruned is **much** more expensive than it looks — on a deep hierarchy it
  is the difference between an O(1) rejection and a full ancestor walk, and `wff` pays
  one per taxonomy edge asserted — so going loose is a last resort, not the deferred
  path's normal state (see `local-lift`)."
  ([src tgt adj depth] (reachable? src tgt adj depth nil))
  ([src tgt adj depth scc]
   (let [ctgt (get scc tgt)]
     (or (= src tgt)
         (and (some? ctgt) (= ctgt (get scc src)))
         (if (nil? depth)
           (loop [seen #{src}, stack [src]]
             (if-let [n (peek stack)]
               (let [nbrs (get adj n)]
                 (if (contains? nbrs tgt)
                   true
                   (let [fresh (into [] (remove seen) nbrs)]
                     (recur (into seen fresh) (into (pop stack) fresh)))))
               false))
           (let [dt (get depth tgt)]
             (and (some? dt)
                  (> (get depth src -1) dt)
                  (loop [seen #{src}, stack [src]]
                    (if-let [n (peek stack)]
                      (let [nbrs (get adj n)]
                        (if (or (contains? nbrs tgt)
                                (and (some? ctgt)
                                     (some #(= ctgt (get scc %)) nbrs)))
                          true
                          (let [fresh (into [] (comp (remove seen)
                                                     (filter #(> (get depth % -1) dt)))
                                            nbrs)]
                            (recur (into seen fresh) (into (pop stack) fresh)))))
                      false)))))))))

(defn- adjacency [edges]
  (reduce (fn [m [a b]] (update m a (fnil conj #{}) b)) {} edges))

(defn closures
  "Compute {:edges :up :down} from scratch, for a set of [sub super] edges — the
  fully materialized closure this namespace deliberately does *not* keep.

  O(V·(V+E)) — a DFS per node.  This is the **reference implementation**: the
  on-demand `genls` / `specs` reads must answer exactly as it would, and the oracle
  test in `taxonomy_test` checks that node by node over random graphs."
  [edges]
  (let [nodes (into #{} (mapcat (fn [[a b]] [a b])) edges)
        adj   (adjacency edges)
        up    (into {} (map (fn [n] [n (reach n adj)])) nodes)
        down  (reduce (fn [m [n ups]]
                        (reduce (fn [m2 u] (update m2 u (fnil conj #{}) n)) m ups))
                      {} up)]
    {:edges (set edges) :up up :down down}))

;; `:handle-edge {handle [a b]}` is the **reverse** of `:support`: which edge each
;; supporting sentex asserts.  A handle supports exactly one edge — its sentence names
;; one — so add/del maintain it 1:1 and the key set is exactly the relation's supporters.
;;
;; It exists so `refresh-beliefs` can read the edges a settle could have moved **off the
;; moved region** rather than off the relation.  Belief moves by handle; only an edge
;; some moved handle supports can have changed its believed-supporter set, so that
;; lookup is the whole reconcile's scope.  Without it both halves of the reconcile are
;; O(vocabulary): the "did anything touch me" gate walks every supporter, and the
;; reconcile itself evaluates belief for every edge — 176ms per flip in a 64k-edge
;; relation, against a taxonomy that is the same size in every settle whatever moved.
;;
;; `:dirty` is the other half of that scope, and it exists because the edge writers are
;; **belief-blind**: `add-edge` and `del-edge` run on the assert/retract path, where no
;; `believed?` is in hand, so they recompute `:edge-ctxs` from every recorded supporter
;; rather than from the believed ones.  On an edge with a single supporter that is exact.
;; On a shared edge it is a superset — a disbelieved supporter's context reads as
;; asserting — and only a reconcile can narrow it.  So a writer leaving a shared edge
;; behind names it here, and the next reconcile takes it whether or not belief moved
;; there.  A superset is the safe interim reading (a scoped read sees an edge it should
;; not, never misses one it should), and the set stays proportional to the edits: the
;; single-supporter edge that is nearly every edge, and all of a bulk load, never enters
;; it.
;; Beside the edge set, three pieces of **derived context state**, all functions of
;; `:support` and belief the way `:edges` is:
;;
;; - `:edge-ctxs {[a b] #{ctx}}` — the supporting contexts of each *active* edge
;;   (keys ≡ `:edges`); nil in the set marks a supporter with no recorded context,
;;   which constrains everywhere.  `:gen` bumps whenever an entry moves, not only
;;   when an edge appears or disappears — a scoped closure read is a function of
;;   these, so they retire the read memo exactly as the edge set does.
;; - `:ctx-counts {ctx n}` — how many supporters (nil excluded) assert from each
;;   context, belief-blind: a superset of the believed edge contexts is all the
;;   scoped reads need, and counting every supporter keeps maintenance O(1) at the
;;   writers with nothing for belief to reconcile.
;; - `:ctxs-gen` — bumped only when a context key appears in or disappears from
;;   `:ctx-counts`, so a bulk load inside one context does not churn what is keyed
;;   on it (the visibility interning of the scoped reads).
;;
;; `:depth` is a potential over the **condensation**, and `:scc` is what makes it one:
;; a node in a strongly connected component maps to that component's representative
;; (`term-min`, so the choice is content-keyed and cannot depend on arrival order).
;; Only a node in a *non-trivial* component has an entry, so an acyclic relation
;; carries an empty map and reads exactly as it did.
(defn- empty-relation []
  {:support {} :handle-edge {} :dirty #{} :edges #{} :edge-ctxs {} :ctx-counts {} :ctxs-gen 0
   :fwd {} :rev {} :nodes #{} :depth {} :scc {} :gen 0})

;; The equality partition, defined here only so `create-taxonomy` can name it; its
;; machinery is the "equality" section further down.
(defn- empty-equality []
  {:support {} :handles #{} :handle-edge {} :out #{} :edges #{} :edge-idx {} :edge-prefs {}
   :class {} :members {}})

(defn create-taxonomy
  "A KB's taxonomy: one atom holding the cached relations, plus a **watch** bumping
  `observe/note-change` on every write to it.

  The clock is what a structure derived from the taxonomy — a qualitative constraint
  network reads `context-up` and the `genl` spec closure — stamps itself with.  A watch
  rather than a bump per mutator, because there are two dozen of those and the whole
  point of a clock is that no write can forget it.  `detached-copy` deliberately carries
  no watch: its purpose is to be mutated where nothing learns of it.  The two side atoms
  need none either — they are caches stamped by the relation's own `:gen`, so neither can
  move an answer without the main map having moved first."
  []
  (doto
   (atom {:genl (empty-relation) :genlCx (empty-relation)
          :equality (empty-equality)
          :disjoint #{} :disjoint-index {} :disjoint-metatypes #{} :metatype-members {}
          :props {} :inverse {} :arity {}
          :cache-support {} :cache-handle-keys {} :cache-dirty #{} :cache-ctxs {}
          ;; A KB installs two read-only callbacks after construction: whether any
          ;; supporter needs exception-aware scoping, and whether one supporter is
          ;; effective from a concrete reader context. Raw taxonomies (the unit-test
          ;; and what-if surface) install neither and retain the original context-only
          ;; path byte-for-byte. `:supporter-visibility-gen` invalidates scoped closure
          ;; memo entries when an except or meta-except changes without moving an edge.
          :supporter-filter-active? nil :supporter-visible? nil
          :supporter-visibility-gen 0
          ;; Oriented schematic rewrite rules (docs/equality.md, symbolic equational
          ;; reasoning).  `:rewrite-support` records every asserted rule keyed by its
          ;; equation handle; `:rewrite-active` is the believed subset `refresh-beliefs`
          ;; keeps in sync — the same support/active discipline as the equality
          ;; partition, so a defeated equation stops rewriting and a revived one resumes.
          :rewrite-support {} :rewrite-active {}
          ;; A side atom of memoized closure reads, keyed per relation and stamped
          ;; with that relation's `:gen`.  Kept *beside* the main map, not inside it,
          ;; so a read that memoizes never contends with the writer on the main atom
          ;; and never mutates the snapshot a concurrent reader is holding.  Stale
          ;; (wrong-gen) entries are ignored on read and overwritten on the next
          ;; miss, so an edge change needs only to bump `:gen`, never to clear this.
          :closure-memo (atom {})
          ;; The interned visible-context sets the scoped reads key on — one entry
          ;; per [relation context], stamped [genlCx-gen ctxs-gen] and recomputed
          ;; on a stamp mismatch.  A side atom for the same reasons as the memo; its
          ;; population is bounded by the context count, never by the read count.
          :vis-index (atom {})
          ;; The content-ordered rewrite rules (`rewrite-rules`), memoized as
          ;; `{:for <the :rewrite-active map it sorted> :rules <sorted seq>}`.  A side
          ;; atom for the same reasons as the other two, stamped on the *object* it
          ;; sorted rather than on a counter — see `rewrite-rules`.
          :rewrite-order (atom nil)})
    (add-watch ::change (fn [_ _ _ _] (observe/note-change)))))

(defn install-supporter-visibility!
  "Install the KB-owned exception visibility callbacks on `tax`.

  `active?` is the cheap whole-KB gate. `visible?` answers whether one stored
  supporter handle is believed and not excepted from one concrete reader context.
  Taxonomy remains independent of the JTMS and exception grammar; the KB owns those
  facts and supplies the two reads after its mutually-referential parts exist."
  [tax active? visible?]
  (swap! tax assoc :supporter-filter-active? active? :supporter-visible? visible?)
  tax)

(defn note-supporter-visibility-change!
  "Invalidate context-scoped derived reads after an except's effective belief moves.

  No edge or flat-cache entry is activated/deactivated here: an except is a hole in a
  visibility cone, not a global retraction. The generation is carried in scoped memo
  keys, so the next affected read recomputes while the unscoped cache stays hot."
  [tax]
  (swap! tax update :supporter-visibility-gen (fnil inc 0))
  tax)

(defn detached-copy
  "The current taxonomy state in a fresh atom, for a what-if probe: mutate the copy,
  read its closures, and the real taxonomy never learns any of it.

  The `:closure-memo` must be the copy's **own** — it is a side atom, so copying the
  map alone would share it by reference, and the probe's reads would write entries
  stamped with the probe's bumped `:gen` into the live memo.  Those entries are not
  merely wasted: the moment the live relation's gen catches up (its next real edge
  change), they answer real reads with closures computed over the probe's
  hypothetical edge — and a *second* probe copies the live gen, bumps to the same
  number, and reads them as its own.  `:vis-index` is a side atom with the same
  stamp discipline, so it gets the same isolation.

  `:rewrite-order` is stamped on the map object it sorted rather than on a number, so a
  probe's entry could never be *mistaken* for the live one's — but a shared atom would
  still have the two evicting each other's single slot on every alternation, and a side
  atom belonging to whoever reads it is the rule here rather than the exception."
  [tax]
  (atom (assoc @tax :closure-memo (atom {}) :vis-index (atom {})
               :rewrite-order (atom nil))))

;; ---- on-demand closures, memoized per generation ------------------------
;;
;; `:fwd` / `:rev` hold direct adjacency; the reflexive-transitive closure is
;; computed by `reach` and cached in `:closure-memo` under the relation's current
;; `:gen`.  Every edge change bumps `:gen`, which invalidates the whole memo for that
;; relation without touching it — a read simply sees a gen mismatch and recomputes.
;; This keeps a repeated read on a shallow hierarchy O(1) while never paying to
;; materialize a deep one.

(def ^:dynamic *closure-pass-cache*
  "An optional atom holding a `{[rel-key dir-key node vis] closure}` map for the span of a
  **read-only** pass over a still taxonomy — the closing settle's clash detection, which
  reads `genls`/`specs` for millions of memberships while writing no edge.  The gen-stamped
  memo below is keyed on the relation's generation, and a whole-corpus settle bumps that
  generation often enough that a recurring closure misses and is re-walked — the shape a
  cold rebuild's clash pass spends its time in.  When this is bound, `closure-of` /
  `closure-of-vis` answer from it and populate it, so each closure is walked once for the
  pass; the pass owns the atom and drops it on the way out, and the generation cannot move
  under a reader that does not write.  nil off such a pass, where the gen-stamped memo is
  the only cache and a mutation must retire it."
  nil)

(defn- closure-of
  "The reflexive-transitive reach of `node` in relation `rel-key`, direction
  `dir-key` (`:fwd` up, `:rev` down), memoized per generation.  `tax` is the
  taxonomy atom."
  [tax rel-key dir-key node]
  (let [pc *closure-pass-cache*
        pk (when pc [rel-key dir-key node nil])]
    (or (when pc (get @pc pk))
        (let [t    @tax
              rel  (get t rel-key)
              gen  (:gen rel)
              memo (:closure-memo t)
              m    @memo
              cur  (when (= gen (get-in m [rel-key :gen])) (get m rel-key))
              s    (or (get-in cur [dir-key node])
                       (let [s (reach node #(get (dir-key rel) %))]
                         (swap! memo (fn [mm]
                                       (let [e (get mm rel-key)
                                             e (if (= gen (:gen e)) e {:gen gen :fwd {} :rev {}})]
                                         (assoc mm rel-key (assoc-in e [dir-key node] s)))))
                         s))]
          (when pc (swap! pc assoc pk s))
          s))))

;; ---- scoped reads: the visibility filter over the same closures ----------
;;
;; A read asked from context K uses exactly the edges K can see — an edge counts
;; iff some believed supporter asserts it from a context in K's genlCx
;; up-cone (`:edge-ctxs`), the same filter `matches-visible` applies to facts.
;; The genlCx closure itself is never filtered: visibility scoped by
;; visibility would be circular, and `forcedDecontextualizedPredicate` already
;; forces every genlCx edge universal.
;;
;; The filter is keyed on `vis = up(K) ∩ ctxs`, where `ctxs` is the relation's
;; context census (`:ctx-counts` keys).  Since every edge's context set is a
;; subset of `ctxs`, two contexts with the same `vis` induce the identical
;; filtered edge set — so `vis` is the memo key, a function of the answer rather
;; than a proxy for it.  nil `vis` means the answer cannot differ from the global
;; one (no context given, or K sees every asserting context): the caller takes
;; today's path and today's memo slot, byte-identical.

(defn- scoped-context?
  "A concrete context to scope by — a symbol that is not a `?var`.  nil and `'?ctx`
  both mean unscoped."
  [context]
  (and (symbol? context) (not (.startsWith (name context) "?"))))

(declare visible-ctxs context-up sees?)

(defn- supporter-filter-active?
  "Does this KB currently need supporter-level exception filtering?"
  [t]
  (boolean (when-let [active? (:supporter-filter-active? t)] (active?))))

(defn- scope-admits-supporter?
  "Does `scope` admit supporter `[handle context]`?

  A plain set is the original context-only scope. An exception-aware scope is a map
  carrying that same visible-context set (nil means every asserting context), the
  concrete reader, and the KB-owned supporter predicate."
  [scope handle supporter-context]
  (if (map? scope)
    (let [{:keys [contexts context supporter-visible?]} scope]
      (and (or (nil? supporter-context)
               (nil? contexts)
               (contains? contexts supporter-context))
           (supporter-visible? handle context)))
    (or (nil? supporter-context) (scope supporter-context))))

(defn- relation-scope
  "The scoped-read key for `rel-key` from `context`, or nil for the global fast path.

  With no exception roster this is exactly `visible-ctxs`'s old set/nil answer. Once
  an exception exists, retain the concrete reader and visibility generation because
  two readers with the same inherited asserting contexts may hide different handles."
  [tax rel-key context]
  (when (scoped-context? context)
    (let [t   @tax
          rel (get t rel-key)
          ;; An exception on genlCx changes which assertion contexts an ordinary
          ;; reader inherits.  genlCx itself must start from the raw cone to avoid
          ;; defining exception visibility in terms of itself; every other relation
          ;; uses the effective cone.  Do not intern this effective set in :vis-index:
          ;; its identity moves with supporter visibility, not only edge generation.
          active? (supporter-filter-active? t)
          vis (cond
                ;; genlCx declarations are forced into CxUniverse and therefore
                ;; globally visible as declarations. Their *edges* can still be
                ;; excepted per reader, but assertion-context filtering must never
                ;; turn the whole context hierarchy off.
                (= rel-key :genlCx) nil

                active?
                (when (seq (:ctx-counts rel))
                  (let [up  (context-up tax context)
                        all (keys (:ctx-counts rel))
                        v   (into #{} (filter up) all)]
                    (when-not (= (count v) (count all)) v)))

                :else (visible-ctxs tax rel-key context))]
      (if active?
        {:contexts vis
         :context context
         :supporter-visible? (:supporter-visible? t)
         :visibility-gen (:supporter-visibility-gen t)}
        vis))))

(defn visible-ctxs
  "`up(K) ∩ ctxs` for relation `rel-key` — the supporting contexts `context` can
  see — or nil when the scoped answer could not differ from the global one.
  Interned per `[genlCx-gen ctxs-gen]`, so repeated reads from one context
  share one set object (O(1) hash for the memo level keyed on it) and the
  intersection runs once per context per taxonomy epoch, not once per call."
  [tax rel-key context]
  (when (scoped-context? context)
    (let [t    @tax
          rel  (get t rel-key)
          ctxs (:ctx-counts rel)]
      (when (seq ctxs)
        (let [stamp  [(:gen (:genlCx t)) (:ctxs-gen rel)]
              vidx   (:vis-index t)
              cached (get @vidx [rel-key context])]
          (if (= stamp (:stamp cached))
            (:vis cached)
            (let [up  (closure-of tax :genlCx :fwd context)
                  vis (into #{} (filter up) (keys ctxs))
                  ;; vis ⊆ ctxs, so equal counts mean equal sets: every asserting
                  ;; context is visible and the filter would keep every edge
                  vis (when-not (= (count vis) (count ctxs)) vis)]
              (swap! vidx assoc [rel-key context] {:stamp stamp :vis vis})
              vis)))))))

(defn- ctxs-visible?
  "Does the supporting-context set `cs` reach a reader whose visible set is `visq`
  (a set, or a predicate built from one)?  nil in `cs` is a supporter with no
  recorded context and constrains everywhere."
  [cs visq]
  (boolean (some (fn [c] (or (nil? c) (visq c))) cs)))

(def ^:dynamic *visible-neighbours-cache*
  "An optional atom holding a `{[dir-key vis n] neighbours}` map for a **read-only**
  pass (see `*closure-pass-cache*`).  The closure memo keys whole closures per
  `(node, vis)`, so a shared upper cone is re-filtered under every distinct root
  that walks through it — the cost the closure cache structurally cannot fold and
  the one this one does: each node's edges are context-filtered once per pass, not
  once per walk.  Bound and dropped by the pass, which holds the taxonomy still, so
  the filtered set is gen-stable for its span; nil off such a pass."
  nil)

(defn- visible-neighbours
  "The `dir-key` neighbours of `n` reachable through an edge some supporter makes
  effective in `scope` — the scoped walk's adjacency. Edge orientation: `:fwd` n→x is edge
  [n x], `:rev` n→x is edge [x n].  Filtered once per pass when a neighbour cache
  is bound (an empty result caches as `[]`, still truthy, so it is not re-walked).
  `rel-key` names the relation `rel` is: it keys the cache, since one pass scopes
  more than one relation (`:genl` and the `:genlCx` witness walk) and their filtered
  neighbours must not collide on a shared `[dir vis n]`."
  [rel-key rel dir-key scope n]
  (let [nc *visible-neighbours-cache*
        k  (when nc [rel-key dir-key scope n])]
    (or (when nc (get @nc k))
        (let [ectxs   (:edge-ctxs rel)
              support (:support rel)
              e-of    (if (= dir-key :fwd) (fn [x] [n x]) (fn [x] [x n]))
              pred    (if (map? scope)
                        (fn [x]
                          (some (fn [[h c]] (scope-admits-supporter? scope h c))
                                (get support (e-of x))))
                        (fn [x] (ctxs-visible? (get ectxs (e-of x)) scope)))
              nbrs  (get (dir-key rel) n)
              res   (if nc (filterv pred nbrs) (filter pred nbrs))]
          (when nc (swap! nc assoc k res))
          res))))

(def ^:dynamic *scoped-memo-budget*
  "How many distinct visibility sets the scoped closure memo holds per relation
  before the scoped level is flushed and repopulated by demand.  Sized by the
  OpenCyc census — 445 asserting contexts induce 561 distinct vissets across its
  13,196 readers — where an unbounded level on a quiescent KB served from many
  contexts would grow monotonically (a heap, not a wrong answer; only a `:gen`
  bump reclaims it).  A flush costs what an ordinary edit's gen bump costs; a
  working set under the budget never flushes at all."
  128)

(defn- closure-of-vis
  "`closure-of` over only the edges effective in `scope` — memoized one level deeper,
  under the interned scope key, in the same gen-stamped memo entry (so an edge or
  context change retires scoped and unscoped reads together).  The scoped level is
  bounded by `*scoped-memo-budget*` distinct vissets; admitting one past the budget
  flushes the level rather than growing it."
  [tax rel-key dir-key node scope]
  (let [pc *closure-pass-cache*
        pk (when pc [rel-key dir-key node scope])]
    (or (when pc (get @pc pk))
        (let [t    @tax
              rel  (get t rel-key)
              gen  (:gen rel)
              memo (:closure-memo t)
              m    @memo
              cur  (when (= gen (get-in m [rel-key :gen])) (get m rel-key))
              s    (or (get-in cur [:scoped scope dir-key node])
                       (let [s (reach node #(visible-neighbours rel-key rel dir-key scope %))]
                         (swap! memo (fn [mm]
                                       (let [e (get mm rel-key)
                                             e (if (= gen (:gen e)) e {:gen gen :fwd {} :rev {}})
                                             e (if (and (not (contains? (:scoped e) scope))
                                                        (<= *scoped-memo-budget* (count (:scoped e))))
                                                 (assoc e :scoped {})
                                                 e)]
                                         (assoc mm rel-key (assoc-in e [:scoped scope dir-key node] s)))))
                         s))]
          (when pc (swap! pc assoc pk s))
          s))))

(defn- reachable-filtered?
  "`reachable?` over only the edges effective in `scope` — the sibling walk the scoped
  `genl?` runs.  The depth potential holds over the *global* edge set and the
  visible set is a subset of it, so both prunings stay sound with no per-context
  depths; and because the neighbour set is filtered before the direct-edge test, a
  direct but invisible edge cannot answer true while the transitive paths filter.

  `scc` is read for the same reason `reachable?` reads it, and used for **less**.  The
  potential ranks the condensation, not the graph, so a node on a path to `tgt` is
  either strictly above it or level with it *inside `tgt`'s own component*; pruning on
  `depth > depth[tgt]` alone rejects the second, which is a real path, and the scoped
  read would then deny what the scoped `genls` walking the same edges returns.  What it
  may **not** borrow is `reachable?`'s other half — answering true off a shared
  component.  Mutual reachability there is a fact about the *global* edge set, and the
  whole question here is which of those edges the reader can see, so a component is a
  reason to keep walking and never an answer."
  [src tgt rel-key rel scope depth scc]
  (let [nbrs #(visible-neighbours rel-key rel :fwd scope %)]
    (or (= src tgt)
        (if (nil? depth)
          (loop [seen #{src}, stack [src]]
            (if-let [n (peek stack)]
              (let [ns (nbrs n)]
                (if (some #(= tgt %) ns)
                  true
                  (let [fresh (into [] (remove seen) ns)]
                    (recur (into seen fresh) (into (pop stack) fresh)))))
              false))
          (let [dt    (get depth tgt)
                ctgt  (get scc tgt)
                ;; Could `x` still lie on a path to `tgt`?  Two spellings of one rule.
                ;; When `tgt` is in no component the level arm cannot fire at all — a
                ;; path into it comes from another component and so descends strictly —
                ;; so the bare comparison is not an approximation there, it is the whole
                ;; rule.  That is every node of an acyclic relation, which `genl` is in
                ;; any KB that has not defeated an edge to get around the check, and this
                ;; predicate runs per neighbour beneath a per-assert caller.  The cost of
                ;; carrying the component arm is then one `scc` lookup per call rather
                ;; than a second comparison per neighbour.
                over? (if (nil? ctgt)
                        (fn [x] (> (get depth x -1) dt))
                        (fn [x] (let [d (get depth x -1)]
                                  (or (> d dt) (and (= d dt) (= ctgt (get scc x)))))))]
            (and (some? dt)
                 (over? src)
                 (loop [seen #{src}, stack [src]]
                   (if-let [n (peek stack)]
                     (let [ns (nbrs n)]
                       (if (some #(= tgt %) ns)
                         true
                         (let [fresh (into [] (comp (remove seen) (filter over?)) ns)]
                           (recur (into seen fresh) (into (pop stack) fresh)))))
                     false))))))))

;; ---- supporter reference counting for the non-transitive caches ---------
;;
;; `genl` and `genlCx` carry their own `:support` map inside the relation (see
;; the ns docstring).  The other five caches — `disjoint`, the disjoint metatypes,
;; the predicate properties, `inverse`, and the declared arities — are flat sets and
;; maps with no such record, so they need reference counting of their own.
;;
;; Tearing one down unconditionally drifts, because none of those predicates is
;; *forced* universal: only `genlCx` is (core_context.clj), so only it is guaranteed
;; one sentex per claim.  `(disjoint dog cat)` asserted in two contexts is two
;; sentexes, both folding into one cache entry — so retracting either one must not
;; delete it while the other is still stored and believed, or the cache would say the
;; pair is not disjoint while the KB still asserts that it is, and a membership the KB
;; should refuse would start being accepted.
;;
;; So they get reference counting, in one shared map keyed by
;; `[kind key]`: the entry survives while any sentex still asserts it.  Belief rides
;; on top of that count exactly as it does for genl — an entry is active iff some
;; supporter is stored *and* believed (`refresh-cache-support`, below, reconciles it
;; after every relabel the way `refresh-relation` does the closures).  `cache-install`
;; / `cache-uninstall` are the *one* definition of what an active entry looks like,
;; shared by the assert-time `add-*` / `mark-*` functions and by that belief reconcile,
;; so the two paths can never drift.

;; `:cache-ctxs {[kind key] #{ctx}}` mirrors `:edge-ctxs` for the flat caches: the
;; supporting contexts of each entry, maintained by the writers from every supporter
;; and refined to the believed ones by `refresh-cache-support`.  No generation rides
;; on it — the flat caches are point lookups, never memoized closures.
;;
;; `:cache-handle-keys {handle #{[kind key]}}` is the **reverse** of `:cache-support`:
;; which entries each supporting sentex asserts.  It is the flat-cache twin of a
;; relation's `:handle-edge` and exists for the same reason — so `refresh-beliefs` can
;; read the entries a settle could have moved *off the moved region* rather than off the
;; cache.  Belief moves by handle, so only an entry some moved handle supports can have
;; changed which of its supporters are believed, and that lookup is the whole reconcile's
;; scope.  Read backward instead, both halves are O(vocabulary): the "did anything touch
;; me" gate walks every supporter, and the reconcile then evaluates belief for every
;; entry — 5.0 ms merely to decide nothing moved, and 95 ms per flip, over 32k
;; declarations, against a map that holds every disjoint pair, predicate property,
;; inverse and declared arity in the KB.
;;
;; A **multimap**, where `:handle-edge` is 1:1.  Every writer here keys the entry off the
;; asserting sentence, so today one handle names one `[kind key]` — but nothing in the
;; structure says so, and removal is per-(handle, key): a 1:1 index would have the first
;; `support-drop` take the handle out from under an entry the same sentex still supports,
;; which reads as a stale cache rather than as a crash.  A set per handle costs the
;; single-key case one small set and makes the index answer to `:cache-support`'s own
;; shape instead of to an invariant nothing states.
;;
;; `:cache-dirty` is the other half of the scope, and it exists because the writers are
;; **belief-blind** in exactly the way `add-edge` / `del-edge` are: `support-add` and
;; `support-drop` run on the assert/retract path with no `believed?` in hand, so they
;; recompute `:cache-ctxs` from every *recorded* supporter, and `supported-del` uninstalls
;; only when the last supporter is gone.  On an entry with a single supporter both are
;; exact.  On a **shared** entry they are not — a disbelieved co-supporter's context reads
;; as asserting, and losing the last *believed* supporter of an entry two sentexes still
;; assert is an uninstall only a `believed?` can make.  So a writer leaving a shared entry
;; behind names it here and the next reconcile takes it whether or not belief moved there.
;; A superset is the safe interim reading (a scoped read sees an entry it should not,
;; never misses one it should), and the set stays proportional to the edits: the
;; single-supporter entry that is nearly every entry, and all of a bulk load, never
;; enters it.

(defn- forget-handle-key
  "Drop `k` from `handle`'s reverse-index entry, and the handle itself once it supports
  nothing — an empty set left behind would make the handle read as a live supporter and
  keep it in the reconcile's scope for the life of the KB."
  [t handle k]
  (let [left (disj (get-in t [:cache-handle-keys handle] #{}) k)]
    (if (seq left)
      (assoc-in t [:cache-handle-keys handle] left)
      (update t :cache-handle-keys dissoc handle))))

(defn- support-add [t k handle ctx]
  (let [m (assoc (get-in t [:cache-support k] {}) handle ctx)]
    (-> t
        (assoc-in [:cache-support k] m)
        (assoc-in [:cache-ctxs k] (into #{} (vals m)))
        (update-in [:cache-handle-keys handle] (fnil conj #{}) k)
        ;; belief-blind above: with a co-supporter the context set may be a superset and
        ;; only a reconcile can narrow it.  Costs the common first-supporter write
        ;; nothing, which is what keeps a bulk load out of the set entirely.
        (cond-> (> (count m) 1) (update :cache-dirty conj k)))))

(defn- support-drop
  "Drop `handle`'s support for `k`.  Returns `[state last-supporter-gone?]`."
  [t k handle]
  (let [left (dissoc (get-in t [:cache-support k] {}) handle)]
    [(-> (if (seq left)
           (-> t
               (assoc-in [:cache-support k] left)
               (assoc-in [:cache-ctxs k] (into #{} (vals left)))
               ;; belief-blind again, and worse than the add: the survivors may include
               ;; one nothing believes, and the caller uninstalls only when the last
               ;; supporter is gone
               (update :cache-dirty conj k))
           (-> t
               (update :cache-support dissoc k)
               (update :cache-ctxs dissoc k)
               ;; the entry is gone outright, so it owes no reconcile — and reconciling
               ;; it would write an empty `:cache-ctxs` back under a key nothing supports
               (update :cache-dirty disj k)))
         (forget-handle-key handle k))
     (empty? left)]))

(defn- supported-add
  "Record `handle` as asserting `k` from `ctx`, and apply `f` to install the cache
  entry."
  [t k handle ctx f]
  (-> t (support-add k handle ctx) f))

(defn- supported-del
  "Drop `handle`'s support for `k`, applying `f` to remove the cache entry only when
  the last supporter is gone."
  [t k handle f]
  (let [[t' gone?] (support-drop t k handle)]
    (cond-> t' gone? f)))

(defn- inverse-key
  "The flat-cache key for an inverse declaration between `p` and `q`.

  `(hash-set p q)`, never the `#{p q}` literal: a self-inverse `(inverse P P)` is a
  legal declaration — it says `(P a b)` iff `(P b a)`, which is what `symmetric` says —
  and the literal is the checked `RT.set`, so it throws `Duplicate key` rather than
  folding to the one-element set the key wants."
  [p q]
  [:inverse (hash-set p q)])

(defn- declared-pair
  "The two terms a `[:inverse #{p q}]` or `[:disjoint #{x y}]` key names, as `[x y]`.  A
  self-pair — `(inverse P P)`, `(disjoint T T)` — collapses to `#{p}`, so `y` falls back
  to `x`: both directions of the index write then name the same pair, which is
  idempotent.  One extractor for both, because the key is a set in both."
  [s]
  (let [x (first s)] [x (or (second s) x)]))

(defn- index-symmetric
  "Add or drop both directions of a declared symmetric pair in the adjacency at `k`,
  `{term -> #{terms declared to stand in the relation to it}}`.  `:inverse` (predicates)
  and `:disjoint-index` (types) are the two, and this is the whole of what they share:
  the relation is symmetric, so it is written both ways; the entry is a *set*; and an
  emptied entry is dissoc'd rather than left behind, so `get` returning nil means what
  it says — `:arity`'s discipline.

  **A set per term, not one partner.**  Nothing refuses a second `(inverse P R)` beside
  a standing `(inverse P Q)`, so a single-valued entry would answer whichever was
  installed last — making the read a function of assertion order, and `inverses-of`
  decides which hops a transitive walk sees.  Order independence is not negotiable
  (README, \"The model in one page\"), so the relation is stored as the many-to-many it
  is and the readers pick from it by content.  It is also what makes the *drop*
  correct: retiring `(inverse P R)` while `(inverse P Q)` still holds must leave
  `P → #{Q}` rather than clearing `P`."
  [t k s add?]
  (let [[x y] (declared-pair s)
        one   (fn [t a b]
                (if add?
                  (update-in t [k a] (fnil conj #{}) b)
                  (let [left (disj (get-in t [k a] #{}) b)]
                    (if (empty? left)
                      (update t k dissoc a)
                      (assoc-in t [k a] left)))))]
    (-> t (one x y) (one y x))))

(defn- cache-install
  "Install the derived cache entry for support key `k` into taxonomy state `t`.  The
  single definition of what an *active* entry is, shared by the assert-time
  `add-*` / `mark-*` functions (via `supported-add`) and by the belief reconcile in
  `refresh-beliefs`.  Idempotent: installing an entry already present is a no-op."
  [t [kind a b]]
  (case kind
    ;; `:disjoint` holds the relation as a set of unordered pairs and `:disjoint-index`
    ;; the same relation as adjacency, because `disjoint?` reads the second: the pair set
    ;; can only be consulted by building a `#{x y}` per candidate, so a walk over two genl
    ;; closures allocates a two-element hash set |as|·|bs| times to ask what is one map
    ;; lookup per supertype here.  Most types are declared disjoint from nothing at all,
    ;; so the outer walk short-circuits on a nil and never touches the inner closure.
    :disjoint (-> t (update :disjoint conj a)                      ; a = #{x y}
                  (index-symmetric :disjoint-index a true))
    :metatype (update t :disjoint-metatypes conj a)                ; a = m
    :member   (update-in t [:metatype-members a] (fnil conj #{}) b)  ; a = m, b = type
    :prop     (update-in t [:props a] (fnil conj #{}) b)             ; a = prop-kind, b = pred
    :inverse  (index-symmetric t :inverse a true)                  ; a = #{p q}
    :arity    (update-in t [:arity a] (fnil conj #{}) b)))                        ; a = pred, b = n

(defn- cache-uninstall
  "Remove the derived cache entry for support key `k` — the exact inverse of
  `cache-install`.  This is the **belief** removal: plain and reversible, so a
  defeated declaration drops out and a revived one returns.  Retracting the *last*
  supporter of a metatype does more (its members and their support go too — see
  `forget-metatype`), but that is teardown of the mark itself, not what belief toggles.
  Idempotent."
  [t [kind a b]]
  (case kind
    :disjoint (-> t (update :disjoint disj a)
                  (index-symmetric :disjoint-index a false))
    :metatype (update t :disjoint-metatypes disj a)
    :member   (update-in t [:metatype-members a] (fnil disj #{}) b)
    :prop     (update-in t [:props a] (fnil disj #{}) b)
    :inverse  (index-symmetric t :inverse a false)
    :arity    (let [ns' (disj (get-in t [:arity a] #{}) b)]
                (if (seq ns') (assoc-in t [:arity a] ns') (update t :arity dissoc a)))))

;; ---- incremental adjacency maintenance ----------------------------------
;; Only the O(V+E) direct adjacency is stored; the closure is answered on demand
;; (`closure-of` above) and read-memoized per generation.  So an insert is O(1) plus a
;; depth repair whose size is the lift `raise-depth` forces — nothing at all for the
;; parent-before-child order, the node's descendants for the child-first one, which is
;; what `*defer-depths?*` trades away — and a delete is O(1) plus a node re-scan.
;; Neither pays to materialize the closure, which is what makes a deep or bulk load
;; sub-quadratic.  Every mutation bumps `:gen`, retiring the read memo.

(defn- bump-gen [rel] (update rel :gen inc))

(defn- ensure-depth
  "Give `n` a depth if it has none.  A fresh node starts at 0; the invariant
  `edge x→y ⇒ depth[x] > depth[y]` is restored by `raise-depth` on insert."
  [rel n]
  (cond-> rel (not (contains? (:depth rel) n)) (assoc-in [:depth n] 0)))

(defn- component-members
  "The inverse of `:scc`: representative → that component's members.  Read off the
  component map alone, which holds an entry only for a node in a **non-trivial**
  component — so an acyclic relation's is `{}` and this costs a `reduce-kv` over
  nothing."
  [scc]
  (reduce-kv (fn [m n r] (update m r (fnil conj #{}) n)) {} scc))

(defn- lift-components
  "Raise components until every `[node depth]` seed holds — the node's whole component
  sitting at least that deep — pushing each raise up through `:rev`, since a component
  with an edge into a raised one has to stay strictly above it.  A component is
  re-enqueued whenever a deeper one lifts it, so a diamond is handled correctly.

  It moves whole **components** because the potential is one over the condensation:
  depth is equal inside a component and strict between two, so a member raised alone
  would break the equality its component's depth is defined by — and, in a cyclic
  relation, would then raise its own mates forever, each lift forcing the next around
  the cycle.  Termination is the condensation being a DAG: every step raises a
  component strictly and climbs an edge of that DAG, so no component can force itself.
  (Depths are never *capped* — a cap keyed on the node count is unsound once deletion
  has left depths loose, since a legitimate lift can then legitimately exceed it.)"
  [rel scc members-of seeds]
  (loop [rel rel, stack (vec seeds)]
    (if-let [[y dy] (peek stack)]
      (let [stack (pop stack)
            dy    (long dy)]
        (if (>= (long (get-in rel [:depth y] 0)) dy)
          (recur rel stack)
          (let [mem (if-let [r (get scc y)] (get members-of r) #{y})
                rel (reduce (fn [r m] (assoc-in r [:depth m] dy)) rel mem)
                up  (into [] (comp (mapcat #(get-in rel [:rev %]))
                                   (remove mem)
                                   (map (fn [u] [u (inc dy)])))
                          mem)]
            (recur rel (into stack up)))))
      rel)))

(defn- raise-depth
  "Restore `edge x→y ⇒ depth[x] > depth[y]` after adding edge a→b: lift `a` above `b`
  if it is not already, and push that lift up through `:rev` as far as it forces
  anything.  `lift-components` is the walk, so the lift moves `a`'s whole component
  when `a` sits in one."
  [rel a b]
  (if (> (long (get-in rel [:depth a])) (long (get-in rel [:depth b])))
    rel
    (let [scc (:scc rel)]
      (lift-components rel scc (component-members scc)
                       [[a (inc (long (get-in rel [:depth b])))]]))))

(def ^:dynamic *defer-depths?*
  "When true, an edge insert skips `raise-depth` and lifts only the edge's own source
  (`local-lift`), going `:loose?` if that breaks an edge above it; `restore-depths`
  rebuilds every depth in one pass when the batch settles.

  `raise-depth` is proportional to the *descendants* of the node it lifts, which is
  the one thing an insert is not supposed to be: adding a hundred thousand edges in an
  order that repeatedly lifts high nodes re-walks their subtrees over and over, so a
  bulk load arriving child-first is quadratic in the hierarchy.  Deferring makes the
  insert O(1) plus the source's in-degree, and pays one O(V+E) repair per batch.

  Going loose is **not** free, which is why `local-lift` exists rather than a blanket
  `:loose?`: while loose `reachable?` drops its pruning, and `wff` runs one such walk
  per taxonomy edge asserted.  Trading the eager repair for a blanket loose potential
  would only swap which arrival order is quadratic — child-first would get cheap and
  parent-first, the *natural* order for a hierarchy, would get expensive.  The local
  lift keeps the potential sound for exactly the orders `raise-depth` was already cheap
  on, so neither order pays.

  Bound by `vaelii.core/with-deferred-settle`, whose settle does the repair — the same
  bargain that scope already makes for belief."
  false)

(defn- local-lift
  "Restore `depth[a] > depth[b]` for the newly-inserted edge a→b **alone**: lift `a`
  just above `b` and check only the edges *into* `a`, never its descendants.

  That is the whole difference from `raise-depth`, which pushes the lift down through
  `:rev` until it stops forcing anything.  Raising `depth[a]` can never break an edge
  `a→x` (the source only moved up), so the only edges at risk are `u→a` for `u` in
  `:rev a` — an in-degree scan, not a descendant walk.  If none is broken the global
  invariant still holds and the potential stays sound, so reads keep their pruning; if
  one is, the relation goes `:loose?` and `restore-depths` owns the repair.

  Edges arriving **parent-before-child** — a hierarchy's natural load order, and the
  order `reachable?`'s pruning is written for — never break one: the child is a fresh
  node, nothing points at it yet.  So the common bulk load keeps an O(1) insert *and*
  an O(1) pruned read, which a blanket `:loose?` would have cost it."
  [rel a b]
  (let [da (get-in rel [:depth a])
        db (get-in rel [:depth b])]
    (if (> da db)
      rel                                          ; already satisfied — nothing moved
      (let [da' (inc db)
            rel (assoc-in rel [:depth a] da')]
        (if (some (fn [u] (<= (get-in rel [:depth u] 0) da')) (get-in rel [:rev a]))
          (assoc rel :loose? true)
          rel)))))

(defn- activate
  "Bring [a b] into the active edge set: record the direct adjacency, the node set,
  and repair the depth potential.  A no-op when the edge is already active, so a
  redundant re-assert costs nothing and leaves the read memo valid.

  `wff` (assert path) and `special/wff-violation` (derivation path) both refuse an
  edge that would close a cycle before it reaches here, so the acyclic branch is the
  only one that runs in practice.  The `reachable?` guard is defensive-in-depth: it is
  O(1) in the common case (`a` is a fresh or shallower node, rejected outright) and, on
  the wff-forbidden cyclic edge, records the adjacency — keeping `genls` / `specs`
  (which walk `reach`, cycle-safe) correct — while skipping `raise-depth`, whose
  termination assumes acyclicity.

  Under `*defer-depths?*` the repair is `local-lift` instead — the edge's own source,
  not its descendants.

  An **already-loose** relation short-circuits both, whether or not this insert is
  deferred: with no sound potential the guard would have to walk unpruned (the cost
  the deferral exists to avoid) and `raise-depth` would build on a stale base, so the
  adjacency is recorded and `restore-depths` is left to own the repair.  Reading
  `:loose?` rather than the dynamic var alone is what keeps that true for an insert
  arriving *after* a batch aborted — the settle that would have repaired never ran.
  What refuses a cycle throughout is `wff`, which reads through `reachable-in?` and
  stays correct while loose."
  [rel a b]
  (if (contains? (:edges rel) [a b])
    rel                                            ; already active — nothing to do
    (let [loose?  (boolean (:loose? rel))
          cyclic? (and (not loose?)
                       (reachable? b a (:fwd rel) (:depth rel) (:scc rel)))
          rel     (-> rel
                      (ensure-depth a) (ensure-depth b)
                      (update-in [:fwd a] (fnil conj #{}) b)
                      (update-in [:rev b] (fnil conj #{}) a)
                      (update :nodes conj a b)
                      (update :edges conj [a b]))]
      (bump-gen (cond
                  loose?           rel
                  ;; the edge closes a cycle: it merges two components, which is a
                  ;; question about the whole graph rather than about this edge, so
                  ;; the potential is surrendered and `restore-depths` owns the repair
                  cyclic?          (assoc rel :loose? true)
                  *defer-depths?*  (local-lift rel a b)
                  :else            (raise-depth rel a b))))))

(defn- strong-components
  "The strongly connected components of `nodes` under adjacency `fwd`, as a map
  node → representative — **only** for the nodes in a component of more than one, so
  an acyclic relation gets `{}` and every read past this point pays a nil lookup.

  Tarjan's algorithm, iterated over an explicit work stack rather than recursed: the
  recursion depth is the graph's depth, and a context lattice is thousands deep.  The
  representative is `term-min` of the component, so which name stands for a component
  is a function of its content and not of the order its edges arrived."
  [nodes fwd]
  (let [idx   (java.util.HashMap.)              ; node → discovery index
        low   (java.util.HashMap.)
        on    (java.util.HashSet.)              ; nodes currently on the Tarjan stack
        stk   (java.util.ArrayDeque.)
        out   (volatile! {})
        n     (volatile! 0)]
    (doseq [root nodes :when (not (.containsKey idx root))]
      ;; each frame is [node remaining-neighbours]; a frame is pushed on descent and
      ;; popped once its neighbours are exhausted, which is where the low-link folds up
      (let [work (java.util.ArrayDeque.)
            visit (fn [v]
                    (.put idx v @n) (.put low v @n) (vswap! n inc)
                    (.push stk v) (.add on v)
                    (.push work (object-array [v (seq (get fwd v))])))]
        (visit root)
        (while (not (.isEmpty work))
          (let [^objects frame (.peek work)
                v              (aget frame 0)
                remaining      (aget frame 1)]
            (if-let [w (first remaining)]
              (do (aset frame 1 (next remaining))
                  (cond
                    (not (.containsKey idx w)) (visit w)
                    (.contains on w)           (.put low v (min (long (.get low v))
                                                                (long (.get idx w))))))
              (do (.pop work)
                  (when (= (.get low v) (.get idx v))
                    ;; v roots a component: everything above it on the stack is in it
                    (let [members (loop [acc []]
                                    (let [w (.pop stk)]
                                      (.remove on w)
                                      (if (= w v) (conj acc w) (recur (conj acc w)))))]
                      (when (> (count members) 1)
                        (let [rep (term-min members)]
                          (vswap! out into (map (fn [m] [m rep])) members)))))
                  (when-let [^objects parent (.peek work)]
                    (let [p (aget parent 0)]
                      (.put low p (min (long (.get low p)) (long (.get low v))))))))))))
    @out))

(defn- repair-depths
  "Recompute every depth of `rel` in one pass, restoring the potential `edge x→y ⇒
  depth[x] ≥ depth[y]`, strict between components and equal inside one.

  The pass runs over the **condensation**: `components` first, then components are
  settled in reverse topological order — one is ready once every component it points
  at is — and each takes `1 + max` of what it points at, so the potential is the
  component's height above the sinks.  A node's depth is its component's.  O(V+E),
  against the O(descendants) *per edge* that repairing on insert costs.

  Condensing is what makes the pass total.  Walking the raw graph, a node on a cycle
  is never ready and would keep a stale depth — sound only for a graph that has none,
  which `genlCx` no longer is (a `genlMt` cycle is a claim OpenCyc makes 49 times,
  and it means the contexts see each other)."
  [rel]
  (let [nodes (:nodes rel)
        fwd   (:fwd rel)
        scc   (strong-components nodes fwd)
        ;; the condensation: a component keyed by its representative, a lone node by
        ;; itself.  Self-loops within a component are dropped — a component points at
        ;; itself by construction and would never be ready.
        cof   (fn [x] (get scc x x))
        cnodes (into #{} (map cof) nodes)
        cfwd  (reduce (fn [m x]
                        (let [cx (cof x)
                              ys (into #{} (comp (filter nodes) (map cof) (remove #{cx}))
                                       (get fwd x))]
                          (if (seq ys) (update m cx (fnil into #{}) ys) m)))
                      {} nodes)
        crev  (reduce (fn [m [x ys]] (reduce (fn [m2 y] (update m2 y (fnil conj #{}) x)) m ys))
                      {} cfwd)
        pending (into {} (map (fn [x] [x (count (get cfwd x))])) cnodes)]
    (loop [cdepth  (transient {})
           pending pending
           ready   (into [] (comp (filter #(zero? (long (pending %))))) cnodes)]
      (if-let [x (peek ready)]
        (let [ready (pop ready)
              dx    (reduce (fn [d y] (max d (inc (long (get cdepth y 0)))))
                            0 (get cfwd x))
              cdepth (assoc! cdepth x dx)
              ;; every component pointing at x may now be ready
              [pending ready]
              (reduce (fn [[p r] u]
                        (let [n (dec (long (get p u 1)))]
                          [(assoc p u n) (if (zero? n) (conj r u) r)]))
                      [pending ready]
                      (get crev x))]
          (recur cdepth pending ready))
        (let [cdepth  (persistent! cdepth)
              settled (into {} (keep (fn [x] (when-let [d (get cdepth (cof x))] [x d]))) nodes)]
          (-> rel
              (assoc :depth (merge (select-keys (:depth rel) (remove settled nodes)) settled))
              (assoc :scc scc)
              (dissoc :loose?)))))))

(defn restore-depths
  "Repair the depth potential of every relation a deferred batch left `:loose?`.
  Idempotent, and free when no relation is loose — which includes the common deferred
  batch, whose `local-lift` kept the potential sound throughout — so `settle` can call
  it unconditionally, and so can a caller unwinding from an aborted batch."
  [tax]
  (swap! tax (fn [t]
               (reduce (fn [t k]
                         (if (get-in t [k :loose?])
                           (update t k (comp bump-gen repair-depths))
                           t))
                       t
                       [:genl :genlCx])))
  tax)

(defn- prune-node
  "Drop `n` from `:nodes` / `:depth` / `:scc` if no active edge touches it any more."
  [rel n]
  (if (or (seq (get-in rel [:fwd n])) (seq (get-in rel [:rev n])))
    rel
    (-> rel (update :nodes disj n) (update :depth dissoc n) (update :scc dissoc n))))

(defn- split-depths
  "Depths for the members of a component that has just split, given `sub` — the
  components of its own induced subgraph.  `{node depth}` over `members`.

  Each new sub-component sits one above the highest thing it points at, whether that is
  another sub-component or a node outside the old component entirely; sinks are settled
  first, so each is settled once.  Tight rather than merely sound, which is what keeps
  the answer from drifting upward every time a component splits: the sub-component
  holding the old component's deepest external edge keeps the depth the whole component
  had, and only a chain **above** it rises at all."
  [rel members sub]
  (let [fwd    (:fwd rel)
        depth  (:depth rel)
        cof    #(get sub % %)
        cnodes (into #{} (map cof) members)
        ;; the sub-condensation, and per sub-component the highest depth it points at
        ;; outside the old component — the floor its own depth has to clear
        [cfwd floor]
        (reduce (fn [acc x]
                  (let [cx (cof x)]
                    (reduce (fn [[cf fl] y]
                              (if (contains? members y)
                                (let [cy (cof y)]
                                  (if (= cx cy) [cf fl] [(update cf cx (fnil conj #{}) cy) fl]))
                                [cf (update fl cx (fnil max 0) (inc (long (get depth y 0))))]))
                            acc (get fwd x))))
                [{} {}] members)
        crev    (reduce-kv (fn [m x ys]
                             (reduce (fn [m2 y] (update m2 y (fnil conj #{}) x)) m ys))
                           {} cfwd)
        pending (into {} (map (fn [x] [x (count (get cfwd x))])) cnodes)]
    (loop [cd      (transient {})
           pending pending
           ready   (into [] (filter #(zero? (long (pending %)))) cnodes)]
      (if-let [x (peek ready)]
        (let [ready (pop ready)
              dx    (reduce (fn [d y] (max d (inc (long (get cd y 0)))))
                            (long (get floor x 0)) (get cfwd x))
              cd    (assoc! cd x dx)
              [pending ready]
              (reduce (fn [[p r] u]
                        (let [n (dec (long (get p u 1)))]
                          [(assoc p u n) (if (zero? n) (conj r u) r)]))
                      [pending ready] (get crev x))]
          (recur cd pending ready))
        (let [cd (persistent! cd)]
          (into {} (map (fn [x] [x (long (get cd (cof x) 0))])) members))))))

(defn- repair-component
  "Repair the component a removed edge sat inside, and the depths its split invalidates.
  A stale `:scc` entry is the one thing in this relation that would answer *true* for a
  pair no longer connected, so it is never left standing.

  **Only an edge whose two endpoints share a component can change one.** A component's
  strong connectivity is a property of its own induced subgraph, and an edge with an
  endpoint outside — or with none in a component at all — is not in that subgraph. So
  every other deletion, which is every deletion in an acyclic relation and most of them
  in a cyclic one, is left alone here: nothing to recompute, and the potential stays
  sound, since removing an edge only relaxes the ordering it has to satisfy.

  When they do share one, the component's own induced subgraph is re-run through
  `strong-components` — the new components of the whole graph refine the old ones, so
  what a split produces is contained in the component that split, and the answer is
  proportional to it rather than to the relation. A component that survives the deletion
  intact leaves everything as it was. A split takes new depths from `split-depths`, and
  a sub-component whose new depth is higher than the one it is replacing pushes that
  rise up through `lift-components`.

  The relation therefore does **not** go `:loose?`, and reads keep their pruning
  through a deletion that would otherwise have cost a whole-relation `repair-depths`.
  The one case that does surrender is a relation **already** loose: there is no sound
  potential to repair against, so the component is dropped whole and the batch's own
  `restore-depths` rebuilds it.  Dropping is not optional there — a loose relation
  still reads `:scc` for the \"same component ⇒ mutually reachable\" answer, which is
  the one thing an unpruned walk cannot correct."
  [rel a b]
  (let [scc (:scc rel)
        rep (get scc a)]
    (cond
      (or (nil? rep) (not= rep (get scc b))) rel
      (:loose? rel) (assoc rel :scc (into {} (remove (fn [[_ r]] (= r rep))) scc))
      :else
      (let [members-of (component-members scc)
            members    (get members-of rep)
            fwd        (:fwd rel)
            sub-fwd    (into {} (map (fn [x] [x (into #{} (filter members) (get fwd x))])) members)
            sub        (strong-components members sub-fwd)]
        (if (= 1 (count (into #{} (map #(get sub % %)) members)))
          rel                                          ; still one component — nothing moved
          (let [depths (split-depths rel members sub)
                scc'   (merge (apply dissoc scc members) sub)
                cof    #(get scc' % %)
                risen  (filterv #(> (long (depths %)) (long (get-in rel [:depth %] 0))) members)
                rel    (-> rel (assoc :scc scc') (update :depth merge depths))
                seeds  (into [] (mapcat (fn [x]
                                          (let [d (inc (long (depths x)))]
                                            (keep (fn [u] (when (not= (cof u) (cof x)) [u d]))
                                                  (get-in rel [:rev x])))))
                             risen)]
            (lift-components rel scc' (component-members scc') seeds)))))))

(defn- deactivate
  "Drop [a b] from the active edge set.  Depths are left as loose upper bounds — a
  deletion only relaxes the ordering, so the invariant survives — and a node left
  with no edge is pruned so `types` / `contexts` match a from-scratch build.  A
  component the edge sat inside is recomputed rather than trusted (see
  `repair-component`)."
  [rel a b]
  (if-not (contains? (:edges rel) [a b])
    rel
    (let [drop-adj (fn [rel k x y]
                     (let [s (disj (get-in rel [k x]) y)]
                       (if (seq s) (assoc-in rel [k x] s) (update rel k dissoc x))))]
      (-> rel
          (update :edges disj [a b])
          (drop-adj :fwd a b)
          (drop-adj :rev b a)
          (repair-component a b)
          (prune-node a) (prune-node b)
          bump-gen))))

(defn- ctx-count-inc
  "Count one more supporter asserting from `ctx`; a context appearing for the first
  time bumps `:ctxs-gen`.  nil (no recorded context) is not counted — it is not a
  context a visibility cone could name."
  [rel ctx]
  (if (nil? ctx)
    rel
    (let [n (long (get-in rel [:ctx-counts ctx] 0))]
      (cond-> (assoc-in rel [:ctx-counts ctx] (inc n))
        (zero? n) (update :ctxs-gen inc)))))

(defn- ctx-count-dec
  "One supporter asserting from `ctx` is gone; a context leaving entirely bumps
  `:ctxs-gen`."
  [rel ctx]
  (if (nil? ctx)
    rel
    (let [n (long (get-in rel [:ctx-counts ctx] 0))]
      (cond
        (zero? n) rel
        (= 1 n)   (-> rel (update :ctx-counts dissoc ctx) (update :ctxs-gen inc))
        :else     (assoc-in rel [:ctx-counts ctx] (dec n))))))

(defn- set-edge-ctxs
  "Record `ctxs` as active edge `e`'s supporting contexts, bumping `:gen` iff the set
  moved — a scoped read's answer is a function of these, so a context-only move must
  retire the read memo even though the edge set did not change."
  [rel e ctxs]
  (if (= ctxs (get-in rel [:edge-ctxs e]))
    rel
    (-> rel (assoc-in [:edge-ctxs e] ctxs) bump-gen)))

(defn- mark-dirty
  "Note that `e`'s `:edge-ctxs` was recomputed belief-blind and owes a reconcile.  Only
  a **shared** edge does: with one supporter the writers' reading is already the believed
  one, either because the supporter is believed or because nothing else claims the edge.
  Costs the common single-supporter write nothing, which is what keeps a bulk load out of
  the set entirely."
  [rel e shared?]
  (cond-> rel shared? (update :dirty conj e)))

(defn- add-edge
  "Record `handle` as asserting [a b] from `ctx`, and activate the edge."
  [rel a b handle ctx]
  (let [support (assoc (get-in rel [:support [a b]] {}) handle ctx)]
    (-> rel
        (assoc-in [:support [a b]] support)
        (assoc-in [:handle-edge handle] [a b])
        (ctx-count-inc ctx)
        (activate a b)
        (set-edge-ctxs [a b] (into #{} (vals support)))
        (mark-dirty [a b] (> (count support) 1)))))

(defn- del-edge
  "Drop `handle`'s support for [a b].  The edge survives while any other sentex
  still asserts it."
  [rel a b handle]
  (let [support (get-in rel [:support [a b]] {})]
    (if-not (contains? support handle)
      rel
      (let [left (dissoc support handle)
            rel  (-> (if (seq left)
                       (assoc-in rel [:support [a b]] left)
                       (update rel :support dissoc [a b]))
                     (update :handle-edge dissoc handle)
                     (ctx-count-dec (get support handle)))]
        (if (seq left)
          ;; retarget only an *active* edge: a refresh may have deactivated this one
          ;; with its (disbelieved) supporters still recorded, and `:edge-ctxs` keys
          ;; exactly the active set.  Belief-blind either way, so the edge owes a
          ;; reconcile: the survivors may include one nothing believes, and losing the
          ;; last *believed* supporter of a still-supported edge is a deactivation only
          ;; a `believed?` can see.
          (-> rel
              (cond-> (contains? (:edges rel) [a b])
                (set-edge-ctxs [a b] (into #{} (vals left))))
              (mark-dirty [a b] true))
          (-> rel (deactivate a b) (update :edge-ctxs dissoc [a b])
              (update :dirty disj [a b])))))))

(defn- moved-touches?
  "Should a cache be reconciled against belief?  Yes when `moved` is nil — the caller
  holds no region and wants an unconditional reconcile — or when one of the cache's
  supporters is in `moved`, the set of handles whose belief just flipped.  When no
  supporter moved, the cache's active set cannot have changed, so the scan is skipped.

  `supporters` is the cache's own record of them: a set of handles, or the map they key.
  Either answers `contains?` by handle and `count` in O(1), which is what lets the
  intersection test walk **whichever side is smaller** — the two are independently sized,
  and a settle relabelling a large region over a cache holding few entries is as ordinary
  a shape as the reverse.  Walking the cache unconditionally is what made deciding a
  32k-entry cache was untouched cost 5 ms, in a settle that had nothing to do there.

  A gate, so a hit still pays the whole scan.  That is the right trade only where the
  scan is small — the equality partition and the rewrite rules, which hold the KB's
  asserted term-identity claims rather than its vocabulary.  The two transitive relations
  and the flat caches are the vocabulary's own size, so they do not gate at all:
  `moved-edges` / `moved-cache-keys` read the affected entries straight off `moved`, and
  skipping falls out of finding none."
  [moved supporters]
  (or (nil? moved)
      (boolean
       (if (and (counted? moved) (< (count moved) (count supporters)))
         (some #(contains? supporters %) moved)
         (some #(contains? moved %) (if (map? supporters) (keys supporters) supporters))))))

(defn- believed-ctxs
  "The contexts of the believed supporters in map `hs` (`{handle ctx}`), nil kept —
  a believed supporter with no recorded context still constrains everywhere.  Empty
  when no supporter is believed, which is what deactivates the edge."
  [hs believed?]
  (reduce-kv (fn [s h c] (if (believed? h) (conj s c) s)) #{} hs))

(defn- moved-edges
  "The edges a supporter in `moved` asserts — the only ones whose believed-supporter set
  can have changed, and so the whole scope a reconcile owes.  `nil` means every edge with
  a supporter, which is what a caller holding no region gets: `refresh-beliefs`'s
  two-arity.  Every `settle` path names one.

  Read forward off `moved` through `:handle-edge`, never backward off the relation.  That
  is what makes the reconcile proportional to the region a settle relabelled rather than
  to the vocabulary — and it subsumes the gate, since a settle touching no supporter here
  yields no edges and the reconcile below returns untouched.  `moved` is a *superset* of
  the handles whose belief flipped (`jtms/touched`), so a handle in it that did not
  actually move costs one edge re-examined and never an answer.

  Plus `:dirty`, the edges a belief-blind writer left owing a reconcile.  Belief did not
  move there, so `moved` cannot name them and they would otherwise never be narrowed.

  Whichever side is **smaller** is the one walked, and that is not a micro-optimization:
  the two are independently sized, and a settle relabelling a large region over a
  taxonomy holding few edges is an ordinary shape rather than a corner (arbitrating a
  standing set of P/¬P dilemmas is one, and `perf`'s `negation-arbitration` measures it).
  Walking `moved` unconditionally makes that settle pay for a taxonomy it never touches —
  the very cost this reverse index exists to remove, moved to the other side.  Either arm
  answers identically; the cost is O(min) rather than O(either)."
  [rel moved]
  (if (nil? moved)
    (keys (:support rel))
    (let [he (:handle-edge rel)]
      (if (and (counted? moved) (<= (count moved) (count he)))
        (into (:dirty rel) (keep he) moved)
        ;; also the arm an empty relation takes, in O(1) — `he` is the map being reduced
        (reduce-kv (fn [s h e] (if (moved h) (conj s e) s)) (:dirty rel) he)))))

(defn- refresh-relation
  "Active edges are those with at least one *believed* supporter, carrying the
  believed supporters' contexts.  Applies the difference edge by edge rather than
  rebuilding, so a settle whose region names no edge returns the relation untouched.
  Where it names edges the pass is not free of belief: the `want` seed evaluates
  `believed-ctxs` over every named edge's supporters before any arm runs, so a settle
  that changed no belief still pays one belief test per supporter of every edge in its
  region and the three arms then find nothing to apply.

  Scoped to `moved-edges` — an edge no moved handle supports and no writer left dirty is
  provably unchanged, so belief is never evaluated for it and it cannot enter either
  difference.  That is the locality invariant for this cache: the reconcile costs what
  moved, not what is stored.  This is the pass that discharges `:dirty`, so it clears the
  set on the way in.

  Three arms, not two.  An edge can keep its liveness while its *contexts* move —
  supported from A by h1 and from B by h2, h2 defeated: the edge stays active and B
  must leave `:edge-ctxs`, or a scoped read from B would answer through a defeated
  supporter.  Liveness alone cannot see that case, so the still-active edges are
  retargeted explicitly (`set-edge-ctxs` bumps the gen only when a set actually
  moved, so the arm is free for the common belief-preserving settle).

  The arms run in that order — deactivate, activate, retarget — rather than edge by
  edge, and it is not presentation.  `activate` refuses to trust a potential across an
  edge that would close a cycle, so an activation reading a graph that still holds the
  edges this same pass is about to drop can surrender `:loose?` where the settled graph
  is acyclic.  Draining the deactivations first is what keeps the potential's fate a
  function of the settled edge set rather than of the order two arms happened to run in."
  [rel believed? moved]
  (let [touched (moved-edges rel moved)]
    (if (empty? touched)
      rel
      (let [rel (assoc rel :dirty #{})           ; this pass is what discharges them
            support (:support rel)
            want (reduce (fn [m e]
                           (let [cs (believed-ctxs (get support e) believed?)]
                             (if (seq cs) (assoc m e cs) m)))
                         {} touched)
            want-edges (into #{} (keys want))
            have (:edges rel)]
        (as-> rel r
          (reduce (fn [r [a b :as e]]
                    (-> r (deactivate a b) (update :edge-ctxs dissoc e)))
                  r (set/difference (into #{} (filter have) touched) want-edges))
          (reduce (fn [r [a b :as e]]
                    (-> r (activate a b) (set-edge-ctxs e (want e))))
                  r (set/difference want-edges have))
          (reduce (fn [r e] (set-edge-ctxs r e (want e)))
                  r (set/intersection want-edges have)))))))

;; The add writers take the asserting sentex's context; the one-shorter arity is for
;; a caller with none to record — a probe, or a test driving the closure math — and
;; stores nil, the constrains-everywhere reading.  Deletion is keyed by handle alone.
(defn add-genl
  ([tax sub super handle] (add-genl tax sub super handle nil))
  ([tax sub super handle ctx] (swap! tax update :genl add-edge sub super handle ctx) tax))
(defn del-genl! [tax sub super handle] (swap! tax update :genl del-edge sub super handle) tax)
(defn add-genlCx
  ([tax sub super handle] (add-genlCx tax sub super handle nil))
  ([tax sub super handle ctx] (swap! tax update :genlCx add-edge sub super handle ctx) tax))
(defn del-genlCx! [tax sub super handle] (swap! tax update :genlCx del-edge sub super handle) tax)

;; ---- equality: rewriteOf / sameAs / equals, one partition ----------------
;;
;; `genl` is a partial order, so it caches up/down closures.  Equality is an
;; **equivalence**, and copying that shape would store every class as a complete
;; graph — quadratic, and it still would not answer "who represents this class?",
;; which is the only question the rewrite path actually asks.  So this is a
;; **partition**: member → class, class → members and representative.
;;
;; All three assertable relations feed it.  They differ in what they say *about* the
;; members, not in the classes they produce, and the whole of that difference rides
;; in one argument: `preferred` names the term a `rewriteOf` puts on top, and is nil
;; for `sameAs` / `equals`.  The edge itself is therefore undirected while the
;; preference belongs to the *supporter* that made the claim — which is what lets a
;; `(sameAs A B)` and a `(rewriteOf B A)` support one edge while only the second
;; deprecates anything, and lets belief withdraw the preference without withdrawing
;; the merge.
;;
;; Support is belief-following exactly as it is for genl.  `:out` is the disbelieved
;; supporter set; `refresh-beliefs` recomputes it wholesale from the current support
;; keys, so it cannot accumulate handles whose sentex has since gone.
;;
;; Insertion is a union, and it costs the **joined class** rather than a pointer:
;; `install-class` re-keys every member and `class-rep` scans each member's incident
;; edges for the preference claims on them, so merging a term into a class of n costs n
;; and n asserts growing one class to n cost Θ(n²) between them.  That is the price of
;; storing the representative rather than deriving it per read, and the bound is the
;; class rather than the relation.  **Deletion can split a class**, which union-find
;; cannot undo, so it rebuilds the affected class from its surviving believed edges —
;; the same bound, the same shape as the cone-local `genl` deletion, never the whole
;; relation.

(defn- pair
  "The canonical undirected edge key for `a` and `b`.  Equality is symmetric, so
  `(sameAs A B)` and `(sameAs B A)` must land on one edge."
  [a b]
  (if (neg? (compare (term-key a) (term-key b))) [a b] [b a]))

(defn- pref-pair
  "The directed [preferred dispreferred] claim that naming `p` makes about edge
  [x y].  nil when `p` is nil (a `sameAs` / `equals` supporter names no preference)."
  [[x y] p]
  (cond (= p x) [x y]
        (= p y) [y x]))

(defn- idx-conj [idx k v] (update idx k (fnil conj #{}) v))
(defn- idx-disj [idx k v]
  (let [s (disj (get idx k #{}) v)]
    (if (seq s) (assoc idx k s) (dissoc idx k))))

(defn- class-members
  "The class `t` belongs to, or `#{t}` when nothing has merged it."
  [rel t]
  (if-let [r (get (:class rel) t)] (get (:members rel) r #{t}) #{t}))

(defn- class-rep
  "The representative of a class, from its members and the preference claims carried
  by the active edges inside it.

  1. A term some `rewriteOf` names preferred wins, and **chains compose**: the heads
     are the preferred terms that nothing else deprecates, so `rewriteOf A B` plus
     `rewriteOf B C` leaves only `A` and it represents all three.
  2. A tie among heads — and a class with no `rewriteOf` at all — falls back to the
     lexicographically smallest term.  Arbitrary, but content-keyed and stable, the
     same discipline as `solve/content-key`: one class yields one representative no
     matter what order its edges arrived in.

  A `rewriteOf` cycle deprecates every preferred term and so has no head.  `wff`
  rejects it like a `genl` cycle; the second fallback is here so this stays total
  rather than returning nil if it ever becomes reachable."
  [rel members]
  (let [ps        (into #{}
                        (mapcat (fn [m] (mapcat #(get (:edge-prefs rel) % #{})
                                                (get (:edge-idx rel) m #{}))))
                        members)
        preferred (into #{} (map first) ps)
        heads     (set/difference preferred (into #{} (map second) ps))]
    (term-min (cond (seq heads) heads (seq preferred) preferred :else members))))

(defn- install-class
  "Install `members` as one class under its freshly-computed representative, dropping
  whatever classes those members used to key under."
  [rel members]
  (let [rep (class-rep rel members)]
    (-> rel
        (update :members #(apply dissoc % (keep (:class rel) members)))
        (assoc-in [:members rep] members)
        (update :class into (map (fn [t] [t rep])) members))))

(defn- components
  "The connected components the active edges induce on `terms`.  A term left with no
  active edge gets no component at all, so the key set matches what a from-scratch
  build produces — an unmerged term represents itself and is not stored."
  [rel terms]
  (let [nbrs (fn [t] (into #{} (mapcat identity) (get (:edge-idx rel) t #{})))]
    (loop [todo (into #{} (filter #(seq (get (:edge-idx rel) % #{}))) terms), acc []]
      (if-let [n (first todo)]
        (let [c (reach n nbrs)]
          (recur (set/difference todo c) (conj acc c)))
        acc))))

(defn- set-edge
  "Make edge `e` active carrying preference claims `ps`, unioning the two classes it
  joins.  Also the path a *second* supporter takes when it adds a preference to an
  edge that was already active: the partition does not move, the representative may."
  [rel [a b :as e] ps]
  (let [rel (-> rel
                (update :edges conj e)
                (update :edge-idx idx-conj a e)
                (update :edge-idx idx-conj b e)
                (update :edge-prefs #(if (seq ps) (assoc % e ps) (dissoc % e))))]
    (install-class rel (into (class-members rel a) (class-members rel b)))))

(defn- unset-edge
  "Deactivate edge `e`.  This is the half union-find cannot do: dropping an edge can
  **split** the class in two, so the class is torn down and rebuilt from the edges
  that survive it.  The work is bounded by the class, not by the relation."
  [rel [a b :as e]]
  (if-not (contains? (:edges rel) e)
    rel
    (let [members  (class-members rel a)               ; == (class-members rel b)
          old-reps (keep (:class rel) members)
          rel      (-> rel
                       (update :edges disj e)
                       (update :edge-idx idx-disj a e)
                       (update :edge-idx idx-disj b e)
                       (update :edge-prefs dissoc e)
                       ;; forget the class wholesale, then re-install whatever the
                       ;; surviving edges still hold together — one component if the
                       ;; edge was redundant, two if it was the only bridge, none at
                       ;; all if both ends are now isolated
                       (update :members #(apply dissoc % old-reps))
                       (update :class #(apply dissoc % members)))]
      (reduce install-class rel (components rel members)))))

(defn- edge-state
  "The preference claims believed supporters make about `e`, or nil when no believed
  sentex asserts the edge at all."
  [rel e]
  (let [live (into {} (remove (fn [[h _]] (contains? (:out rel) h)))
                   (get (:support rel) e))]
    (when (seq live)
      (into #{} (keep (fn [[_ p]] (pref-pair e p))) live))))

(defn- apply-edge
  "Reconcile one edge with what its believed supporters now say.  An edge whose state
  did not move costs nothing — the common case for a settle that defeated nothing."
  [rel e]
  (let [want (edge-state rel e)
        have (when (contains? (:edges rel) e) (get (:edge-prefs rel) e #{}))]
    (cond (= want have) rel
          (nil? want)   (unset-edge rel e)
          :else         (set-edge rel e want))))

(defn- refresh-equality
  "Reconcile the equality partition with belief, scoped to what `moved` names: only a
  moved supporter can change its believed status or its own edge's state, so the
  reconcile updates `:out` for `moved ∩ handles` and re-applies exactly those edges —
  the `moved-edges` discipline the transitive relations hold, `:handle-edge` being the
  same reverse map, walked from whichever side is smaller.  Unscoped, the i-th merge
  of a load re-asked belief of every supporter and re-derived the live state of every
  edge, Θ(N²) across the load.  nil `moved` is the unconditional reconcile
  (`refresh-beliefs`' two-arity): every supporter re-asked, every edge re-applied."
  [rel believed? moved]
  (if-not (moved-touches? moved (:handles rel))
    rel
    (if (nil? moved)
      (let [handles (into #{} (mapcat keys) (vals (:support rel)))
            rel     (assoc rel :out (into #{} (remove believed?) handles))]
        (reduce apply-edge rel (keys (:support rel))))
      (let [he       (:handle-edge rel)
            affected (if (and (counted? moved) (<= (count moved) (count he)))
                       (filterv #(contains? he %) moved)
                       (filterv #(contains? moved %) (keys he)))
            rel      (reduce (fn [r h]
                               (if (believed? h)
                                 (update r :out disj h)
                                 (update r :out conj h)))
                             rel affected)]
        (reduce apply-edge rel (distinct (keep he affected)))))))

(defn equality-partition
  "Compute `{:class :members}` from scratch, given the active undirected `edges` and
  the active `[preferred dispreferred]` claims.

  This is the **reference implementation**, the equality analogue of `closures`: the
  incremental union above and the class-local rebuild below must agree with it edge
  for edge, and the oracle test in `taxonomy_test` checks exactly that after every
  edit of a random sequence."
  [edges prefs]
  (let [rel (reduce (fn [r [a b :as e]]
                      (-> r (update :edges conj e)
                          (update :edge-idx idx-conj a e)
                          (update :edge-idx idx-conj b e)))
                    (empty-equality) edges)
        rel (reduce (fn [r [p d :as pp]]
                      (update-in r [:edge-prefs (pair p d)] (fnil conj #{}) pp))
                    rel prefs)]
    (-> (reduce install-class rel (components rel (into #{} (mapcat identity) edges)))
        (select-keys [:class :members]))))

(defn add-equality
  "Record `handle` as asserting that `a` and `b` denote one thing, merging their
  classes.  `preferred` names the term a `rewriteOf` puts on top (`a`, `b`, or nil
  for `sameAs` / `equals`, which deprecate nothing)."
  [tax a b handle preferred]
  (let [e (pair a b)]
    (swap! tax update :equality
           (fn [rel] (-> rel
                         (assoc-in [:support e handle] preferred)
                         (update :handles conj handle)
                         (update :handle-edge assoc handle e)
                         (update :out disj handle)
                         (apply-edge e)))))
  tax)

(defn del-equality!
  "Drop `handle`'s support for the merge of `a` and `b`.  The merge survives while any
  other sentex still asserts it; when the last one goes the class splits back into
  whatever its remaining edges still connect."
  [tax a b handle]
  (let [e (pair a b)]
    (swap! tax update :equality
           (fn [rel]
             (let [hs (dissoc (get-in rel [:support e] {}) handle)]
               (-> (if (seq hs)
                     (assoc-in rel [:support e] hs)
                     (update rel :support dissoc e))
                   (update :handles disj handle)
                   (update :handle-edge dissoc handle)
                   (apply-edge e))))))
  tax)

(defn representative
  "The term that stands for `term`'s equivalence class — `term` itself when nothing
  has merged it."
  [tax term]
  (get-in @tax [:equality :class term] term))

(defn scoped-class
  "`[members representative]` for `term` counting only the equality edges some
  supporter `visible?` admits — the equality analogue of the scoped closure reads,
  and the shape a **context-scoped** rewrite needs.

  It has to be recomputed rather than filtered out of the global partition, because
  dropping an edge can *split* a class: `A~B~C` with only `A~B` visible is the class
  `{A B}`, and its representative is elected among those two alone, not inherited from
  the class `C` was in.  The election rule is `class-rep`'s, over the visible edges'
  preference claims — so a `rewriteOf` this context cannot see neither retires a term
  nor promotes one.

  Recomputed per call and not memoized: a class is a handful of terms, and the callers
  already pay a record fetch per supporter to decide `visible?`.  The **global** read
  is `representative` above and stays the fast path — nothing that has not merged ever
  reaches here."
  [tax term visible?]
  (let [rel  (:equality @tax)
        out  (:out rel #{})
        vis  (fn [e] (some (fn [[h _]] (and (not (contains? out h)) (visible? h)))
                           (get (:support rel) e {})))
        nbrs (fn [t] (into #{} (comp (filter vis) (mapcat identity))
                           (get (:edge-idx rel) t #{})))
        members (reach term nbrs)]
    (if (= 1 (count members))
      [members term]
      (let [ps (into #{}
                     (comp (mapcat (fn [m] (get (:edge-idx rel) m #{})))
                           (distinct)
                           (filter vis)
                           (mapcat (fn [e]
                                     (keep (fn [[h p]]
                                             (when (and (not (contains? out h)) (visible? h))
                                               (pref-pair e p)))
                                           (get (:support rel) e {})))))
                     members)
            preferred (into #{} (map first) ps)
            heads     (set/difference preferred (into #{} (map second) ps))]
        [members (term-min (cond (seq heads) heads (seq preferred) preferred :else members))]))))

(defn class-fully-visible?
  "Does `visible?` admit **every believed supporter of every active edge** in `term`'s
  class?  When it does, the scoped election *is* the global one — same members, because
  no edge drops, and same representative, because no preference claim drops — so the
  caller can take `representative`'s O(1) map lookup instead of rebuilding the class.

  The condition is per *supporter*, not per edge, and that is what makes it sound.  One
  edge may carry a `sameAs` and a `rewriteOf` at once; hiding only the `rewriteOf` leaves
  the class intact and moves the head, so an edge-level test would licence the fast path
  on exactly the case that needs the slow one.

  This is the common shape rather than an optimisation for a corner: a KB states its
  merges in `CxCore`, or in the context doing the reading, and either way every
  supporter is visible.  A reader pays one memoized `visible?` per supporter of a class
  that is a handful of terms — against `scoped-class`'s reachability walk and preference
  election, which is the cost this exists to skip."
  [tax term visible?]
  (let [rel (:equality @tax)
        out (:out rel #{})]
    (every? (fn [m]
              (every? (fn [e]
                        (every? (fn [[h _]] (or (contains? out h) (visible? h)))
                                (get (:support rel) e {})))
                      (get (:edge-idx rel) m #{})))
            (get (:members rel) (get (:class rel) term term) #{term}))))

(defn same-class? "Do `a` and `b` denote the same thing?" [tax a b]
  (= (representative tax a) (representative tax b)))

(defn equiv-class "Every term known equal to `term`, incl. itself." [tax term]
  (let [rel (:equality @tax)]
    (get (:members rel) (get (:class rel) term term) #{term})))

(defn merged?
  "Has anything merged `term` at all?  The O(1) gate every scoped read takes first: a
  KB with no equalities, and a term in none of them, never pays for `scoped-class`."
  [tax term]
  (boolean (seq (get-in @tax [:equality :edge-idx term]))))

(defn merged-term-pred
  "A `term -> boolean` closed over **one** snapshot of the partition, or nil when the
  closure is empty — the gate for a caller asking `merged?` of many terms in a row.

  `merged?` derefs per call, which is the right shape for the single question a scoped
  class read asks and the wrong one for a filter running over every symbol of every
  match in a query's answer set.  Returning nil rather than a constantly-false predicate
  is what lets such a caller drop the whole filter, which is what every KB that has
  merged nothing does."
  [tax]
  (let [rel (:equality @tax)]
    (when (seq (:edges rel))
      (let [idx (:edge-idx rel)]
        (fn [term] (contains? idx term))))))

(defn deprecated?
  "Did a believed `rewriteOf` name `term` the dispreferred side?  False for a `sameAs`
  or `equals` member — those merge without deprecating either name.

  With a `visible?` supporter predicate, only the `rewriteOf`s that reader inherits
  count — the same scoping `representative` / `same-class?` / `equiv-class` take, and
  necessary for the same reason: a retirement is a sentex, so a context that cannot see
  it has not been told, and reporting the term deprecated there would contradict the
  representative that same context elects for it.  Read per supporter rather than off
  the aggregated `:edge-prefs`, since one edge may carry a `rewriteOf` and a `sameAs`
  at once and only the first deprecates."
  ([tax term] (deprecated? tax term nil))
  ([tax term visible?]
   (let [rel (:equality @tax)]
     (boolean
      (some (fn [e]
              (if-not visible?
                (some (fn [[_ d]] (= d term)) (get (:edge-prefs rel) e))
                (some (fn [[h p]]
                        (and (not (contains? (:out rel #{}) h))
                             (visible? h)
                             (= term (second (pref-pair e p)))))
                      (get (:support rel) e {}))))
            (get (:edge-idx rel) term #{}))))))

(defn- edge-pref-claims
  "The `[preferred dispreferred]` rewriteOf claims on edge `e` — all of them unscoped,
  only the believed and visible ones under `visible?`.  A `sameAs` / `equals`-only edge
  yields none, since its supporters name no preference (`pref-pair` returns nil)."
  [rel e visible?]
  (if-not visible?
    (get (:edge-prefs rel) e #{})
    (into #{}
          (keep (fn [[h p]]
                  (when (and (not (contains? (:out rel #{}) h)) (visible? h))
                    (pref-pair e p))))
          (get (:support rel) e {}))))

(defn spelling-representative
  "`term`'s representative considering only `rewriteOf` (spelling) edges — a `sameAs` /
  `equals` identity merge is **not** followed.  This is the mention read: a quoted term
  tracks a *spelling* rename of its symbol but not a *coreference* merge of its referent,
  so `res/representative-term` uses it inside a `quotingFunction`'s arguments.

  The rewriteOf edges form their own sub-partition; the answer is the representative of
  `term`'s rewriteOf-connected component, elected by the same rule `class-rep` uses — a
  preferred term nothing deprecates, else the lexicographically smallest.  A term no
  rewriteOf touches — including one merged only by `sameAs` — is its own representative,
  returned unchanged.  With `visible?`, only the believed edges that reader inherits
  count, the scoping `deprecated?` / `representative` take.  Recomputed per call: a class
  is a handful of terms, and the caller's `merged?` gate skips it entirely for an
  unmerged one."
  ([tax term] (spelling-representative tax term nil))
  ([tax term visible?]
   (let [rel (:equality @tax)]
     (loop [seen #{term} frontier [term] claims #{}]
       (if-let [t (peek frontier)]
         (let [cs  (into #{}
                         (mapcat #(edge-pref-claims rel % visible?))
                         (get (:edge-idx rel) t #{}))
               nxt (into #{} (comp (mapcat (fn [[p d]] [p d])) (remove seen)) cs)]
           (recur (into seen nxt) (into (pop frontier) nxt) (into claims cs)))
         (let [preferred  (into #{} (map first) claims)
               deprecated (into #{} (map second) claims)
               heads      (set/difference preferred deprecated)]
           (cond (seq heads)     (term-min heads)
                 (seq preferred) (term-min preferred)
                 :else           term)))))))

(defn equality-edges [tax] (get-in @tax [:equality :edges] #{}))

(defn equality-prefs
  "Every active `[preferred dispreferred]` claim — the directed `rewriteOf` graph,
  flattened out of the per-edge preference sets.  `wff` walks it to reject a cycle;
  nothing else needs the direction, since the partition itself is undirected."
  [tax]
  (into #{} (mapcat identity) (vals (get-in @tax [:equality :edge-prefs] {}))))

(defn equality-supporters
  "The handles of the sentexes asserting an **active** equality edge incident on
  `term` — the merges that put `term` in a class other than its own.

  Migration reads this to justify a rewritten twin: each incident edge is an
  independent witness for the rewrite, so the twin gets one justification per
  supporter and survives losing any single one."
  [tax term]
  (let [rel (:equality @tax)]
    (into #{}
          (comp (mapcat (fn [e] (keys (get (:support rel) e {}))))
                (remove (:out rel #{})))
          (get (:edge-idx rel) term #{}))))

;; ---- schematic rewrite rules (oriented equational rewriting) -------------
;; A schematic `(equals L R)` is oriented once (by `vaelii.impl.rewrite/orient`, at
;; the assert layer) into a rewrite `[lhs rhs]` and cached here.  The cache holds
;; only the oriented pair, its handle, and the equation's context — the term algebra
;; is `vaelii.impl.rewrite`'s and stays out of the taxonomy.  Belief rides on the
;; handle: `:rewrite-active` is the subset of `:rewrite-support` whose equation is
;; believed, reconciled by `refresh-beliefs`.

(defn add-rewrite-rule
  "Cache the oriented rewrite `lhs → rhs` asserted by equation `handle` in `context`.
  Recorded in both the support map (for revival) and the active map (assumed believed
  on assert; a settle reconciles)."
  [tax handle lhs rhs context]
  (let [entry {:handle handle :lhs lhs :rhs rhs :context context}]
    (swap! tax (fn [t] (-> t
                           (assoc-in [:rewrite-support handle] entry)
                           (assoc-in [:rewrite-active handle] entry)))))
  tax)

(defn del-rewrite-rule!
  "Drop equation `handle`'s rewrite rule entirely — the last (and only) supporter is
  gone, so the rule leaves both maps."
  [tax handle]
  (swap! tax (fn [t] (-> t
                         (update :rewrite-support dissoc handle)
                         (update :rewrite-active dissoc handle))))
  tax)

(defn rewrite-rules
  "The active oriented rewrite rules — a seq of `{:handle :lhs :rhs :context}` for
  every schematic equation currently believed.  `vaelii.impl.kb/rewrite-term` reads
  these to normalize terms; the empty case is the gate that keeps normalization a
  no-op for a KB with no schematic equations.

  **Content-ordered, not insertion-ordered.**  Normalization tries rules in this
  order at each redex, so two overlapping rules that could rewrite one term must be
  ordered by *content* and not by which equation was asserted first — otherwise the
  normal form (and thus the stored twin) would depend on arrival order, which
  order-independence (docs/nmtms.md) forbids.  Sorting by the printed LHS is arbitrary
  but stable and handle-free, so the same rule *set* always yields the same normal
  form, confluent or not.

  **Sorted once per rule set, not once per call.**  `kb/rewrite-term` calls this and
  `kb/rewrite-goal` calls that, so every `query` carrying a context reached the
  `pr-str`-per-rule sort — a cost the empty case (no schematic equations, the KB the
  gate above is written for) does not have but every KB with one pays on every read.
  The order is memoized in the `:rewrite-order` side atom, beside the main map for the
  reasons `:closure-memo` is (a read that memoizes must not contend with the writer, or
  mutate the snapshot a concurrent reader holds).

  Stamped on the **identity** of the `:rewrite-active` map, not on a generation counter.
  A persistent map is its own change detector: every writer here already replaces it
  (`add-rewrite-rule`, `del-rewrite-rule!`, `refresh-rewrite`, `clear-relations!`) and
  none can replace it without producing a different object, so no writer has to remember
  to bump anything — the failure mode a counter has, and the one that matters most for a
  field three separate paths write.  It is also ABA-free where a counter is not:
  `clear-relations!` installs a fresh empty map, which is a *new* object, whereas a
  counter reset to 0 would make a cleared taxonomy read as the pre-clear one (exactly why
  `clear-relations!` has to drop the gen-stamped memo by hand).  The cost is a re-sort
  when `refresh-rewrite` rebuilds an equal set, which is a handful of rules."
  [tax]
  (let [t      @tax
        active (:rewrite-active t)
        memo   (:rewrite-order t)
        cur    @memo]
    (if (identical? active (:for cur))
      (:rules cur)
      (let [rs (sort-by (comp pr-str (juxt :lhs :rhs)) (vals active))]
        (reset! memo {:for active :rules rs})
        rs))))

(defn- refresh-rewrite
  "Reconcile `:rewrite-active` with belief: a rule is active iff its equation handle is
  believed.  Recomputed rather than diffed — the rule set is tiny."
  [t believed? moved]
  (if-not (moved-touches? moved (:rewrite-support t))
    t
    (assoc t :rewrite-active
           (into {} (filter (fn [[h _]] (believed? h))) (:rewrite-support t)))))

(defn- moved-cache-keys
  "The flat-cache entries a supporter in `moved` asserts — the only ones whose believed
  supporters can have changed, and so the whole scope a reconcile owes.  `nil` means
  every entry with a supporter, which is what a caller holding no region gets:
  `refresh-beliefs`'s two-arity.  Every `settle` path names one.

  The flat-cache twin of `moved-edges`, and the same three claims hold.  Read forward off
  `moved` through `:cache-handle-keys`, never backward off `:cache-support`, which is what
  makes the reconcile proportional to the region a settle relabelled rather than to a map
  holding every disjoint pair, property, inverse and declared arity in the KB — and it
  subsumes the gate, since a settle touching no declaration yields no keys and the
  reconcile below returns untouched.  `moved` is a *superset* of the handles whose belief
  flipped (`jtms/touched`), so a handle in it that did not actually move costs one entry
  re-examined and never an answer.

  Plus `:cache-dirty`, the entries a belief-blind writer left owing a reconcile.  Belief
  did not move there, so `moved` cannot name them and they would otherwise never be
  narrowed.

  And off whichever side is **smaller**, for the reason `moved-edges` states: `moved` and
  the cache are independently sized, so walking `moved` unconditionally would hand the
  same O(vocabulary) bill to the settle on the opposite shape — a large relabelled region
  over a KB that declares few disjointness pairs, which arbitrating a standing set of
  P/¬P dilemmas is.  Either arm answers identically; the cost is O(min) rather than
  O(either)."
  [t moved]
  (if (nil? moved)
    (keys (:cache-support t))
    (let [hk (:cache-handle-keys t)]
      (if (and (counted? moved) (<= (count moved) (count hk)))
        (reduce (fn [s h] (if-let [ks (hk h)] (into s ks) s)) (:cache-dirty t) moved)
        ;; also the arm an empty cache takes, in O(1) — `hk` is the map being reduced
        (reduce-kv (fn [s h ks] (if (moved h) (into s ks) s)) (:cache-dirty t) hk)))))

(defn- refresh-cache-support
  "Reconcile the five flat caches — `disjoint`, the disjoint metatypes and their
  members, the predicate properties, `inverse` and the declared arities — with current
  belief, the way `refresh-relation` does for genl.  Each `[kind key]` in
  `:cache-support` is active iff some supporter is believed; install or uninstall its
  cache entry to match, reusing the very `cache-install` / `cache-uninstall` the assert
  path uses so the two can never disagree on what an active entry is.

  Every op here is O(1) and idempotent, so a reconciled entry is re-affirmed rather than
  diffed: there is no closure to rebuild, and `cache-install` on an entry already present
  changes nothing.  (genl's `refresh-relation` diffs only because rebuilding a *closure*
  is expensive.)

  Scoped to `moved-cache-keys` — an entry no moved handle supports and no writer left
  dirty is provably unchanged, so belief is never evaluated for it.  That is the locality
  invariant for these caches: the reconcile costs what moved, not what the KB declares.
  This is the pass that discharges `:cache-dirty`, so it clears the set on the way in.

  A key whose `:cache-support` entry has since gone is skipped rather than reconciled.
  Nothing in scope should name one — `support-drop` retires the handle and the dirty mark
  with the entry, and `forget-metatype` owes the same by hand — and the guard is what
  keeps the failure a no-op instead of an empty `:cache-ctxs` written back under a key no
  sentex supports, which reads as an entry asserted from nowhere."
  [t believed? moved]
  (let [touched (moved-cache-keys t moved)]
    (if (empty? touched)
      t
      (let [support (:cache-support t)]
        (reduce (fn [t k]
                  (if-let [supporters (get support k)]
                    (let [cs (believed-ctxs supporters believed?)]
                      (-> (if (seq cs) (cache-install t k) (cache-uninstall t k))
                          ;; the flat-cache twin of refresh-relation's third arm: an
                          ;; entry that stays active can still change contexts when one
                          ;; of several supporters moves belief
                          (assoc-in [:cache-ctxs k] cs)))
                    t))
                (assoc t :cache-dirty #{})    ; this pass is what discharges them
                touched)))))

(defn refresh-beliefs
  "Reconcile the cached relations with current belief: an edge (or a flat-cache entry)
  is active iff some sentex asserting it is believed.  Called after a relabel (from
  `settle`), which is the only thing that can flip a supporter's label without adding
  or removing one.

  Cheap in the common case — `believed?` is an in-memory JTMS lookup, the closures are
  only rebuilt if the active edge set actually moved, an equality edge whose supporters
  did not change label is skipped outright, and the flat caches are single-op
  idempotent reconciles.  So a settle that defeats nothing applies no difference; what it
  still pays is its **region**.  Only the equality partition and the rewrite rules decline
  to look at all (the gate below), while the two transitive relations and the flat caches
  evaluate `believed-ctxs` for every edge and entry the region names before finding that
  none of them moved.  Zero work is a region naming nothing, not a belief that held still.

  All seven caches follow belief here — the two transitive relations, the equality
  partition, and the five flat caches (`disjoint`, disjoint metatypes + members, the
  predicate properties, `inverse`, the declared arities) — so a defeated declaration
  stops taking effect the
  moment `settle` relabels, and a revived one takes effect again.

  `moved` is the set of handles whose belief just flipped (`jtms/touched`, a superset),
  and the six caches read it two ways.  The two transitive relations and the flat caches
  **scope** by it — `moved-edges` / `moved-cache-keys` turn the moved handles into the
  edges and entries they assert, and a settle reconciles those and nothing else, which is
  what keeps a flip in a 100k-edge taxonomy the price of a flip.  Those five are the
  vocabulary's own size, so nothing less than scoping them would do.

  The equality partition and the rewrite rules **gate** on it instead: a cache no moved
  handle supports is left alone, and a hit rescans it.  Both hold the KB's asserted
  term-identity claims rather than its vocabulary, and the gate reads whichever of the two
  sides is smaller, so a settle that moves neither pays the size of its own region.

  `nil` reconciles every cache unconditionally, for a caller holding no region.  `recover`
  is that caller and passes it: a settle's reconcile is scoped *and* gated on belief
  having moved, so a rebuild that replays a declaration nothing supports — OUT from the
  moment its node is made, opposed by nothing — has no settle event to lean on
  (`core/recover`).  Every `settle` path names a region instead; the supersession pass
  widens its own by hand rather than dropping it, because a supersession flip is a belief
  change with no relabel to record it."
  ([tax believed?] (refresh-beliefs tax believed? nil))
  ([tax believed? moved]
   (swap! tax (fn [t] (-> t
                          (update :genl        refresh-relation believed? moved)
                          (update :genlCx refresh-relation believed? moved)
                          (update :equality    refresh-equality believed? moved)
                          (refresh-rewrite believed? moved)
                          (refresh-cache-support believed? moved))))
   tax))

(defn clear-relations!
  "Drop **every** cache, support and all.  `recover` rebuilds them from the durable
  store and must not merge into whatever the in-memory taxonomy already had —
  otherwise a stale entry outlives the data it came from.

  Clearing must cover **all eight** caches, not just the two transitive relations:
  because `recover` merges into whatever it clears, a merge can only ever *add*, so a
  disjoint pair, a predicate property, an inverse or a declared arity whose sentex is
  gone would survive the recovery that is supposed to re-derive it.  The equality partition is the same
  story and worse — a stale merge makes two individuals one.  Clearing all eight is
  what makes `recover` a rebuild rather than a top-up.

  Clearing then replaying the *stored* declarations (defeated ones included) is
  deliberate: `:support` and `:cache-support` must record every asserting sentex, and the
  `refresh-beliefs` `recover` runs over the replay decides which entries are active — so
  a defeated `(disjoint dog cat)` is rebuilt into the cache and then dropped by belief,
  giving the same answer either side of a restart.  Belief-filtering the replay instead
  would lose the disbelieved supporter, and clearing its defeat could never revive the
  entry."
  [tax]
  (swap! tax assoc
         :genl (empty-relation) :genlCx (empty-relation)
         :equality (empty-equality)
         :disjoint #{} :disjoint-index {} :disjoint-metatypes #{} :metatype-members {}
         :props {} :inverse {} :arity {}
         :cache-support {} :cache-handle-keys {} :cache-dirty #{} :cache-ctxs {}
         :rewrite-support {} :rewrite-active {})
  ;; The read memo is stamped with each relation's `:gen`, which the fresh
  ;; `empty-relation`s just reset to 0, so drop the memo too — otherwise a lingering
  ;; entry could be mistaken for a current one.  The vis-index is stamped the same
  ;; way, so it goes with it.  The rewrite order is stamped on the map object it
  ;; sorted, and the fresh `{}` above can never be that object, so dropping it
  ;; releases the rules it retains rather than correcting an answer.
  (reset! (:closure-memo @tax) {})
  (reset! (:vis-index @tax) {})
  (reset! (:rewrite-order @tax) nil)
  tax)

;; ---- introspection (for rendering) --------------------------------------

(defn genl-edges   [tax] (get-in @tax [:genl :edges] #{}))
(defn genlCx-edges [tax] (get-in @tax [:genlCx :edges] #{}))

(defn edge-contexts
  "The supporting contexts of active edge `[a b]` in relation `rel-key` — the
  believed supporters' after a settle, every supporter's between a write and the
  settle (the same discipline as `:edges` liveness).  nil in the set is a supporter
  with no recorded context, which constrains everywhere.  Empty when the edge is
  not active."
  [tax rel-key e]
  (get-in @tax [rel-key :edge-ctxs e] #{}))

(defn cache-contexts
  "The supporting contexts of flat-cache entry `k` (`[:disjoint #{a b}]`,
  `[:prop kind pred]`, …) — the flat-cache twin of `edge-contexts`."
  [tax k]
  (get-in @tax [:cache-ctxs k] #{}))

(defn- cache-entry-visible?
  "Does flat-cache entry `k` have a believed supporter visible from `context`?

  The old path remains a context-set intersection while no exception exists. Once
  exception filtering is active, inspect supporters: the effective context cone
  handles excepted genlCx links and the KB callback handles belief plus exceptions
  targeting the declaration itself."
  [tax k context]
  (if-not (scoped-context? context)
    true
    (let [t @tax]
      (if (supporter-filter-active? t)
        (let [scope {:contexts (context-up tax context)
                     :context context
                     :supporter-visible? (:supporter-visible? t)}]
          (boolean
           (some (fn [[h c]] (scope-admits-supporter? scope h c))
                 (get-in t [:cache-support k]))))
        (ctxs-visible? (get-in t [:cache-ctxs k])
                       (closure-of tax :genlCx :fwd context))))))
(defn types        [tax] (get-in @tax [:genl :nodes] #{}))
(defn contexts     [tax] (get-in @tax [:genlCx :nodes] #{}))
(defn disjoint-pairs [tax] (:disjoint @tax))

(defn relation-gen
  "The generation counter of a cached relation (`:genl` / `:genlCx`), bumped on
  every edge change.  A caller memoizing something derived from a closure reads this to
  notice it must recompute, without comparing edge sets — which is the whole point,
  since the edge set is the thing that is too big to compare."
  [tax rel-key]
  (get-in @tax [rel-key :gen] 0))

(defn- reachable-in?
  "Does `src` reach `tgt` in relation `rel-key`, following `:fwd`?  The depth-pruned
  `reachable?` rejects most pairs in O(1) and never materializes a closure — the cheap
  path shared by `genl?` / `sees?` and the assert-time cycle checks in `wff`.

  A relation left `:loose?` by a deferred batch has no sound potential yet, so the
  depth is withheld and the walk runs unpruned: slower, and the same answer."
  [tax rel-key src tgt]
  (let [rel (get @tax rel-key)]
    (reachable? src tgt (:fwd rel) (when-not (:loose? rel) (:depth rel)) (:scc rel))))

;; ---- genl (types) --------------------------------------------------------
;;
;; Each read has a context arity: the closure over only the edges visible from
;; that context (`visible-ctxs`).  A nil visible set — no context, a `?var`, or a
;; context that sees every asserting context — is the global path, byte-identical
;; to the one-shorter arity.  An empty visible set still walks: an edge with a
;; nil-context supporter constrains everywhere, including from a context that
;; sees no asserting context at all.

(defn genls
  "Supertypes of t, incl t — through every active edge, or (with `context`) only
  the edges visible from it."
  ([tax t] (closure-of tax :genl :fwd t))
  ([tax t context]
   (if-some [scope (relation-scope tax :genl context)]
     (closure-of-vis tax :genl :fwd t scope)
     (closure-of tax :genl :fwd t))))

(defn specs
  "Subtypes of t, incl t — through every active edge, or (with `context`) only
  the edges visible from it."
  ([tax t] (closure-of tax :genl :rev t))
  ([tax t context]
   (if-some [scope (relation-scope tax :genl context)]
     (closure-of-vis tax :genl :rev t scope)
     (closure-of tax :genl :rev t))))

(defn specs-of-all
  "The union of `specs` over every node in `nodes`, walked **once**.

  `specs` memoizes per node, which is the right shape for one question asked repeatedly
  and the wrong one for many questions asked together: n nodes are n closures, and where
  the nodes nest — a chain, which is what a batch of `genl` edges written by a load is —
  those closures sum to n²/2 elements though their union holds n.  The memo cannot help,
  since it is keyed on the node a walk started from and every walk starts somewhere else.

  So this seeds one traversal with all of them and guards with one `seen`, making the cost
  the union plus the edges under it rather than the sum of the parts.  Reflexive like
  `specs`, and unscoped like its two-arity: a caller wanting the visibility filter wants
  `specs` per node and the memo that comes with it.

  Deliberately not memoized.  The key would be the seed set, which is a different set
  almost every time and would hold every predicate it ever named."
  [tax nodes]
  (let [adj (:rev (get @tax :genl))]
    (loop [seen (transient (set nodes)), stack (vec nodes)]
      (if-let [n (peek stack)]
        (let [fresh (remove #(get seen %) (get adj n))]
          (recur (reduce conj! seen fresh) (into (pop stack) fresh)))
        (persistent! seen)))))

(defn genl?
  "Is sub a (transitive) subtype of super — through every active edge, or (with
  `context`) only the edges visible from it?"
  ([tax sub super] (reachable-in? tax :genl sub super))
  ([tax sub super context]
   (if-some [scope (relation-scope tax :genl context)]
     (let [rel (get @tax :genl)]
       (reachable-filtered? sub super :genl rel scope
                            (when-not (:loose? rel) (:depth rel))
                            (:scc rel)))
     (reachable-in? tax :genl sub super))))

;; ---- what a reachability rests on ---------------------------------------
;;
;; `genls` / `genl?` answer *whether* one type reaches another; a caller that is
;; going to **depend** on that reachability needs to name the sentexes it rests on,
;; so the dependency can be withdrawn when they are.  A forward firing matched by
;; subsumption is exactly such a caller (docs/contexts.md).
;;
;; The witness is **one path, one supporter per edge** — a justification is a
;; conjunction of supports, not a proof that no other support exists.  A second route
;; (another path, or the same edge asserted from a second context) therefore does not
;; appear; when the named witness goes, what rested on it goes with it and is
;; re-derived from the surviving route.  That is the bargain the qualitative support
;; already makes for the same reason (docs/qcn.md): every route re-derives what the
;; first one reached, so carrying them all would be one justification per path in a
;; hierarchy where paths multiply.
;;
;; The choice is keyed on **content** — the walk expands neighbours in name order and
;; the supporter is picked by asserting context — never on handle id, which is
;; allocated in assertion order and would smuggle arrival order into belief.
;;
;; Each step also reports the **context** its supporter was asserted from, because a
;; caller that depends on a reachability inherits its visibility: a conclusion resting
;; on an edge stated somewhere belongs no higher than a context that can see where it
;; was stated.  So the witness prefers, per edge, the **most general** supporter
;; available — the one every other supporter of that edge sees — since a needlessly
;; specific choice would drag its dependant down with it.  Across *paths* the witness is
;; still the shortest one; a longer route through more general contexts might carry
;; further, and is deliberately not searched for.

(defn- more-general-supporter
  "The member of `cands` (`[handle ctx]` pairs) whose context every other candidate's
  context sees — the one that constrains a dependant least — or nil when no member is
  comparable to all of them.  A nil context is recorded by a writer that had none and
  is seen from everywhere, so it wins outright."
  [tax cands]
  (or (first (filter (fn [[_ c]] (nil? c)) cands))
      (first (filter (fn [[_ c]]
                       (every? (fn [[_ c2]] (contains? (closure-of tax :genlCx :fwd c2) c))
                               cands))
                     cands))))

(defn- visible-edge-supporters
  "The believed supporters of active edge `e` a reader seeing `vis` can use, as a vector
  of `[handle ctx]` — the candidate set `edge-supporter` chooses the most general of, and
  the strength-aware pickers below read for class.  A supporter is believed iff its own
  context is in `:edge-ctxs` (an edge is stored once per context, so the context
  identifies it); nil `vis` is the unscoped read where every asserting context is visible."
  [rel e scope]
  (into [] (filter (let [live (get (:edge-ctxs rel) e #{})]
                     (fn [[h c]]
                       (if (map? scope)
                         (scope-admits-supporter? scope h c)
                         (and (contains? live c)
                              (or (nil? scope) (nil? c) (scope c)))))))
        (get (:support rel) e {})))

(defn- edge-supporter
  "A believed supporter of active edge `e` that a reader seeing `vis` can use, as
  `[handle ctx]`, or nil.  `:edge-ctxs` is the believed supporters' context set, so a
  supporter is believed iff its own context is in it — an edge is stored once per
  context, so that identifies it.

  The **most general** visible supporter, since its context is inherited by whatever
  depends on the edge; asserting-context name breaks a tie between incomparable ones, so
  the choice is a function of the contexts rather than of the order the supporters
  arrived in.  The key is that name and **nothing else** — never a handle, which is
  allocated in assertion order and would decide where a dependant's conclusion lands by
  which supporter was loaded first (`term-key`, and docs/nmtms.md).  Two candidates
  sharing a context therefore tie, and are left to the stable sort: same context means
  same visibility and same generality, so a dependant inherits the identical placement
  whichever of them is named, and there is nothing left for a further tie-break to
  decide.

  An edge with a **single** supporter takes neither the ordering nor the comparison: it
  is trivially the most general, and that is the overwhelming common case.  The
  short-circuit is not a micro-optimization — `more-general-supporter` reads the
  genlCx closure, whose memo a bulk load retires on every context edge it asserts,
  so paying it per edge per subsuming firing cost a fifth of the schema load."
  [tax rel e vis]
  (let [cands (visible-edge-supporters rel e vis)]
    (cond
      (empty? cands)      nil
      (nil? (next cands)) (nth cands 0)
      :else (let [ordered (sort-by (fn [[_ c]] (str c)) cands)]
              (or (more-general-supporter tax ordered) (nth ordered 0))))))

(defn- most-general-of
  "The most general of `cands` (a non-empty vector of `[handle ctx]`), tie-broken by
  asserting-context name and never by handle — exactly `edge-supporter`'s choice, factored
  so the strength-aware picker below shares it once it has narrowed to one strength class."
  [tax cands]
  (if (nil? (next cands))
    (nth cands 0)
    (let [ordered (sort-by (fn [[_ c]] (str c)) cands)]
      (or (more-general-supporter tax ordered) (nth ordered 0)))))

(defn- edge-class
  "The defeat class active edge `e` holds at, as `vis` sees it: the **strongest** of its
  visible supporters' classes (`strength/max`), `:default` when none is monotonic, or nil
  when no supporter is visible at all.  `supporter-class` is `handle → class` — a live
  JTMS `defeat-class` read — and a supporter it cannot classify (OUT, or mid-settle)
  counts as `:default`, the weakest, so the walk never over-claims `:monotonic` for an
  edge it cannot confirm holds that strongly."
  [rel e vis supporter-class]
  (let [cands (visible-edge-supporters rel e vis)]
    (when (seq cands)
      (reduce (fn [c [h _]] (strength/max c (or (supporter-class h) :default)))
              :default cands))))

(defn- strongest-edge-supporter
  "A `[handle ctx]` witness for edge `e` that holds at the edge's own strength: the most
  general supporter *among those at the maximum class*.  So the justification records a
  supporter as strong as the edge is, and where two supporters tie on strength the
  placement-relevant (most general) one is named — `edge-supporter`'s own choice, applied
  after the strength filter.  nil when the edge has no visible supporter."
  [tax rel e vis supporter-class]
  (let [cands (visible-edge-supporters rel e vis)]
    (when (seq cands)
      (let [top  (reduce (fn [c [h _]] (strength/max c (or (supporter-class h) :default)))
                         :default cands)
            best (filterv (fn [[h _]] (= top (or (supporter-class h) :default))) cands)]
        (most-general-of tax best)))))

(defn- bfs-witness-path
  "Shortest path `sub →* super` over neighbours `nbrs`, admitting an edge `[p x]` only
  when `admit?` allows it and mapping each traversed edge to a `[handle ctx]` supporter via
  `witness`.  Returns the vector of witnesses (one per edge, `super`-end first) or nil —
  unreachable, or an admitted edge whose `witness` came back nil.  Neighbours are expanded
  in the order `nbrs` imposes (name order), so the path is a function of the hierarchy
  rather than of the order it was built in, and the first path to `super` is a shortest
  one."
  [sub super nbrs admit? witness]
  (loop [q (conj clojure.lang.PersistentQueue/EMPTY sub), parent {sub nil}]
    (when-let [n (peek q)]
      (if (= n super)
        (loop [x n, acc []]
          (if (= x sub)
            acc
            (let [p (get parent x)]
              (when-let [s (witness [p x])]
                (recur p (conj acc s))))))
        (let [fresh (remove #(contains? parent %)
                            (filter #(admit? [n %]) (nbrs n)))]
          (recur (into (pop q) fresh)
                 (into parent (map (fn [x] [x n])) fresh)))))))

(defn reach-support
  "A witness for `sub →* super` in relation `rel-key`, as the `[handle ctx]` of one
  supporter per edge along a single path — or nil when `context` sees no such path.
  Empty for `sub` = `super`, which rests on nothing.  A nil `context` walks
  unscoped, which is what a caller wanting the witness *before* it knows its vantage
  asks for.

  Walks the same visible adjacency the scoped closure reads do, so it finds a witness for
  exactly the pairs `genl?` answers true from that context, and the two can never disagree
  about what a context can reach.  Neighbours are expanded in name order, so the answer is
  a function of the hierarchy rather than of the order it was built in.

  **Without `supporter-class`** it is breadth-first — the witness is a *shortest* path (the
  fewest supports the reachability can be made to depend on), and each edge names its most
  general supporter (`edge-supporter`), the choice placement wants.  This is the read the
  `genlCx` visibility walk and every unstrengthened caller take.

  **With `supporter-class`** (a `handle → defeat-class` read) it is a *widest-bottleneck*
  path: the route whose floor — the `min` defeat class along it — is highest, tie-broken by
  depth then by the same name order.  Each edge names its **strongest** supporter
  (`strongest-edge-supporter`), so the conclusion a firing builds over these handles is
  capped at the floor and no lower (reasoning/26).  Since there are exactly two classes
  (`strength.clj`), the widest floor is found by trying each class as a threshold, highest
  first, and taking the first shortest path made only of edges that clear it — a threshold
  scan that stays correct for any fixed number of classes and is two passes for two."
  ([tax rel-key sub super context] (reach-support tax rel-key sub super context nil))
  ([tax rel-key sub super context supporter-class]
   (if (= sub super)
     []
     (let [rel (get @tax rel-key)
           scope (relation-scope tax rel-key context)
           ;; nil `vis` is the unscoped walk — every asserting context is visible, so
           ;; the plain adjacency *is* the visible one, exactly as in `genls`
           adj (if (nil? scope) #(get (:fwd rel) %) #(visible-neighbours rel-key rel :fwd scope %))
           ;; `str` keeps a node that is not a symbol (a NAT) sortable; built once per
           ;; adjacency now, and a node with 0/1 neighbour — common in a sparse relation —
           ;; sorts nothing
           nbrs #(nm/sort-by-content-key str compare (adj %))]
       (if (nil? supporter-class)
         (bfs-witness-path sub super nbrs (fn [_] true)
                           #(edge-supporter tax rel % scope))
         (some (fn [threshold]
                 (bfs-witness-path
                  sub super nbrs
                  (fn [e] (>= (strength/rank-of (edge-class rel e scope supporter-class))
                              (strength/rank-of threshold)))
                  #(strongest-edge-supporter tax rel % scope supporter-class)))
               [:monotonic :default]))))))

(defn reach-strength
  "The defeat class of the **strongest** route `sub →* super` in `rel-key` that `context`
  sees — `:monotonic` / `:default`, or nil when unreachable.  `:monotonic` for `sub` =
  `super`, which rests on nothing and so holds as strongly as anything can.
  `supporter-class` is the same `handle → class` read `reach-support` takes.

  Derived from `reach-support`'s widest-bottleneck path so the number and the witness can
  never disagree: the floor of the path it names *is* the strength, since each edge on it
  contributes its strongest supporter (docs/taxonomy.md, \"Strength of a subsumption
  path\")."
  [tax rel-key sub super context supporter-class]
  (if (= sub super)
    :monotonic
    (when-let [path (reach-support tax rel-key sub super context supporter-class)]
      (reduce (fn [floor [h _]] (strength/min floor (or (supporter-class h) :default)))
              :monotonic path))))

;; ---- genlCx (contexts) ---------------------------------------------------

(defn raw-context-up
  "Contexts `c` inherits from through the active genlCx cache, without `except` holes.

  Exception evaluation uses this non-recursive base relation to decide which exception
  declarations a reader can see. Ordinary callers want `context-up`, which filters an
  excepted genlCx supporter from the resulting walk."
  [tax c]
  (closure-of tax :genlCx :fwd c))

(defn raw-sees?
  "Does `k` inherit `y` in the active genlCx cache before exception filtering?"
  [tax k y]
  (reachable-in? tax :genlCx k y))

(defn context-up
  "Contexts c inherits from, incl c, after context-visible genlCx exceptions."
  [tax c]
  (if-some [scope (relation-scope tax :genlCx c)]
    (closure-of-vis tax :genlCx :fwd c scope)
    (raw-context-up tax c)))

(defn context-down
  "Contexts that inherit from c, incl c, after context-visible genlCx exceptions."
  [tax c]
  (let [raw (closure-of tax :genlCx :rev c)]
    (if (supporter-filter-active? @tax)
      ;; Reverse visibility has no single reader: every candidate descendant brings
      ;; its own exception cone.  Filter the raw candidates by that candidate's
      ;; forward answer instead of pretending `c` supplies one static reverse scope.
      (into #{} (filter #(sees? tax % c)) raw)
      raw)))

(defn sees? "Does context k see assertions in context y?" [tax k y]
  (if-some [scope (relation-scope tax :genlCx k)]
    (let [rel (get @tax :genlCx)]
      (reachable-filtered? k y :genlCx rel scope
                           (when-not (:loose? rel) (:depth rel))
                           (:scc rel)))
    (reachable-in? tax :genlCx k y)))

(defn- seeing-member
  "The member of `ctxs` that sees every other member, or nil.  When one exists it is a
  **maximal common descendant**: any common descendant sees every member, so it sees
  the found `k`, making `k` its ancestor-or-self.  A rule and its antecedent facts
  sitting on one spine — nearly every forward firing — is answered here by |ctxs|²
  depth-pruned `sees?` probes, no closure read at all.

  It is *the* maximum unless two members see each other, in which case both qualify
  and they are the same place to stand; the tie is broken by `term-min` rather than by
  position, so a firing does not place its conclusion in whichever mutually-visible
  context its antecedents happened to be listed in first."
  [tax ctxs]
  (let [seers (filter (fn [k] (every? #(sees? tax k %) ctxs)) ctxs)]
    (when (seq seers) (term-min seers))))

(defn- placement-rep
  "The one context that stands for `k`'s mutually-visible group, or `k` itself when it
  is in no cycle.

  Every context in `k`'s component sees exactly what `k` sees, so if `k` can hold a
  conclusion so can every one of them, and all of them equally: the group is one place
  to stand wearing several names.  Which name is `term-min`'s — content, never arrival
  order — and it is applied to **both** of the function below's exits, or the same
  firing would land in `CxAlpha` when its antecedents named the cycle and in
  `CxBeta` when they named something above it."
  [tax k]
  (get-in @tax [:genlCx :scc k] k))

(defn- common-descendant-set
  "Every context that sees all of `cs` — the intersection of the down closures,
  stopping at the first empty intermediate rather than intersecting the rest into
  nothing."
  [tax cs]
  (if (seq cs)
    (reduce (fn [acc c]
              (let [i (set/intersection acc (context-down tax c))]
                (if (seq i) i (reduced i))))
            (context-down tax (first cs)) (rest cs))
    #{}))

(defn- maximal-common-descendants*
  "The general path of `maximal-common-descendant-contexts`, below — every case its
  one-context fast exit does not answer."
  [tax ctxs]
  (let [cs (vec (distinct ctxs))]
    (if-let [k (seeing-member tax cs)]
      #{(placement-rep tax k)}
      (let [common (common-descendant-set tax cs)]
        (into #{}
              (comp (remove (fn [k]
                              (some (fn [anc] (and (not= anc k)
                                                   (contains? common anc)
                                                   (not (sees? tax anc k))))
                                    (context-up tax k))))
                    (map (fn [k] (placement-rep tax k))))
              common)))))

(defn maximal-common-descendant-contexts
  "The *maximal* elements of the **common descendants** of `ctxs`: the contexts K
  that see every ctx (each ctx in up(K)) — i.e. the intersection of the down
  closures — keeping only the most general.  Returns a set: possibly empty (no
  common view), possibly several (incomparable maxima).  Used to place a
  forward-derived sentex given the contexts of the rule and its antecedent facts.

  Two exits ahead of the closure work, because this runs on every forward firing: a
  member that sees every other member is the maximum (`seeing-member`), and an
  intersection that empties part-way skips the maximality filter, whose `context-up`
  read per survivor is the expensive half on a wide lattice.

  **Mutually visible contexts are one maximum, not none and not two.**  A common
  ancestor only dominates `k` if it does not see `k` back; two contexts in a
  `genlCx` cycle are equally general, so each would otherwise strike the other
  out and the firing would have nowhere to land.  They are collapsed to one by
  `term-min` — the same content-keyed choice `seeing-member` makes — since placing the
  conclusion in every member of a cycle would store one claim several times over in
  contexts that already see each other."
  [tax ctxs]
  (let [c0 (first ctxs)]
    (if (and observe/*chain-fast-paths*
             (some? c0)
             (every? #(= c0 %) (next ctxs)))
      ;; every member is the one context — the general path's `seeing-member` answer
      ;; (its `sees?` probe is reflexive, so a single distinct member always passes
      ;; it), reached without building the distinct vector or filtering it.  This is
      ;; nearly every forward firing (rule and facts in one context).  `placement-rep`
      ;; still runs: a member of a `genlCx` cycle places at the group's one name
      ;; here as everywhere, and a context the taxonomy has never heard of comes back
      ;; as itself on both paths.
      #{(placement-rep tax c0)}
      (maximal-common-descendants* tax ctxs))))

(defn common-descendants
  "Every context that sees all of `ctxs` — the intersection of their down closures.
  The set `maximal-common-descendant-contexts` takes the maxima of, for a caller that
  needs to ask something *of each member* rather than only where the most general ones
  are (`settle`'s exposure asks each whether it can prove a disjointness)."
  [tax ctxs]
  (common-descendant-set tax (vec (distinct ctxs))))

(defn maximal-contexts
  "The maximal (most general) contexts in the supplied `ctxs` under the current
  context-visibility relation.

  Unlike `maximal-common-descendant-contexts`, this does not manufacture a candidate
  set from assertion contexts.  It maximizes a set a caller has already filtered by a
  stronger predicate — notably forward placement while visibility exceptions are
  active, where a sentex can be hidden at its assertion context and restored only in a
  descendant by a meta-exception.  Mutually visible contexts are collapsed through the
  same stable representative used by ordinary placement."
  [tax ctxs]
  (let [members (set ctxs)]
    (into #{}
          (comp (remove (fn [k]
                          (some (fn [anc]
                                  (and (not= anc k)
                                       (contains? members anc)
                                       (not (sees? tax anc k))))
                                (context-up tax k))))
                (map (fn [k] (placement-rep tax k))))
          members)))

(defn common-descendant?
  "Does any context see every member of `ctxs` — is the common-descendant set
  non-empty?  The boolean of `maximal-common-descendant-contexts`, for the callers
  that only ever ask existence (`settle`'s nogood pairing asks it of every opposed
  belief pair): the maximality filter never runs, the comparable case never reads a
  closure, and the fallback intersection stops at the first empty."
  [tax ctxs]
  (let [cs (vec (distinct ctxs))]
    (boolean (and (seq cs)
                  (or (seeing-member tax cs)
                      (seq (common-descendant-set tax cs)))))))

(defn meet-closure
  "`ctxs` closed under `maximal-common-descendant-contexts` of its pairs: every context
  where two or more of them meet, plus the members themselves.

  The shape a reader enumeration needs.  Knowledge stated in several contexts is read
  by whoever inherits some combination of them, and *which* combination changes the
  answer — a qualitative network composes only the constraints one reader can see
  (docs/qcn.md), an equality election runs only over the edges one reader can see
  (docs/equality.md).  So the parties are the fact-holding contexts and the contexts
  where they meet, and both callers want exactly this set.

  **Pairs reach every subset.**  A common descendant of `{a b c}` is a common
  descendant of `{a b}`, so it lies under some maximal one `m`, and under `c`; hence
  under a maximal common descendant of `{m c}`, which the next round adds.  The closure
  may therefore hold a context that is maximal for no subset — harmless for both
  callers, since a more specific reader sees a superset of the knowledge and so either
  agrees with a more general one or refines it.

  **Fewer than two contexts closes immediately**, which is every KB that has not
  divided the knowledge in question between contexts: there is nothing for a
  second to meet, so no closure is read at all."
  [tax ctxs]
  (let [start (set ctxs)]
    (if (< (count start) 2)
      start
      (loop [acc start]
        (let [more (into acc
                         ;; contexts are symbols, so order them directly — the `str` was
                         ;; rebuilt for both on every pair of an n² sweep, and the result
                         ;; is a set, so the pair-dedup order is immaterial anyway
                         (for [a acc, b acc
                               :when (neg? (compare a b))
                               m (maximal-common-descendant-contexts tax [a b])]
                           m))]
          (if (= more acc) acc (recur more)))))))

;; ---- disjointness --------------------------------------------------------

(defn add-disjoint
  ([tax a b handle] (add-disjoint tax a b handle nil))
  ([tax a b handle ctx]
   (let [k [:disjoint #{a b}]]
     (swap! tax supported-add k handle ctx #(cache-install % k)))
   tax))
(defn del-disjoint! [tax a b handle]
  (let [k [:disjoint #{a b}]]
    (swap! tax supported-del k handle #(cache-uninstall % k)))
  tax)

(defn- forget-metatype
  "Drop `m` entirely: the mark, its recorded members, and the support entries behind
  them.  Purging the support matters — a re-declaration rescans the store for members
  and re-adds them, so a leftover handle from the previous life would keep a
  membership alive after the sentex stating it had gone.

  This is the one teardown that drops `:cache-support` entries without going through
  `support-drop`, so it owes the two indexes keyed off it — `:cache-handle-keys` and
  `:cache-dirty` — the same removal by hand.  That is a **contract**, not tidiness.
  `:cache-handle-keys` is what `moved-cache-keys` reads to turn a settle's moved handles
  into the entries to reconcile, so a handle left in it after its entry is gone puts a key
  nothing supports into every later scope, for the life of the KB; and a `:cache-dirty`
  mark left behind puts it there on *every* settle, moved or not.  Both are then skipped
  by the reconcile's own guard, so the cost is wasted work rather than a wrong answer —
  but it is wasted work that never stops.

  A dropped member's handle leaves `:cache-handle-keys` by its `[kind key]`, not
  wholesale: one sentex names one claim today, and the index is a multimap precisely so
  nothing here has to depend on that.

  Which entries to drop costs **one** scan of `:cache-support` and the removals are
  keyed off what it found, rather than rebuilding each map around a predicate: the map
  holds every disjoint pair, property, inverse and declared arity in the KB (OpenCyc:
  tens of thousands) where a metatype has a handful of members, so a rebuild is
  proportional to the wrong thing twice over.  The scan itself cannot be avoided by
  reading `:metatype-members` for the keys — that map is belief-filtered, so a member
  whose supporters are all defeated has left it while the `:cache-support` entry this
  exists to purge is still there.  `:cache-ctxs` is written by the same two functions as
  `:cache-support` and keys identically, so one key list serves both."
  [t m]
  (let [member-of-m? (fn [[k _]] (and (vector? k) (= :member (first k)) (= m (second k))))
        dropped      (into {} (filter member-of-m?) (:cache-support t))
        ks           (keys dropped)]
    (-> (reduce (fn [t [k supporters]]
                  (reduce (fn [t h] (forget-handle-key t h k)) t (keys supporters)))
                t dropped)
        (update :disjoint-metatypes disj m)
        (update :metatype-members dissoc m)
        (update :cache-support #(apply dissoc % ks))
        (update :cache-ctxs #(apply dissoc % ks))
        (update :cache-dirty #(reduce disj % ks)))))

(defn mark-disjoint-metatype
  ([tax m handle] (mark-disjoint-metatype tax m handle nil))
  ([tax m handle ctx]
   (let [k [:metatype m]]
     (swap! tax supported-add k handle ctx #(cache-install % k)))
   tax))
(defn unmark-disjoint-metatype! [tax m handle]
  (swap! tax supported-del [:metatype m] handle #(forget-metatype % m))
  tax)
(defn disjoint-metatype? [tax m] (contains? (:disjoint-metatypes @tax) m))
(defn disjoint-metatypes [tax] (:disjoint-metatypes @tax))

;; A metatype's members are **recorded, not materialized**.  `(disjointMetatype M)`
;; makes every pair of M's members disjoint.  Materializing that clique would mean
;; n(n-1)/2 real `(disjoint a b)` sentexes: quadratic in the member count and stored
;; as independent premises with no justification linking them back to M, so retracting
;; M could not withdraw them and the KB would fill with derived-looking content nobody
;; wrote.
;;
;; Instead membership is cached here and `disjoint?` consults it directly.  The
;; clique becomes a property of the code rather than of the store: nothing is
;; written, retracting M releases every pair at once, and retracting a single
;; `(M T)` releases exactly T's pairs.

(defn add-metatype-member
  ([tax m t handle] (add-metatype-member tax m t handle nil))
  ([tax m t handle ctx]
   (let [k [:member m t]]
     (swap! tax supported-add k handle ctx #(cache-install % k)))
   tax))
(defn del-metatype-member! [tax m t handle]
  (let [k [:member m t]]
    (swap! tax supported-del k handle #(cache-uninstall % k)))
  tax)
(defn metatype-members [tax m] (get-in @tax [:metatype-members m] #{}))

(def ^:dynamic *separation-frame-cache*
  "An optional atom `{[a context] frame}` for a **read-only** pass (see
  `*closure-pass-cache*`).  A cold rebuild's clash pass asks `disjointness-test` — and
  so `separation-frame` — once per candidate membership `(a x)`, but the frame depends
  on `a` and `context` alone, and the region holds millions of memberships over a few
  thousand types, so the same `[a context]` frame is rebuilt once per *instance* of the
  type.  Bound and dropped by the pass, which holds the taxonomy still, so the frame is
  gen-stable for its span; nil off such a pass."
  nil)

(defn- separation-frame*
  "Everything a disjointness question about `a` settles before any candidate is named:
  `a`'s supertype closure, the declarations that reach it, and the visibility
  predicates its context imposes.

  What survives the build is only what `a` can possibly be separated *by*: the
  supertypes of `a` that are declared disjoint from something (`:seps`, each with the
  set it is declared disjoint from), and the metatypes some supertype of `a` belongs
  to (`:metas`, each as `[m members members-above-a]`).  Both are usually empty — most
  types are declared disjoint from nothing and belong to no metatype — and when they
  are, no candidate is looked at at all, not even to read its closure.

  Two readers ask it in opposite directions: `disjointness-test` closes over it and
  tests a candidate, `separating-partners` reads the same two rosters to *enumerate*
  the other side.  One prologue, because the failure two copies of it would have is a
  candidate the predicate convicts and the enumeration never reaches.

  A nil, variable, or otherwise unscoped `context` gives visibility predicates that are
  constantly true *and take no key*, so the unscoped path never builds the `#{x y}` a
  visibility lookup would need — the whole reason the pair set is not what disjointness
  is asked of."
  [tax a context]
  (let [scoped? (scoped-context? context)
        as      (if scoped? (genls tax a context) (genls tax a))
        t       @tax
        members (:metatype-members t)
        pair-vis?   (if scoped?
                      (fn [x y] (cache-entry-visible? tax [:disjoint #{x y}] context))
                      (fn [_ _] true))
        meta-vis?   (if scoped?
                      (fn [m] (cache-entry-visible? tax [:metatype m] context))
                      (fn [_] true))
        member-vis? (if scoped?
                      (fn [m ty] (cache-entry-visible? tax [:member m ty] context))
                      (fn [_ _] true))
        ;; `a`'s separable supertypes, each with what it is declared disjoint from
        seps  (let [didx (:disjoint-index t)]
                (into [] (keep (fn [x] (when-let [ys (get didx x)] [x ys]))) as))
        ;; and the metatypes that hold some supertype of `a` — a metatype holding none
        ;; can separate `a` from nothing, so it leaves the roster here rather than
        ;; being re-examined per candidate
        metas (into []
                    (keep (fn [m]
                            (let [ms (get members m)]
                              (when (and (seq ms) (meta-vis? m))
                                (let [in-a (filterv #(and (contains? as %) (member-vis? m %)) ms)]
                                  (when (seq in-a) [m ms in-a]))))))
                    (:disjoint-metatypes t))]
    {:scoped? scoped? :seps seps :metas metas
     :pair-vis? pair-vis? :member-vis? member-vis?}))

(defn- separation-frame
  "`separation-frame*`, memoized per `[a context]` when a pass cache is bound
  (`*separation-frame-cache*`).  The clash pass asks the same type's frame once per
  instance of the type; off the pass this is a bare call, byte-identical."
  [tax a context]
  (let [sfc *separation-frame-cache*]
    (if sfc
      (let [k [a context]]
        (or (get @sfc k)
            (let [f (separation-frame* tax a context)]
              (swap! sfc assoc k f)
              f)))
      (separation-frame* tax a context))))

(defn disjointness-test
  "A predicate `type -> boolean` answering `(disjoint? tax a <type> context)` — the
  question with everything that depends on `a` and `context` alone read once
  (`separation-frame`).  `disjoint?` is this asked once; `checks/disjoint-problem`
  asks it of every type the term already holds, which is the shape it exists for.

  A type `a` no declaration reaches answers false without looking at the candidate at
  all; one that *is* separable pays a set lookup per declaration rather than a walk
  over the closure product."
  [tax a context]
  (let [{:keys [scoped? seps metas pair-vis? member-vis?]} (separation-frame tax a context)]
    (if (and (empty? seps) (empty? metas))
      (constantly false)
      (fn [b]
        (let [bs (if scoped? (genls tax b context) (genls tax b))]
          (boolean
           (or (some (fn [[x ys]]
                       (some (fn [y] (and (not= x y) (contains? bs y) (pair-vis? x y))) ys))
                     seps)
               ;; a metatype separates when it holds a supertype of `a` and a *different*
               ;; supertype of `b`.  Driven from the members, not from `as × bs`: a
               ;; metatype has a handful where a closure has a chain's worth, and the
               ;; question is a set intersection whichever side it is read from.
               (some (fn [[m ms in-a]]
                       (let [in-b (filterv #(and (contains? bs %) (member-vis? m %)) ms)]
                         (some (fn [x] (some #(not= x %) in-b)) in-a)))
                     metas))))))))

(defn separating-partners
  "The types a **visible declaration** separates `a` from: every `y` such that some
  supertype of `a` is declared `(disjoint x y)` with `x` ≠ `y`, or shares a disjoint
  metatype with `y`.

  This is the enumeration `disjointness-test` is the membership test of, and the two
  read one frame so they cannot disagree.  Every type disjoint from `a` is a **subtype
  of one of these and nothing else is** — disjointness is inherited downward through
  `genl` and reaches a candidate no other way — so `(disjoint a ?t)` is answered by
  `specs` of this set.  What that buys is the bound: the answer is a function of the
  declarations, which are few, rather than of the vocabulary, which is not.

  Belief and context are the frame's, so a retracted declaration has already left
  `:disjoint-index` / `:metatype-members`, and a declaration the reader's context
  cannot see is dropped by the same visibility predicate that decides the pair for
  `disjoint?`.  The index is *not* itself context-scoped, which is why the filter is
  applied here rather than trusted to the lookup."
  [tax a context]
  (let [{:keys [seps metas pair-vis? member-vis?]} (separation-frame tax a context)]
    (persistent!
     (as-> (transient #{}) acc
       (reduce (fn [acc [x ys]]
                 (reduce (fn [acc y]
                           (if (and (not= x y) (pair-vis? x y)) (conj! acc y) acc))
                         acc ys))
               acc seps)
       (reduce (fn [acc [m ms in-a]]
                 (reduce (fn [acc y]
                           (if (and (member-vis? m y) (some #(not= % y) in-a))
                             (conj! acc y)
                             acc))
                         acc ms))
               acc metas)))))

(defn separating-pairs
  "Every **ordered** pair `[x y]`, `x` ≠ `y`, that a visible declaration separates —
  the declared pairs in both directions, plus each disjoint metatype's members against
  each other.

  `separating-partners` with neither side given, and it answers the same question for
  the goal that gives nothing away: `(disjoint ?x ?y)` is `specs(x) × specs(y)` over
  these.  Bounded by the declaration set by construction, which is what keeps a
  two-variable goal — a shape a user types by accident — from being a walk over the
  vocabulary squared."
  [tax context]
  (let [scoped? (scoped-context? context)
        t       @tax
        vis?    (if scoped? #(cache-entry-visible? tax % context) (fn [_] true))]
    (concat
     (for [s (:disjoint t)
           :let  [[x y] (declared-pair s)]
           :when (and (not= x y) (vis? [:disjoint s]))
           pair  [[x y] [y x]]]
       pair)
     (for [m  (:disjoint-metatypes t)
           :when (vis? [:metatype m])
           :let  [ms (filterv #(vis? [:member m %]) (get (:metatype-members t) m))]
           x  ms
           y  ms
           :when (not= x y)]
       [x y]))))

(defn disjoint?
  "Are types a and b provably disjoint?  True when some supertype of a and some
  *different* supertype of b are separated — either by a declared `(disjoint x y)`,
  or by both being members of one disjoint metatype.  Either way disjointness is
  inherited downward through genl (subtypes of disjoint types are disjoint), which
  is what the walk over both up-closures buys.

  The metatype arm is why no clique is stored: `(disjointMetatype M)` separates
  M's members by being *consulted*, not by materializing a `(disjoint a b)` per
  pair.  Only metatypes still marked are consulted, so unmarking one releases every
  pair it separated in a single step.  Being consulted is also what makes the arm
  *scopable* at all — a materialized clique would have frozen each pair in whatever
  context the expansion ran from.

  The context arity scopes on three levels: the two `genls` closures walk only
  visible edges, a `(disjoint x y)` pair counts only when some supporter's context
  is visible, and the metatype arm asks the same of the mark and of each of the two
  memberships.  Every added visibility probe sits *behind* an existing cheap
  membership guard, so the negative path — the overwhelming majority, since this
  runs on every unary assert — costs what the global read costs over the (smaller)
  scoped closures.

  Monotone on visibility by construction, and it must stay so: seeing more contexts
  can only add witnesses, never remove one.  That is what lets a descendant context
  detect a clash its ancestors cannot while the ancestors stay clean — the whole
  exposure story rests on it — so no closed-world arm (no \"not disjoint because I
  can see a reason they overlap\") may ever be added here."
  ([tax a b] ((disjointness-test tax a nil) b))
  ([tax a b context] ((disjointness-test tax a context) b)))

;; ---- disjointness witnesses: what a clash's joint visibility rests on ----

(defn- requirement
  "The context choices a supporting-context set imposes on a witness — nil when it
  imposes none (a supporter with no recorded context is seen from everywhere, so
  the ingredient never constrains the reader)."
  [cs]
  (when-not (contains? cs nil) (not-empty cs)))

(defn- path-requirements
  "Lazy seq of per-path requirement vectors from `sub` up to `tgt` over `:fwd` —
  one element per path, each a vector of context-choice sets, one per constraining
  edge on that path.  Reflexive: `sub` = `tgt` yields the single empty vector.
  Cycle-guarded, so a stray cycle terminates."
  [rel sub tgt seen]
  (if (= sub tgt)
    (list [])
    (lazy-seq
     (mapcat (fn [nxt]
               (when-not (contains? seen nxt)
                 (let [req (requirement (get (:edge-ctxs rel) [sub nxt] #{}))]
                   (map (fn [tail] (if req (into [req] tail) tail))
                        (path-requirements rel nxt tgt (conj seen sub))))))
             (get (:fwd rel) sub)))))

(defn- requirement-choices
  "Lazy cartesian product over requirement sets: each yield is one concrete witness
  context set — one context chosen per constraining ingredient."
  [reqs]
  (if (empty? reqs)
    (list #{})
    (for [c     (first reqs)
          rest* (requirement-choices (rest reqs))]
      (conj rest* c))))

(defn disjointness-witnesses
  "Lazy seq of **witness context sets** for the provable disjointness of `a` and
  `b`: each is the supporting contexts of one complete derivation — a genl path
  from `a` up to one separated type, a path from `b` up to the other, and the
  separating declaration (a `(disjoint x y)` pair, or a metatype mark plus both
  memberships).  A reader sees the clash iff it sees every context in *some*
  witness; a supporter with no recorded context imposes nothing and never appears.

  Lazy on every level — paths, separated pairs, and per-ingredient supporter
  choices can all multiply, and a node can have exponentially many ancestor paths
  — so a consumer that finds its witness early never pays for the tail.  Empty
  exactly when the pair is not globally disjoint, which is the cheap guard a
  caller runs first."
  [tax a b]
  (let [t       @tax
        rel     (:genl t)
        cctxs   (:cache-ctxs t)
        req     (fn [k] (requirement (get cctxs k #{})))
        pairs   (:disjoint t)
        members (:metatype-members t)
        as      (genls tax a)
        bs      (genls tax b)]
    (concat
     (for [x as, y bs
           :when (and (not= x y) (contains? pairs #{x y}))
           :let  [d (req [:disjoint #{x y}])]
           pa (path-requirements rel a x #{})
           pb (path-requirements rel b y #{})
           w  (requirement-choices (cond-> (into pa pb) d (conj d)))]
       w)
     (for [m (:disjoint-metatypes t)
           :let  [ms (get members m #{})]
           :when (seq ms)
           x as, y bs
           :when (and (not= x y) (contains? ms x) (contains? ms y))
           :let  [reqs (keep req [[:metatype m] [:member m x] [:member m y]])]
           pa (path-requirements rel a x #{})
           pb (path-requirements rel b y #{})
           w  (requirement-choices (into (into pa pb) reqs))]
       w))))

;; ---- predicate properties -----------------------------------------------

(defn mark-prop
  ([tax kind pred handle] (mark-prop tax kind pred handle nil))
  ([tax kind pred handle ctx]
   (let [k [:prop kind pred]]
     (swap! tax supported-add k handle ctx #(cache-install % k)))
   tax))
(defn unmark-prop! [tax kind pred handle]
  (let [k [:prop kind pred]]
    (swap! tax supported-del k handle #(cache-uninstall % k)))
  tax)
(defn has-prop?
  "Does `pred` carry property `kind` — anywhere, or (with `context`) declared from
  a context the reader can see?"
  ([tax kind pred] (contains? (get-in @tax [:props kind]) pred))
  ([tax kind pred context]
   (let [t @tax]
     (and (contains? (get-in t [:props kind]) pred)
          (or (not (scoped-context? context))
              (cache-entry-visible? tax [:prop kind pred] context))))))
(defn props "The set of predicates carrying property `kind`." [tax kind] (get-in @tax [:props kind] #{}))

(defn quoting-function?
  "Is `head` declared a `quotingFunction`?  Its arguments are a **mention**, held opaque
  to identity congruence (`res/representative-term` spelling mode)."
  [tax head]
  (and (symbol? head) (has-prop? tax :quoting head)))

(defn any-quoting-functions?
  "Cheap gate: does the KB declare any `quotingFunction`?  False ⇒ no mention position
  exists, so `res/representative-term` takes the ordinary full-representative walk with no
  per-node check.  An in-memory taxonomy-prop read, mirroring `nat/any-reifiable-functions?`."
  [tax]
  (boolean (seq (props tax :quoting))))

(defn props-over
  "`p` and every **super-predicate** of it carrying property `kind` — anywhere, or (with
  `context`) declared from a context the reader can see, walking only the `genl` edges
  visible from it.  Empty when none does.

  For the properties a violation is convicted **against**, and only those.  A `genl` edge
  between predicates says the sub's tuples *are* the super's, so a clash among the sub's
  tuples is a clash among the super's: `(fatherOf a b)` beside `(fatherOf b a)` breaks
  `(asymmetric parentOf)`, and two `fatherOf` mothers for one child are two `parentOf`
  values against `(functional parentOf)`.  Reading the mark off the exact functor made
  those bypassable through a sub-predicate door while the *converse probe* fanned down
  the same hierarchy, so which spelling arrived second decided whether the pair was
  found.

  **Not for the generative ones.**  `transitive`, `symmetric`, `reflexive` and
  `transitiveInArg` license tuples rather than refusing them, and a licence read for a
  predicate nobody declared it of manufactures knowledge — `inherit-test`'s
  `the-licence-stays-with-the-predicate-it-names` and `provers-test`'s
  `the-walk-reads-hops-through-the-subsumption-fan` pin that, and both call `has-prop?`
  for the goal's own predicate.  The direction is what separates the two families, and it
  is also why this walks **up** where `inverses-under` walks down: an inverse recorded on
  a sub-predicate is a hop of the super, and a constraint declared of a super binds the
  sub.

  The `:props` roster is empty for the kind on nearly every KB, so the common case is one
  map read and no closure walk — the gate `inverses-under` takes on the empty `:inverse`
  map, and it is what keeps a descending read off the goal paths that ask `has-prop?` per
  goal."
  ([tax kind p] (props-over tax kind p nil))
  ([tax kind p context]
   (let [marked (get-in @tax [:props kind])]
     (if (empty? marked)
       #{}
       (into #{}
             (comp (filter marked) (filter #(has-prop? tax kind % context)))
             (if (some? context) (genls tax p context) (genls tax p)))))))

(def closure-relations
  "The two relations whose transitive closure the engine caches and answers itself —
  `genl` and `genlCx`.  They are held **out** of the generic `:transitive` prop
  machinery, so a `(transitive genl)` fact stays queryable but *inert*: it never routes
  genl to the generic closure prover, never sets `has-prop? :transitive genl`, and the
  taxonomy answers genl-transitivity from its own cache as it always has.
  `provers/transitive-predicates` and `inherit/virtual-relations` are both this set, and
  `special`'s mark ingestion reads it as the skip-set."
  '#{genl genlCx})

(def arg-declaration-props
  "Per argument-constraint kind, the `:props` roster its **subject** is marked under —
  `(arg parentOf 1 person)` marks `parentOf` as declaring `arg`.

  A declaration constrains the tuples of every predicate beneath the one it names, so
  reading it means asking, per super-predicate of the sentence's own functor, whether it
  declares anything at all.  Asked of the index that is one argument-root probe per
  super per assert — proportional to how deep in the type hierarchy the predicate sits,
  on the path `assert` names its dominant per-fact cost.  Marked here it is a set
  membership, which is the same trade `(arity P n)` takes one screen up and for the same
  reason: a declaration is not something to re-derive per write.

  The roster is the **global** one, so a filter built on it is a superset of what any
  context can see; the scoped retrieval it gates is what decides which declarations
  actually speak for a reader."
  '{arg :declares-arg-isa, genlArg :declares-arg-genl, quotedArg :declares-quoted-arg,
    interArg :declares-inter-arg-isa})

;; The supporters behind a flat-cache entry, read back.  A consumer that *justifies*
;; something on a declaration needs the declaring sentexes as antecedents, and reading
;; them here beats re-querying the store for a sentence the cache was built from.
;; Every stored supporter is returned, believed or not: a justification's antecedents
;; are labelled by the JTMS, so handing it a defeated supporter is how a derivation
;; revives by itself when that supporter does.
(defn- cache-supporters [tax k] (into #{} (keys (get-in @tax [:cache-support k] {}))))
(defn prop-supporters
  "The **handles** of the sentexes declaring property `kind` of `pred`, as a set —
  every one of them, defeated members included, which is what lets a derivation resting
  on one revive by itself when that supporter does.

  Handles, not sentexes: the callers put these straight into a justification's
  antecedents, and a set has no order for such a list to inherit."
  [tax kind pred] (cache-supporters tax [:prop kind pred]))

(defn add-inverse
  ([tax p q handle] (add-inverse tax p q handle nil))
  ([tax p q handle ctx]
   (let [k (inverse-key p q)]
     (swap! tax supported-add k handle ctx #(cache-install % k)))
   tax))
(defn del-inverse! [tax p q handle]
  (let [k (inverse-key p q)]
    (swap! tax supported-del k handle #(cache-uninstall % k)))
  tax)
(defn add-arity
  ([tax pred n handle] (add-arity tax pred n handle nil))
  ([tax pred n handle ctx]
   (let [k [:arity pred n]]
     (swap! tax supported-add k handle ctx #(cache-install % k)))
   tax))
(defn del-arity! [tax pred n handle]
  (let [k [:arity pred n]]
    (swap! tax supported-del k handle #(cache-uninstall % k)))
  tax)
(defn arity-declarations
  "The whole `pred -> #{n}` declared-arity table, for a caller that needs to know
  whether the KB declares *any* arity at all, or whether the table has moved since it
  last looked.  One map read; never walked here."
  [tax] (get @tax :arity {}))

(defn declared-arity
  "The arity `pred` is declared with, or nil — anywhere, or (with `context`) declared
  from a context the reader can see.

  `(arity P n)` is a declaration the engine interprets, so it is cached here beside
  `transitive` and `inverse` rather than re-queried: the arity check runs on **every**
  assertion, and answering it from the index walked 16 candidate postings per
  assertion — 13.3M over an OpenCyc load, nearly all of them finding nothing, and 22%
  of the whole load's allocation.

  Nil when the KB has been told **two different arities** for one predicate.  That is
  not the same as being told nothing, but the answer to \"which arity does this
  predicate have\" is genuinely unsettled, and refusing an assertion on whichever of
  two contradictory declarations was found first would be arbitrary — open-world is
  the same stance the check takes toward a predicate nobody has declared.

  Scoped, that uniqueness is asked of what the reader can **see** rather than of the
  whole KB: two contexts declaring different arities leave each reader with one answer,
  and only a reader seeing both has none.  Testing uniqueness first and filtering after
  would instead let a declaration a reader cannot see suppress the one it can."
  ([tax pred] (declared-arity tax pred nil))
  ([tax pred context]
   (let [ns'  (get-in @tax [:arity pred])
         seen (if (scoped-context? context)
                (filterv #(cache-entry-visible? tax [:arity pred %] context) ns')
                (vec ns'))]
     (when (= 1 (count seen)) (first seen)))))

(defn inverses-of
  "**Every** predicate declared inverse to `p`, as a set — anywhere, or (with `context`)
  the ones declared from a context the reader can see.  Empty when none is.

  Nearly every predicate has none, so a caller probing per partner does one map read and
  no work; the set has more than one member only where a KB declared `(inverse P Q)` and
  `(inverse P R)`, which nothing refuses.  This is the reader a *step relation* wants —
  a hop somebody recorded on any declared partner is a hop, and answering off one of them
  would leave the others silently off the graph."
  ([tax p] (get-in @tax [:inverse p] #{}))
  ([tax p context]
   (let [qs (get-in @tax [:inverse p] #{})]
     ;; the empty case first, and it is the overwhelmingly common one: a transitive walk
     ;; asks this per node, so reaching `closure-of` before finding out there is no
     ;; partner would charge every ordinary walk a genlCx closure lookup per hop for
     ;; an answer that is empty either way
     (if (or (empty? qs) (not (scoped-context? context)))
       qs
       (into #{} (filter #(cache-entry-visible? tax (inverse-key p %) context)) qs)))))

(defn inverse-of
  "The declared inverse of `p`, or nil — anywhere, or (with `context`) declared
  from a context the reader can see.

  **One partner, chosen by content.**  A predicate may carry several declared inverses,
  and this answers the lexicographically smallest of them so the answer is a function of
  the knowledge rather than of the order it arrived in — the tie-break every other
  many-to-one read here takes, and for the reason the README gives.  A caller that must
  see all of them asks `inverses-of`; this one exists for the callers that want *a*
  partner (the applicability tests, the vocabulary reports) and are not walking a graph."
  ([tax p] (first (sort (inverses-of tax p))))
  ([tax p context] (first (sort (inverses-of tax p context)))))

(defn inverses-under
  "Every predicate declared inverse to `p` **or to a sub-predicate of `p`**, as a set —
  anywhere, or (with `context`) declared from a context the reader can see, walking
  only the `genl` edges visible from it.

  A hop somebody recorded on a partner of a sub-predicate is a hop of the super too:
  `(Q y x)` under `(inverse P' Q)` is `(P' x y)`, and a `P'` tuple is a `P` tuple by
  subsumption, however it is spelled.  A step relation or a swapped-goal delegate
  reading only `p`'s own partners leaves those edges silently off the graph — a claim
  then answers under the sub-predicate and not under its super, which no reading of
  `genl` admits.

  The `:inverse` map is empty for nearly every KB, so the common case is one map read
  and no closure walk; the spec closure is consulted only when some inverse exists."
  ([tax p] (inverses-under tax p nil))
  ([tax p context]
   (if (empty? (get @tax :inverse))
     #{}
     (let [ps  (if (some? context) (specs tax p context) (specs tax p))
           inv (if (some? context) #(inverses-of tax % context) #(inverses-of tax %))]
       (into #{} (mapcat inv) ps)))))

;; ---- what the taxonomy holds, declared ----------------------------------
;;
;; Three structures with three different bounds, which is why they are three rows and
;; not one.  The unscoped closure level has **no count bound at all** — it is retired by
;; a `:gen` bump rather than by size, so on a quiescent KB read from everywhere it grows
;; to the vocabulary and stays there.  The scoped level is capped per relation at
;; `*scoped-memo-budget*` distinct visibility sets.  The visibility index is bounded by
;; the context census, never by the read count.  A column of bare integers over the
;; three would say none of that.

(defn- memo-level
  "`f` applied to each relation's memo entry and summed — the shape all three counts
  take.  O(relations), and every `count` inside it is O(1) on a Clojure map, which is
  what keeps a polling page off the hierarchy itself."
  [kb f]
  (when-let [tax (:taxonomy kb)]
    (reduce + 0 (map (comp f val) @(:closure-memo @tax)))))

(defn- drop-memo-level
  "Empty one level of every relation's memo, `keys` naming the level's slots, and answer
  what went.  Safe at any moment: an entry is a memoized read, and the next read of it
  recomputes exactly what was dropped."
  [kb f ks]
  (let [n (or (memo-level kb f) 0)]
    (when-let [tax (:taxonomy kb)]
      (swap! (:closure-memo @tax)
             (fn [m] (reduce-kv (fn [acc rel e]
                                  (assoc acc rel (reduce #(assoc %1 %2 {}) e ks)))
                                {} m))))
    n))

(caches/register-cache
 {:cache    :taxonomy-closures
  :label    "Taxonomy closures"
  :scope    :kb
  :unit     "reach sets"
  :limit    nil
  :counters nil
  :note     (str "One reflexive-transitive reach set per type or context ever asked "
                 "about, up and down. Retired by a genl or genlCx edge changing — "
                 "a generation bump invalidates the level without touching it — and by "
                 "nothing else, so this is the one cache here with no count bound: it "
                 "grows to the vocabulary a reader has walked.")
  :read     (fn [kb] {:entries (memo-level kb #(+ (count (:fwd %)) (count (:rev %))))})
  :clear    (fn [kb] (drop-memo-level kb #(+ (count (:fwd %)) (count (:rev %)))
                                      [:fwd :rev]))})

(caches/register-cache
 {:cache    :taxonomy-scoped-closures
  :label    "Taxonomy closures, scoped"
  :scope    :kb
  :unit     "visibility sets"
  ;; a thunk for the reason the symbol pool's is: rebinding this var is the only way to
  ;; exercise the flush, so a bound captured at load would disagree with the one in force
  :limit    (fn [] *scoped-memo-budget*)
  :counters nil
  :note     (str "The same reach sets computed over only the edges one context can see, "
                 "held a level deeper under the visibility set that induced them. The "
                 "limit is per relation, and admitting one past it flushes the level "
                 "rather than growing it.")
  :read     (fn [kb] {:entries (memo-level kb #(count (:scoped %)))})
  :clear    (fn [kb] (drop-memo-level kb #(count (:scoped %)) [:scoped]))})

(caches/register-cache
 {:cache    :taxonomy-visibility
  :label    "Taxonomy visibility sets"
  :scope    :kb
  :unit     "relation/context pairs"
  :limit    nil
  :counters nil
  :note     (str "The interned set of asserting contexts each reader can see, one per "
                 "relation and context. Bounded by the context census rather than by "
                 "the read count, and recomputed when its stamp moves.")
  :read     (fn [kb] {:entries (some-> (:taxonomy kb) deref :vis-index deref count)})
  :clear    (fn [kb] (let [v (some-> (:taxonomy kb) deref :vis-index)
                           n (if v (count @v) 0)]
                       (some-> v (reset! {}))
                       n))})

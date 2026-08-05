;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.jtms
  "A non-monotonic truth-maintenance system.

  Each TMS *node* corresponds to a datum (a sentex handle) and records: its label
  (IN/OUT), whether it is a premise (and at what assumption *strength*), its
  derivation depth, the justifications that conclude it (:supports), and the
  justifications that use it as an antecedent (:consequences).

  A node holds **no reference to the sentex it labels** — only its handle.  The record
  store is where a sentex lives, so a copy here would be a second one to keep in step;
  and because this graph is always resident, a strong reference from it would hold every
  record in RAM, which on a paging backend defeats the paging entirely (measured: the
  nodes reached 50% of the record store).  A caller that needs the sentence fetches it
  by handle.

  Belief is a least fixpoint: a node is IN when it is a premise or has a valid
  justification (all antecedents IN) — EXCEPT that a node in the *defeated* set is
  forced OUT.  Because labels are computed from the current justification set and
  the current defeated set rather than accumulated as events arrive, belief is
  order-independent: asserting a defeater later withdraws a previously-drawn
  conclusion, and removing the defeater revives it.  That is the non-monotonic
  behaviour a plain monotone JTMS lacked.

  ## Two invariants

  **Order independence.** The same knowledge, given in any order, yields the same
  beliefs.  Every operation here recomputes labels from current state, so nothing
  depends on arrival order.  (The one place this can leak is a *tie-break* between
  two equally-strong beliefs: keying it on handle id would smuggle assertion order
  back in, so the contradiction layer keys it on content — see
  `vaelii.impl.solve/content-key`.)

  **Locality.** No operation recomputes the whole graph.  A change can only affect
  nodes downstream of it, so every relabel is scoped to the *affected region* — the
  forward consequence closure of whatever changed — with the rest of the graph held
  fixed as the boundary.  Cost is proportional to the region, not to the size of the
  KB, which is what lets belief maintenance scale.

  These two pull against each other, and the reconciliation is the whole design:
  a local fixpoint over the region, with boundary labels fixed, has a *unique*
  solution, and it is the same one a global fixpoint would produce.  See
  `relabel-region*`.

    * strength — every premise carries a strength (:monotonic / :default); every
      justification carries a *strength* too (:monotonic for a bare rule, :default for
      a defeasible one), capping the class it confers.  From these, `relabel` derives
      each IN node's *defeat-class* (monotonic > default, see
      vaelii.impl.strength).  Strength **propagates**: a justification confers no more
      than the weakest of its antecedents' classes, so a conclusion is never stronger
      than what it rests on.  That makes the class equation recursive, and
      `region-classes` solves it as a least fixpoint inside the region relabel.
      The class decides who loses a soft contradiction; the caller
      (core) owns the contradiction layer and pushes the losers into the defeated set
      with `defeat`.

    * defeated — a set of datums forced OUT by contradiction resolution.  It is
      *derived* (recomputed each settle by core), so `clear-defeats!` resets it and
      revival is automatic.

    * superseded — a *map* `datum -> reason` of datums displaced by an equality
      merge: the stale spelling of a fact whose terms have been rewritten to their
      class representative (docs/equality.md).  Three things make it its own state
      rather than a reuse of `defeated` or `blocked`:

      - `blocked` names *justifications*, and a directly asserted `(bornIn Dep
        Chicago)` is a **premise with no justification at all** — `region-fixpoint`
        seeds every premise IN unconditionally, so there is nothing for a block to
        invalidate.  Superseding has to act on the datum.
      - `defeated` would be the wrong reason.  A superseded spelling lost no
        argument; it was restated, and `why-not` must be able to say so — hence the
        map carries the displacing representative rather than being a bare set.
      - It is **not** a forced OUT inside the fixpoint.  A superseded datum stays in
        `:in` for the purposes of `valid?`, because its rewritten twin is justified
        *by it*: forcing it OUT structurally would invalidate the twin's own
        justification and the merge would believe neither spelling.  What
        supersession removes is *reported* belief — `in?` and `in-datums` subtract
        it — so the stale spelling stops matching, stops answering queries and stops
        entering nogoods, while everything derived from it stands.

      Retention is the point: the spelling is the **caller's premise**, so unlike an
      excepted conclusion it is never swept, and dropping the equality gives it back.
      Like `defeated` and `blocked` the map is *derived* — core recomputes it each
      settle from the equality closure — so belief stays order independent.

    * blocked — a set of *justification* ids whose rule's exception currently holds
      (`exceptWhen`, see docs/exceptions.md).  A blocked justification is not a
      defeated conclusion: it is simply **invalid**, so it supports nothing, confers
      no defeat-class, and does not make its consequence groundable — which is what
      lets the ordinary dependency-directed sweep garbage-collect an excepted
      conclusion instead of retaining it for revival.  This module is pure and has no
      KB, so it cannot run the exception query itself: the caller evaluates the
      exception and hands the answer in with `set-blocked`, which relabels only the
      region the change reaches.  Like `defeated`, the set is *derived* — computed
      from current state each settle, never accumulated — so belief stays order
      independent.

  Retraction is dependency-directed: drop the premise, relabel, then SWEEP the
  affected closure — datums that end up OUT with no valid support and are not
  defeated are solely supported by the retraction, so they (and their non-premise
  justifications) are returned for the caller to delete from the stores.  A datum that
  is merely *defeated* keeps its support and is retained for later revival.

  This module owns the in-memory graph; the caller owns physical deletion, since
  only it holds the stores."
  (:require [clojure.set :as set]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.protocols]
            [vaelii.impl.strength :as strength]))

;; A justification's `strength` is the defeat-class it confers, capping the derived
;; datum's class (:monotonic for a bare rule, :default for a defeasible one); `out` is
;; reserved for negation-as-failure antecedents (unused today, empty set).
(defrecord Justification [id informant antecedents consequence bindings strength out])

(defn ->just
  "Construct a Justification, defaulting `strength` to :monotonic and out to #{} (so a
  bare monotone justification behaves exactly as before — it adds no defeasibility of its
  own, and `conferred-class` caps it at its weakest antecedent)."
  ([id informant antecedents consequence bindings]
   (->just id informant antecedents consequence bindings :monotonic))
  ([id informant antecedents consequence bindings strength]
   (->Justification id informant antecedents consequence bindings (or strength :monotonic) #{})))

(defn graph-just
  "The part of a justification the **network** is made of — everything except the
  firing's `:bindings`.

  Belief never reads the bindings: `valid?` needs the antecedents, `conferred-class`
  the strength and the informant, and the region walks the consequence.  The bindings
  are the variable map of the firing that produced it, and only two readers want them
  — re-evaluating an `exceptWhen` query and a NAF antecedent per firing — both of
  which hold the KB and take the **record** from the store, where it is durable.  So
  the network keeps the graph and the store keeps the record, and the JTMS stops
  holding a second copy of every justification.  Measured (`lein bench-jtms`, a
  rules-heavy corpus at 3.6 justifications per node): 80 of 277 B each.

  It also **normalizes** — antecedents to a vector, `out` to a set, strength
  defaulted — so that however a caller spells a justification, the two
  representations store a value equal to each other's.  `:bindings` is nil rather
  than dropped, keeping the record shape fixed for every reader."
  [j]
  (->Justification (:id j) (:informant j) (vec (:antecedents j)) (:consequence j)
                   nil (or (:strength j) :monotonic) (set (:out j))))

;; ---- labelling ----------------------------------------------------------

(defn- ensure* [state datum depth]
  (update-in state [:nodes datum]
             (fn [n]
               (if n
                 (update n :depth min depth)
                 {:datum datum :premise? false
                  :depth depth :supports #{} :consequences #{}}))))

(defn- valid?
  "Is justification `j` currently satisfied under the IN set `in` and the blocked set
  `blocked`?

  Three independent conditions: every antecedent believed, no negation-as-failure
  antecedent believed (the `:out` slot, reserved and empty today), and the
  justification not blocked by its rule's exception."
  [j in blocked]
  (and (every? #(contains? in %) (:antecedents j))
       (not-any? #(contains? in %) (:out j))
       (not (contains? blocked (:id j)))))

(defn- conferred-class
  "The defeat-class a valid justification confers on its consequence: its own
  strength, capped by the *weakest* of its antecedents' classes.

  A conclusion can be no stronger than the weakest thing it rests on — a bare rule
  over a merely-default premise concludes a default, and the same rule over
  known-true facts concludes a monotonic, which is correct: it *is* monotonically
  entailed.

  The **informant is excluded from the cap**.  A rule is one of its own
  justification's antecedents, which is what makes retracting or defeating the rule
  withdraw everything it licensed — but that is a *validity* role, not a ground.
  Capping on it as well would fold the rule's assumption strength into every
  conclusion, and since `assert` gives a rule `:default` like anything else, that
  alone would put every derived datum at `:default`.  The strength a rule contributes
  is already carried by `:strength` on the justification (`:monotonic` for a bare
  rule, `:default` for a `set/defaultRule`)."
  [j classes]
  (reduce (fn [c a] (strength/min c (get classes a :default)))
          (or (:strength j) :monotonic)
          (remove #(= % (:informant j)) (:antecedents j))))

(defn- node-class
  "The defeat-class of an IN datum: the strongest support it has — its premise
  strength, and the class each currently-valid justification *confers* on it.

  A blocked justification is not valid, so it confers nothing: its strength is never
  read, exactly as if it were missing an antecedent."
  [state d in classes]
  (let [n       (get-in state [:nodes d])
        blocked (:blocked state #{})
        prem  (when (and (:premise? n) (not (contains? (:defeated state) d)))
                (:premise-strength n :default))
        strs  (for [jid (:supports n)
                    :let [j (get-in state [:justs jid])]
                    :when (and j (valid? j in blocked))]
                (conferred-class j classes))]
    (reduce strength/max :default (remove nil? (cons prem strs)))))

;; ---- region-local relabelling -------------------------------------------

(defn- affected-region
  "Every node whose label could change when `seeds` change: the forward closure over
  consequence justifications, seeds included.

  This is the claim locality rests on — a node's label is a function of its
  justifications' antecedents, so a node whose label can move is, by construction,
  reachable from whatever moved.  Everything outside the region is boundary: fixed,
  and never even looked at."
  [state seeds]
  (loop [seen #{}, stack (vec seeds)]
    (if (empty? stack)
      seen
      (let [d (peek stack), stack (pop stack)]
        (if (seen d)
          (recur seen stack)
          (recur (conj seen d)
                 (into stack (->> (get-in state [:nodes d :consequences])
                                  (map #(get-in state [:justs % :consequence]))
                                  (remove nil?)))))))))

(defn- region-fixpoint
  "Least fixpoint of IN over `region`, with `base` — the boundary's believed nodes —
  held fixed.  `forced-out?` forces a node OUT whatever its support (the defeated set
  when labelling; nothing when computing groundability).

  Blocking is *not* a forced-OUT: it invalidates a justification rather than a datum,
  so it is read through `valid?` and therefore applies to the groundability pass as
  well.  That is deliberate — an excepted conclusion has lost a derivation, not merely
  a belief, so the retraction sweep should collect it (docs/exceptions.md, \"Garbage
  collection, not defeat\").

  Starting from *nothing believed inside the region* and only ever adding is what
  keeps support well-founded: a cycle within the region that has no ground outside
  it never enters, exactly as in a global least fixpoint.  And a least fixpoint is
  unique, so the result cannot depend on the order nodes are visited — which is why
  going local costs no order independence."
  [state region cands base forced-out?]
  (let [blocked (:blocked state #{})
        justs   (:justs state)
        nodes   (:nodes state)
        seeded  (into base
                      (filter #(and (get-in state [:nodes % :premise?]) (not (forced-out? %))))
                      region)]
    ;; Semi-naive worklist.  `valid?` is monotone in `in` (blocked is fixed and the
    ;; reserved `:out` slot is empty), so a justification only needs re-testing when one
    ;; of its antecedents newly enters `in` — reached through `:consequences`, the stored
    ;; inverse of the antecedent edge.  Each justification is retried once per antecedent
    ;; that fires, not once per round: O(region edges), not O(region depth × cands).  The
    ;; result is the same unique least fixpoint, so locality and order independence hold.
    (loop [in    seeded
           stack (vec cands)]
      (if (empty? stack)
        in
        (let [j (peek stack), stack (pop stack), c (:consequence j)]
          (if (and (contains? region c)
                   (not (contains? in c))
                   (not (forced-out? c))
                   (valid? j in blocked))
            (recur (conj in c)
                   (into stack (keep justs) (get-in nodes [c :consequences])))
            (recur in stack)))))))

(defn- region-classes
  "Defeat-classes for `region` under the IN set `in`, as a **least fixpoint**.

  The class equation is recursive: a justification confers no more than the weakest
  of its antecedents' classes, so a node's class depends on its antecedents'.  A
  single pass over the region would therefore be wrong, and wrong in a way that looks
  fine — visited in one order it reads a not-yet-computed antecedent as bottom and
  under-rates the conclusion; visited in another it reads a stale, too-high value and
  over-rates it.  Either way the answer would depend on the traversal order, which is
  exactly what order independence forbids.

  So: every in-region IN node starts at `:default`, the bottom of the lattice, and
  the equation is iterated to stability.  The operator is monotone in the class
  lattice (`strength/max` and `strength/min` both are, and raising an antecedent's
  class can only raise what a justification confers), and the iteration starts at
  bottom, so it converges to the *least* fixpoint.  A least fixpoint is unique —
  hence independent of visit order, and of the order the knowledge arrived in.

  Nodes outside the region are boundary: their stored class is read and held fixed,
  just as their labels are.  A boundary node whose class could move would have an
  antecedent in the region and would therefore be in the region itself, so holding
  them fixed loses nothing."
  [state region in]
  (let [nodes   (:nodes state)
        justs   (:justs state)
        base    (reduce (fn [m d] (if (contains? in d) m (dissoc m d)))
                        (:classes state {}) region)
        members (filterv #(contains? in %) region)
        init    (reduce (fn [m d] (assoc m d :default)) base members)]
    ;; Worklist over the same monotone operator.  A node's class rises only when an
    ;; antecedent's rises, so a member is recomputed only when a node it derives from
    ;; moves — reached through `:consequences`.  Starting every member at :default
    ;; (bottom), this converges to the same unique least fixpoint a round-robin sweep
    ;; would, in O(region edges) rather than O(region depth × members); the class lattice
    ;; has height one, so each member's class changes at most once.  Uniqueness of the
    ;; least fixpoint is what keeps the answer independent of the order nodes are visited.
    (loop [classes init
           stack   (vec members)]
      (if (empty? stack)
        ;; drop the :default entries **of this region**.  Every read of this map already
        ;; defaults an absent datum to :default (it is the lattice's bottom), so storing
        ;; them says nothing — and on a KB whose content is mostly :default, which a
        ;; common-sense KB's is, they are nearly the whole map.  `defeat-class` is the one
        ;; reader that did not default, and it decides OUT-vs-absent from `:in` instead,
        ;; which is what it was really using the entry's presence to mean.
        ;;
        ;; Only the members are filtered, because only they were seeded at :default here:
        ;; every entry outside the region came from an earlier relabel that applied this
        ;; same filter, so the map already holds no :default anywhere else.  Rebuilding
        ;; the whole map instead would make a region relabel O(classes) — proportional to
        ;; the KB rather than to the region, which is the one thing locality forbids, and
        ;; it is invisible until a KB carries enough non-:default content for the map to
        ;; be large (an import of Cyc's monotonic assertions is exactly that).
        (reduce (fn [m d] (if (= :default (get m d)) (dissoc m d) m)) classes members)
        (let [d   (peek stack)
              stk (pop stack)
              cls (node-class state d in classes)]
          (if (= cls (get classes d))
            (recur classes stk)
            (recur (assoc classes d cls)
                   (into stk (comp (keep justs)
                                   (map :consequence)
                                   (filter #(contains? in %)))
                         (get-in nodes [d :consequences])))))))))

(defn- relabel-region*
  "Recompute `:in`, `:groundable` and the defeat-classes for `region`, holding every
  node outside it fixed.  Equivalent to a global relabel whenever the region is the
  affected closure of what changed, and proportional to the region rather than to
  the graph.

  Boundary classes need no recomputation either: a node's class depends on which of
  its justifications are valid and on those justifications' antecedents' classes, so
  a boundary node whose class could move would have an antecedent in the region — and
  would therefore be in the region itself."
  [state region]
  (let [defeated (:defeated state #{})
        old-in   (:in state #{})
        ;; the region members this window has not relabelled yet — their label right now
        ;; is their label before anything in the window moved, and that is the reading
        ;; `touched-in` wants.  A member relabelled earlier already contributed its own,
        ;; and the earlier one is the one that predates the window.
        fresh    (into #{} (remove (:touched state #{})) region)
        ;; only the justifications that can conclude something in the region matter
        cands    (into [] (comp (mapcat #(get-in state [:nodes % :supports] #{}))
                                (distinct)
                                (keep #(get-in state [:justs %])))
                       region)
        in       (region-fixpoint state region cands
                                  (set/difference old-in region)
                                  defeated)
        ground   (region-fixpoint state region cands
                                  (set/difference (:groundable state #{}) region)
                                  (constantly false))
        state    (assoc state :in in :groundable ground)]
    ;; Record the region as *touched*: a supporter's belief can flip only inside a
    ;; relabelled region, so the accumulated touched set is a superset of every handle
    ;; whose belief moved this settle — what `tax/refresh-beliefs` uses to skip a cache
    ;; no moved supporter touches.  Alongside
    ;; it, `touched-in` records which of them were **believed before** — so the two
    ;; together say which way each one moved, which the superset alone cannot.
    (-> state
        (assoc :classes (region-classes state region in))
        (update :touched (fnil into #{}) region)
        (update :touched-in (fnil into #{}) (filter old-in fresh)))))

(defn- resettle
  "Relabel the region affected by `seeds`."
  [state seeds]
  (relabel-region* state (affected-region state seeds)))

(defn- relabel-all*
  "Relabel every node.  Only for `recover`, which rebuilds the graph from the durable
  store and so has no smaller region to work from.

  The blocked set is **reset to empty first**.  Nothing about an exception is stored,
  so blocking cannot be read back from the durable store — it is derived state, and a
  rebuild that merged into whatever was there could only ever *add*, leaving a block
  standing for a justification whose exception no longer holds (or that no longer
  exists).  That is the bug docs/taxonomy.md records for the transitive closures.  So
  recovery starts unblocked and the caller re-evaluates the exceptions afterwards; the
  window in between believes an excepted conclusion, which the next settle withdraws."
  [state]
  ;; Supersession goes with it, and for the same reason: it is derived from the
  ;; equality closure, which `recover` rebuilds from the store afterwards.  A merge
  ;; inherited here could hold a spelling OUT for an equality no longer asserted.
  (let [state (assoc state :blocked #{} :superseded {})]
    (relabel-region* state (set (keys (:nodes state))))))

(defn- premise* [state datum strength-kw]
  (-> (ensure* state datum 0)
      (assoc-in [:nodes datum :premise?] true)
      (assoc-in [:nodes datum :premise-strength] (or strength-kw :default))
      (resettle [datum])))

(defn- add-just* [state j]
  (let [{:keys [id antecedents consequence] :as just} (graph-just j)
        state (-> state
                  (assoc-in [:justs id] just)
                  (update-in [:nodes consequence :supports] conj id)
                  (as-> s (reduce (fn [st a] (update-in st [:nodes a :consequences] conj id))
                                  s (concat antecedents (:out just)))))
        in    (:in state #{})]
    ;; Fast path — a *redundant* justification changes nothing, so skip the region relabel.
    ;; If `consequence` is already believed and this justification confers no stronger a
    ;; defeat-class than it already holds (or is not even valid), then belief, groundability
    ;; and every downstream class are unmoved: an already-IN node feeds its consequences
    ;; identically whether it rests on one witness or two.  This is what collapses a
    ;; recursive/cyclic forward load from O(derived²) to O(derived).  The `affected-region`
    ;; walk that dominated it happened *per re-derivation* — every alternate path to an
    ;; existing fact relabelled the fact's whole growing forward closure.  Now the closure is
    ;; walked once, when the fact is *first* derived (a brand-new node has no consequences
    ;; yet, so its region is a singleton and the relabel is O(log n)); every later
    ;; re-derivation via another path is a no-op.  Any *real* change still takes the full
    ;; resettle — a newly-IN consequence, a class that actually rises, a defeated/blocked one
    ;; (all of which move belief or class and so must reconcile the region) — so belief is
    ;; identical to the per-conclusion relabel, only cheaper.
    ;;
    ;; The consequence still enters `touched`, and that is not a hedge against the fast
    ;; path being wrong about belief.  A caller reading the window asks a slightly larger
    ;; question — *is what I published about this datum still current* — and a second
    ;; witness moves the answer to that while moving no label: `settle/record-clashes!`
    ;; republishes a standing clash's supporting justifications each settle and carries
    ;; the report forward for a pair the window does not hold, so a silent arrival is a
    ;; report naming fewer reasons than the KB holds.  Noting one handle is O(1) where
    ;; polling every standing pair for its support count is O(standing) per settle — which
    ;; `lein perf`'s `negation-arbitration` reads as a 19% worse growth ratio at 800
    ;; standing dilemmas, against no measurable change for this.  `touched-in` takes it too,
    ;; or the window would read as "newly believed" — but only when this window has not
    ;; relabelled it already, since an earlier relabel's answer is the one that predates
    ;; the window (`relabel-region*`'s `fresh`).
    (if (and (contains? in consequence)
             (or (not (valid? just in (:blocked state #{})))
                 (let [cls (get (:classes state) consequence :default)]
                   (= cls (strength/max cls (conferred-class just (:classes state)))))))
      (cond-> (update state :touched (fnil conj #{}) consequence)
        (not (contains? (:touched state #{}) consequence))
        (update :touched-in (fnil conj #{}) consequence))
      (resettle state [consequence]))))

;; ---- retraction ---------------------------------------------------------

(defn- dissoc-all
  "`(apply dissoc m ks)` in one transient pass.  `apply dissoc` walks the map once per
  key with a full HAMT path copy each time, and `dead` here is the whole swept region of
  a retraction — which is a routine path rather than a rare one, since an `exceptWhen`
  block runs the sweep on ordinary fact arrival."
  [m ks]
  (if (seq ks) (persistent! (reduce dissoc! (transient (or m {})) ks)) (or m {})))

(defn- disj-all
  "`(apply disj s ks)` in one transient pass, for the same reason as `dissoc-all`."
  [st ks]
  (if (seq ks) (persistent! (reduce disj! (transient (or st #{})) ks)) (or st #{})))

(defn- sweep*
  "SWEEP: collect the datums in `suspects` that are no longer *structurally*
  derivable (not groundable) and are not premises, delete them and every
  justification touching them, and return
  [new-state {:removed-sentexes [datum...] :removed-justifications [jid...]}].

  Groundability ignores defeats, so a defeated node with a surviving derivation is
  kept for revival, while a defeated node whose only support was just torn down is
  swept (no orphan leak).  Blocking, by contrast, *does* suppress groundability
  (see `region-fixpoint`), which is what makes this the garbage collector for an
  excepted conclusion as well as for a retracted one — docs/exceptions.md,
  \"Garbage collection, not defeat\".

  The caller must have relabelled `suspects` already: this reads `:groundable`, it
  does not compute it.

  Like every other operation here it is **region-local**: the justifications to tear
  down are read off the dead nodes' own `:supports` / `:consequences`, never found by
  scanning `:justs`.  That matters because `exceptWhen` blocks a justification on
  ordinary fact arrival, so sweeping is routine rather than a retraction-only path,
  and a sweep that scanned the whole graph would make a run of them quadratic."
  [state suspects]
  (let [groundable (:groundable state #{})
        dead     (filter (fn [d]
                           (and (not (get-in state [:nodes d :premise?]))
                                (not (contains? groundable d))))
                         suspects)
        ;; The justifications that touch a dead datum are exactly the ones its node
        ;; already names: `:supports` (it is their consequence) and `:consequences`
        ;; (it is one of their antecedents, or an :out antecedent).  Reading the two
        ;; adjacency sets keeps this proportional to the swept region — scanning
        ;; `:justs` instead would make every sweep cost the whole graph, which is the
        ;; locality invariant this module is built on (docs/nmtms.md).
        dead-jids (into #{}
                        (comp (mapcat (fn [d] (concat (get-in state [:nodes d :supports] #{})
                                                      (get-in state [:nodes d :consequences] #{}))))
                              ;; an adjacency set names a justification; only a live one
                              ;; is ours to remove or to report
                              (filter #(contains? (:justs state) %)))
                        dead)
        removed-justifications (remove #(= :premise (get-in state [:justs % :informant])) dead-jids)
        ;; the swept datums, as handles.  The caller fetches each one's record from the
        ;; store before deleting it — the store is where a sentex lives, and a copy kept
        ;; here would be a second one to keep in step (and, on a paging backend, would
        ;; hold every record resident).
        removed-sentexes   (vec dead)
        ;; 5. apply removals to the graph
        state (reduce (fn [st jid]
                        (let [{:keys [antecedents consequence out]} (get-in st [:justs jid])]
                          (-> st
                              (update :justs dissoc jid)
                              (update-in [:nodes consequence :supports] #(disj (or % #{}) jid))
                              (as-> s (reduce (fn [s2 a]
                                                (update-in s2 [:nodes a :consequences]
                                                           #(disj (or % #{}) jid)))
                                              s (concat antecedents out))))))
                      state dead-jids)
        state (update state :nodes dissoc-all dead)
        state (update state :classes dissoc-all dead)
        ;; a block names a justification, so a swept justification must lose its
        ;; block too — an id left behind would be a stale block waiting to be
        ;; reapplied to whatever reuses it
        state (update state :blocked disj-all dead-jids)
        ;; a supersession names a datum, so a swept datum must lose it too — an entry
        ;; left behind would hold a future handle OUT for a merge that is long gone
        state (update state :superseded dissoc-all dead)
        ;; the swept nodes were OUT and ungroundable, so dropping them cannot move
        ;; any survivor's label — only these bookkeeping sets need the removal
        state (update state :in         disj-all dead)
        state (update state :groundable disj-all dead)]
    [state {:removed-sentexes removed-sentexes
            :removed-justifications removed-justifications}]))

(defn- retract-known*
  [state datum]
  (let [;; 1. drop premise support for datum
        state    (-> state
                     (assoc-in [:nodes datum :premise?] false)
                     (update-in [:nodes datum] dissoc :premise-strength))
        ;; 2. MARK: the affected closure — also exactly the region to relabel, so
        ;;    marking and relabelling walk the graph once between them
        suspects (affected-region state [datum])
        ;; 3. relabel that region with datum no longer a premise (SAVE happens
        ;;    implicitly: a suspect with a surviving valid justification stays IN)
        state    (relabel-region* state suspects)]
    ;; 4-5. sweep what the retraction solely supported, and apply the removals
    (sweep* state suspects)))

(defn- suspend-premise*
  [state datum]
  (if-not (get-in state [:nodes datum])
    state
    (let [state (-> state
                    (assoc-in [:nodes datum :premise?] false)
                    (update-in [:nodes datum] dissoc :premise-strength))]
      (relabel-region* state (affected-region state [datum])))))

(defn- retract*
  "Return [new-state {:removed-sentexes [datum...] :removed-justifications [jid...]}].

  An unknown datum is a no-op: retraction is idempotent, and the test is what keeps it
  so.  Reaching `retract-known*` regardless would have `assoc-in` *create* the node it
  was asked to retract; the sweep then collects the phantom (not a premise, not
  groundable) and the result claims a removal that never happened."
  [state datum]
  (if-not (get-in state [:nodes datum])
    [state {:removed-sentexes [] :removed-justifications []}]
    (retract-known* state datum)))

(defn- set-blocked*
  [state jids]
  (let [jids    (set jids)
        was     (:blocked state #{})
        ;; only the justifications whose blocked status actually MOVED can change a
        ;; label, so they alone seed the region — the ones blocked in both sets are
        ;; already accounted for in the current labels
        changed (set/union (set/difference jids was) (set/difference was jids))]
    (if (empty? changed)
      state
      (-> state
          (assoc :blocked jids)
          (resettle (keep #(get-in state [:justs % :consequence]) changed))))))

(defn- swap-with-result!
  "Atomically apply `f` — a pure `state -> [state' result]` fn — to atom `a`,
  retrying on contention exactly as `swap!` does, and return the result.

  This replaces a deref-then-`reset!` shape that silently *discarded* any
  concurrent `swap!` landing between the deref and the reset — under incidental
  concurrency (a REPL thread beside the web handler) that was lost premises and
  justifications, not staleness.  Atomicity here makes concurrent operations
  compose; it does not make interleaved KB operations semantically serializable —
  the engine's contract is still one writer (docs/storage.md)."
  [a f]
  (loop []
    (let [old @a
          [new result] (f old)]
      (if (compare-and-set! a old new)
        result
        (recur)))))

;; ---- the representation seam --------------------------------------------

(defprotocol Tms
  "What a truth-maintenance network must answer, independent of how it stores the
  graph.  Two implementations ship: `RefTms` here — an atom over one persistent map,
  the reference — and `vaelii.impl.dense-jtms`, which holds the same graph in
  bitmaps and primitive-keyed maps.  Selected per KB (`open-kb`'s `:tms` opt),
  reference by default, and proven to answer identically by `jtms_dense_oracle_test`.

  The seam is at the *representation*, not at the algorithm: both implementations
  run the same least-fixpoint relabel over the same affected region, because that is
  the semantics, not an implementation detail.  What differs is where a node's
  premise flag, depth and adjacency live.

  Every method is named with a leading `-`; the plain names (`in?`, `add-premise`, …)
  are the public functions below, which dispatch here.  Callers use those."
  (-believed?        [tms datum] "Is `datum` believed (IN, minus supersession)?")
  (-believed         [tms]       "Seq of the believed datums, or nil when none.")
  (-node?            [tms datum] "Is there a node for `datum`?")
  (-datums           [tms]       "Seq of every datum with a node.")
  (-depth            [tms datum] "Derivation depth, 0 when unknown.")
  (-premise?         [tms datum] "Is `datum` a premise?")
  (-premise-strength [tms datum] "Its assumption strength, or nil.")
  (-defeat-class     [tms datum] "Defeat-class of an IN datum, nil when OUT.")
  (-defeated         [tms]       "The forced-OUT set.")
  (-blocked          [tms]       "The blocked justification-id set.")
  (-superseded       [tms]       "The `datum -> reason` supersession map.")
  (-touched          [tms]       "Datums whose region was relabelled since the reset.")
  (-touched-in       [tms]       "Of those, the ones already believed when first relabelled.")
  (-reset-touched    [tms]       "Clear the touched sets.")
  (-supports         [tms datum] "Justification ids concluding `datum`.")
  (-dependents       [tms datum] "Justification ids using `datum` as an antecedent.")
  (-justification    [tms jid]   "The graph justification (`graph-just` — no bindings), or nil.")
  (-justifications   [tms]       "Every live graph justification.")
  (-ensure-node      [tms datum depth] "Create the node if absent; lower its depth.")
  (-add-premise      [tms datum strength] "Mark `datum` a premise at `strength`.")
  (-suspend-premise  [tms datum] "Drop `datum`'s premise mark and relabel — no sweep.")
  (-add-justification [tms just] "Record `just` and relabel what it moves.")
  (-relabel          [tms]       "Whole-graph relabel (recover only).")
  (-defeat           [tms datums] "Force `datums` OUT and relabel their region.")
  (-clear-defeats    [tms]       "Empty the defeated set and relabel.")
  (-set-blocked      [tms jids]  "Replace the blocked set and relabel what moved.")
  (-update-blocked   [tms f]     "Apply `f` to the blocked set as one atomic step.")
  (-supersede        [tms m]     "Replace the supersession map (no relabel).")
  (-retract          [tms datum] "Drop the premise, relabel, sweep; return the removals.")
  (-sweep            [tms seeds] "Sweep the consequence closure of `seeds`.")
  (-snapshot         [tms]
    "The whole network as one canonical persistent map — `:nodes :justs :in
    :groundable :defeated :blocked :superseded :classes`.  This is the *comparison*
    shape the differential oracle checks and the shape `RefTms` happens to store; a
    dense implementation materializes it, so it is a debugging and testing surface,
    never something an engine path calls."))

;; ---- the reference implementation: one atom, one persistent map ---------

(deftype RefTms [^clojure.lang.Atom state]
  ;; `@tms` yields the state map, which is what the JTMS tests and the RAM benches
  ;; read.  It is the live map, not a copy — this implementation *is* the canonical
  ;; shape, so there is nothing to materialize.
  clojure.lang.IDeref
  (deref [_] @state)

  Tms
  (-believed? [_ datum]
    (let [s @state]
      (and (contains? (:in s #{}) datum)
           (not (contains? (:superseded s {}) datum)))))
  (-believed [_] (let [s @state] (seq (remove (:superseded s {}) (:in s #{})))))
  (-node? [_ datum] (contains? (:nodes @state) datum))
  (-datums [_] (keys (:nodes @state)))
  (-depth [_ datum] (get-in @state [:nodes datum :depth] 0))
  (-premise? [_ datum] (boolean (get-in @state [:nodes datum :premise?])))
  (-premise-strength [_ datum] (get-in @state [:nodes datum :premise-strength]))
  (-defeat-class [_ datum]
    (let [s @state]
      (when (contains? (:in s) datum) (get (:classes s) datum :default))))
  (-defeated [_] (:defeated @state #{}))
  (-blocked [_] (:blocked @state #{}))
  (-superseded [_] (:superseded @state {}))
  (-touched [_] (:touched @state #{}))
  (-touched-in [_] (:touched-in @state #{}))
  (-reset-touched [_] (swap! state assoc :touched #{} :touched-in #{}) nil)
  (-supports [_ datum] (get-in @state [:nodes datum :supports] #{}))
  (-dependents [_ datum] (get-in @state [:nodes datum :consequences] #{}))
  (-justification [_ jid] (get-in @state [:justs jid]))
  (-justifications [_] (vals (:justs @state)))
  (-ensure-node [_ datum depth]
    ;; skip the swap when it would write back a value-identical map — a node already
    ;; present at a depth no higher than `depth` is exactly what `ensure*` leaves
    ;; (`min` keeps the stored depth); this runs once per placement, so most calls
    ;; are that no-op.  Sound under the single-writer contract: nothing moves the
    ;; node between the read and the skipped write.
    (let [n (when observe/*chain-fast-paths* (get (:nodes @state) datum))]
      (when (or (nil? n) (< (long depth) (long (:depth n 0))))
        (swap! state ensure* datum depth)))
    nil)
  (-add-premise [_ datum strength] (swap! state premise* datum strength) nil)
  (-suspend-premise [_ datum] (swap! state suspend-premise* datum) nil)
  (-add-justification [_ just] (swap! state add-just* just) nil)
  (-relabel [_] (swap! state relabel-all*) nil)
  (-defeat [_ datums]
    (swap! state (fn [s] (-> s (update :defeated (fnil into #{}) datums) (resettle datums))))
    nil)
  (-clear-defeats [_]
    (swap! state (fn [s] (let [was (:defeated s #{})]
                           (-> s (assoc :defeated #{}) (resettle was)))))
    nil)
  (-set-blocked [_ jids] (swap! state set-blocked* jids) nil)
  (-update-blocked [_ f] (swap! state (fn [s] (set-blocked* s (f (:blocked s #{}))))) nil)
  (-supersede [_ m] (swap! state assoc :superseded (into {} m)) nil)
  (-retract [_ datum] (swap-with-result! state #(retract* % datum)))
  (-sweep [_ seeds] (swap-with-result! state (fn [s] (sweep* s (affected-region s seeds)))))
  (-snapshot [_] @state))

(defn create-tms
  "A fresh, empty truth-maintenance network — the reference implementation.

  `:in` is the believed set and the authority on belief — nodes carry no label of
  their own, so there is no second copy to drift.  `:groundable` is the set that is
  *structurally* derivable from the premises ignoring defeats: a defeated node that
  is still groundable can revive, one that is not has lost its last derivation and
  is swept.  Both are maintained region-locally.

  `:blocked` is the set of justification ids currently blocked by their rule's
  exception; it starts empty and only a caller that has evaluated the exceptions can
  fill it.

  (Rules live in the stores as sentexes, not here.)"
  []
  (->RefTms (atom {:nodes {} :justs {} :defeated #{} :blocked #{} :superseded {}
                   :classes {} :in #{} :groundable #{} :touched #{} :touched-in #{}})))

;; ---- public API ---------------------------------------------------------
;;
;; Thin dispatch onto the protocol.  Every engine path calls these, never a protocol
;; method directly, so the representation a KB was opened with is invisible above
;; this line.

(defn in?
  "Is `datum` believed?  Structural support minus supersession: a datum the equality
  layer has displaced keeps its place in the fixpoint (its twin is justified by it)
  but is not believed, so it stops matching and stops answering queries."
  [tms datum] (-believed? tms datum))

(defn depth  [tms datum] (-depth tms datum))
(defn known-datum?
  "Does the TMS hold a node for `datum`?  False for an **inert** sentex
  (`core/assert-inert`) — stored and indexed but never a TMS datum — which is how
  `retract!` tells a belief-bearing retraction from a direct teardown."
  [tms datum] (-node? tms datum))
(defn in-datums [tms] (-believed tms))
(defn premise? [tms datum] (-premise? tms datum))
(defn premise-strength [tms datum] (-premise-strength tms datum))
(defn datums [tms] (-datums tms))

(defn defeat-class
  "The current defeat-class of an IN datum (monotonic / default), or nil
  when the datum is OUT.  Valid after `relabel`.

  `:classes` holds only the datums *above* the lattice's bottom, so IN-ness is what
  separates \"OUT, hence no class\" from \"IN at the default class\".  An entry's mere
  presence cannot carry both, since only one of them is information."
  [tms datum] (-defeat-class tms datum))

(defn defeated?  [tms datum] (contains? (-defeated tms) datum))
(defn defeated   [tms] (-defeated tms))

(defn touched
  "The datums whose region has been relabelled since the last `reset-touched!` — a
  superset of every datum whose belief could have flipped in that window.  `settle`
  reads it to tell `tax/refresh-beliefs` which handles moved, so a cache no moved
  supporter touches is skipped.

  Plus the datums a **redundant** justification landed on, which is the one entry here
  whose belief provably did *not* move: the window is read as \"what I published about
  this datum may be out of date\", and a second witness for an already-believed
  conclusion moves that without moving a label (`add-just*` says why the alternative is
  worse).  Every consumer reads a superset, so an extra handle costs a re-derivation and
  never an answer."
  [tms] (-touched tms))

(defn touched-in
  "The subset of `touched` that was **already believed** when this window first
  relabelled it.  With `touched` and current belief that is the whole belief delta:
  a datum in `touched` and IN now but not here came *in*, and one here that is OUT now
  went *out*.  The superset alone cannot say which — most of a relabelled region does
  not move — so this is what a caller reporting consequences reads.

  \"When first relabelled\" is what makes it a reading from before the window rather
  than from part-way through it: a datum relabelled twice keeps the earlier answer."
  [tms] (-touched-in tms))

(defn reset-touched!
  "Clear the accumulated touched sets (see `touched` / `touched-in`).  `settle` clears
  them once it has read them, at the *end* — so the window a caller sees spans
  everything since the last settle finished, which for `edit` is the whole deferred
  batch and its one settle rather than the settle alone."
  [tms] (-reset-touched tms) tms)

(defn superseded
  "The `datum -> reason` map of spellings an equality merge has displaced."
  [tms] (-superseded tms))

(defn superseded? [tms datum] (contains? (-superseded tms) datum))

(defn supersession
  "Why `datum` is superseded — the representative that displaced it — or nil."
  [tms datum] (get (-superseded tms) datum))

(defn supersede
  "**Replace** the superseded map with `m` (`{datum reason}`).

  Replace, not accumulate, for the same reason `set-blocked` replaces: the caller
  recomputes the whole answer from the current equality closure each settle, so a
  supersession cannot outlive the merge that caused it and belief cannot depend on
  the order the merges arrived in.

  No relabel: supersession does not enter the fixpoint (see the namespace docstring),
  it only subtracts from what `in?` reports, so there is no region to recompute."
  [tms m] (observe/note-change) (-supersede tms m) tms)

(defn supports
  "Justification ids that conclude `datum` (its supporting justifications)."
  [tms datum] (-supports tms datum))

(defn dependents
  "Justification ids that use `datum` as an antecedent (or a defeater)."
  [tms datum] (-dependents tms datum))

(defn justification [tms jid] (-justification tms jid))
(defn justifications [tms] (-justifications tms))

(defn- indexed
  "`coll` as something `nth` reaches in constant time — itself when it already is one
  (an antecedent list is stored as a vector), a vector otherwise."
  ^clojure.lang.Indexed [coll]
  (if (instance? clojure.lang.Indexed coll) coll (vec coll)))

(defn- covered?
  "Is every one of `a`'s `na` elements among `b`'s `nb`? — the subset half, by index
  rather than by seq, so nothing is allocated to answer it."
  [^clojure.lang.Indexed a ^long na ^clojure.lang.Indexed b ^long nb]
  (loop [i 0]
    (if (>= i na)
      true
      (let [x (.nth a i)]
        (if (loop [j 0]
              (cond (>= j nb)          false
                    (= x (.nth b j))   true
                    :else              (recur (inc j))))
          (recur (inc i))
          false)))))

(defn- same-antecedents?
  "Do `a` and `b` name the same antecedents *as sets* — same members, order and
  duplicates immaterial?  Mutual containment, which is that definition read directly,
  and it allocates nothing where `(= (set a) (set b))` allocated two hash sets.

  The allocation matters because of **where this is asked**.  A conclusion re-derived
  by k witnesses is checked once per witness against every justification it holds so
  far, so the comparison runs Θ(k²) times per conclusion across a run.  Measured on the
  W4 join pyramid (10k, 65k derived facts): 7.7M comparisons for 429k justifications
  stored, and building those sets was the single largest line in the profile.

  An antecedent list is two to five handles, so a scan beats hashing one of them, and
  a mismatch — the common case, since a fresh witness is a fresh justification — ends
  at the first member `b` does not hold."
  [a b]
  (let [av (indexed a) na (count a)
        bv (indexed b) nb (count b)]
    (and (covered? av na bv nb)
         (covered? bv nb av na))))

(def ^:dynamic *dedup-cache*
  "`{:tms tms :m mutable-HashMap-of-consequence→HashSet-of-just-keys}`, or nil — the
  default, and `has-justification?` scans `-supports` as always.

  A **run-scoped index over the dedup question**.  A conclusion re-derived by k
  witnesses is asked about once per witness, and each ask scans every justification it
  already holds — Θ(k²) `same-antecedents?` comparisons per conclusion across a forward
  run, with a `-justification` fetch apiece (the W4 join pyramid at 1k: ~430k firings
  over ~66k conclusions, and the scan is the largest line in the profile).  Bound by
  `chain/chain` for the length of a run, the first ask per conclusion builds its key
  set from `-supports` once and every later ask is one hash probe.

  The binding carries the TMS it was built beside, and `dedup-cache-for` hands the
  map out only to that TMS: a nested run over a *second* KB (legal from a
  `:on-progress` callback) reaches these fns with the first KB's binding still in
  force, and handle spaces overlap, so an unscoped reuse would answer one KB's dedup
  question from the other's supports.  Anything but the owning TMS bypasses to the
  reference scan.

  Justification *existence* is structural, not belief: a label flip adds and removes
  nothing here, so no entry goes stale by belief moving — only by a justification
  being **removed**, which reaches the graph on exactly two paths (`retract!`,
  `sweep!`), and both clear the cache wholesale.  `add-justification` extends the
  entry it passes through, so a bound cache never disagrees with the graph it mirrors.
  The keys are handle-content — no canonicalization — so there is no canon stamp to
  carry (`observe/*handle-cache*`, which has one, says what that kind of stamp is
  for; the `:tms` slot here is identity, not currency)."
  nil)

(defn- dedup-cache-for
  "The bound dedup index's map when it mirrors `tms`, else nil (see `*dedup-cache*`)."
  ^java.util.HashMap [tms]
  (let [c *dedup-cache*]
    (when (and c (identical? (:tms c) tms)) (:m c))))

(defmacro with-dedup-cache
  "Run `body` with the justification dedup index engaged for `tms`; an outer cache
  over the *same* TMS is reused rather than shadowed — the composition
  `observe/with-handle-cache` makes — and one over another TMS is shadowed by a
  fresh map.  A no-op when `observe/*chain-fast-paths*` is bound false — the
  reference lever `chain_fast_paths_test` pulls."
  [tms & body]
  `(let [tms# ~tms]
     (binding [*dedup-cache* (or (let [c# *dedup-cache*]
                                   (when (and c# (identical? (:tms c#) tms#)) c#))
                                 (when observe/*chain-fast-paths*
                                   {:tms tms# :m (java.util.HashMap.)}))]
       ~@body)))

;; Both key shapes normalize fixnum boxing to Long: the HashMap/HashSet compare with
;; Java equals, where Integer 7 ≠ Long 7, and the reference scan compares with `=`,
;; where they are equal — every handle producer allocates Longs today, but the cache
;; is where a future Integer would silently split a key, so the coercion lives here
;; rather than as a convention.
(defn- unbox ^Object [x] (if (int? x) (long x) x))

(defn- just-key
  "The content `has-justification?` deduplicates on — the informant plus the
  antecedents **as a set**, `same-antecedents?`'s judgement (order and duplicates
  immaterial) frozen into one hashable value."
  [informant antecedents]
  [(unbox informant) (set antecedents)])

(defn- dedup-keys
  "The cached key set for `consequence`, built from its supports on the first ask."
  ^java.util.HashSet [tms ^java.util.Map cache consequence]
  (let [ck (unbox consequence)]
    (or (.get cache ck)
        (let [s (java.util.HashSet.)]
          (doseq [jid (-supports tms consequence)]
            (when-let [j (-justification tms jid)]
              (.add s (just-key (:informant j) (:antecedents j)))))
          (.put cache ck s)
          s))))

(defn has-justification?
  "Is there already a support for `consequence` from `informant` over exactly these
  antecedents (as a set)?  Guards against duplicate justifications.  Answered from
  the dedup index when one is bound for this TMS — the same judgement, one hash
  probe — and by the supports scan otherwise."
  [tms informant antecedents consequence]
  (if-let [^java.util.Map cache (dedup-cache-for tms)]
    (.contains (dedup-keys tms cache consequence) (just-key informant antecedents))
    (boolean
     (some (fn [jid]
             (let [j (-justification tms jid)]
               (and (= informant (:informant j))
                    (same-antecedents? antecedents (:antecedents j)))))
           (-supports tms consequence)))))

;; Every mutating entry point below bumps `observe/note-change` — the coarse clock a
;; cache derived from *belief* stamps itself with (the qualitative constraint networks
;; are the caller today).  It goes here, on the wrappers, rather than in the two `Tms`
;; implementations: the wrappers are the whole of how the engine reaches the network, so
;; one bump apiece is exhaustive by construction and neither representation can forget
;; one.  A call that turns out to move no label bumps anyway, which costs a re-derivation
;; and never a wrong answer.

(defn ensure-node [tms datum depth] (observe/note-change) (-ensure-node tms datum depth) datum)

(defn add-premise
  "Add `datum` as a premise at `strength` (default :default)."
  ([tms datum] (add-premise tms datum :default))
  ([tms datum strength-kw]
   (observe/note-change)
   (-add-premise tms datum (or strength-kw :default))
   datum))

(defn suspend-premise
  "Drop `datum`'s premise mark and relabel its region — a retraction's effect on
  **belief**, and nothing else.  Unknown datums no-op.

  `retract!` is this plus the sweep, and the sweep is exactly the part that cannot be
  put back: it deletes, so restoring the datum afterwards means re-deriving it at fresh
  handles.  Belief does not need it — a swept datum is OUT and ungroundable, so
  dropping it moves no label — which is what makes the pair (`suspend-premise`, then
  `add-premise` at the same strength) a reversible retraction.  `core/preview` is the
  caller: it answers what a removal would do to belief and then puts the premise back.

  Bare, not `!`, because nothing is lost: the node, its justifications and its record
  all stay exactly where they were."
  [tms datum] (observe/note-change) (-suspend-premise tms datum) datum)

(defn add-justification [tms just]
  (observe/note-change)
  (-add-justification tms just)
  ;; keep a bound dedup index in step: extend the one entry this justification lands
  ;; in, when that entry has been built (an absent entry rebuilds from `-supports`,
  ;; which now includes this justification, so absence needs nothing)
  (when-let [^java.util.Map cache (dedup-cache-for tms)]
    (when-let [^java.util.HashSet ks (.get cache (unbox (:consequence just)))]
      (.add ks (just-key (:informant just) (:antecedents just)))))
  just)

(defn relabel
  "Recompute *every* node's label and defeat-class.  This is the one whole-graph
  operation, and it exists for `recover`, which rebuilds the network from the durable
  store and therefore has no smaller region to start from.  Nothing on the assert /
  retract / settle path calls it.

  It also **clears the blocked set**: blocking is derived from exception queries that
  are never stored, so a rebuild cannot recover it and must not inherit a stale one.
  Recovery lands unblocked, and the caller re-evaluates."
  [tms] (observe/note-change) (-relabel tms) tms)

(defn defeat
  "Force `datums` OUT (contradiction resolution) and relabel the region they affect."
  [tms datums] (observe/note-change) (-defeat tms datums) tms)

(defn blocked
  "The justification ids currently blocked by their rule's exception."
  [tms] (-blocked tms))

(defn blocked?
  "Is justification `jid` currently blocked?"
  [tms jid] (contains? (-blocked tms) jid))

(defn set-blocked
  "Replace the blocked set with `jids` — the justifications whose exception the caller
  has just found to hold — and relabel the region the change reaches.

  The set is *replaced*, not accumulated: the caller re-evaluates every exception it
  cares about and states the whole answer, exactly as core recomputes the defeated set
  each settle.  Nothing here remembers that a justification was blocked a round ago,
  so belief cannot depend on the order the exceptions were discovered in.

  The region is seeded from the **consequences of the justifications whose blocked
  status changed** — blocking or unblocking j can only move j's conclusion and what
  follows from it — so cost is proportional to that region, not to the graph, and a
  call that changes nothing does no work at all.  `#{}` unblocks everything."
  [tms jids] (observe/note-change) (-set-blocked tms jids) tms)

(defn block
  "Add `jids` to the blocked set (a delta on `set-blocked`, for a caller that knows
  only what it just found rather than the whole answer).  Reads and writes in one
  step, so a delta cannot be computed against a set that has already moved."
  [tms jids] (observe/note-change) (-update-blocked tms #(into % jids)) tms)

(defn unblock
  "Remove `jids` from the blocked set."
  [tms jids] (observe/note-change) (-update-blocked tms #(reduce disj % jids)) tms)

(defn clear-defeats!
  "Reset the derived defeated set and relabel — the basis for revival.

  The region is the *previously* defeated nodes: lifting a forced OUT can only
  affect them and what follows from them, so a settle that defeated nothing last
  round does no work at all here."
  [tms] (observe/note-change) (-clear-defeats tms) tms)

(defn retract!
  "Dependency-directed retraction (drop premise / relabel / sweep).  Returns
  {:removed-sentexes [datum...] :removed-justifications [jid...]}.
  Unknown datums no-op (empty result): retraction is idempotent."
  [tms datum]
  (observe/note-change)
  ;; the one path besides `sweep!` that removes justifications — a bound dedup index
  ;; over this TMS is cleared wholesale rather than edited (see `*dedup-cache*`)
  (when-let [^java.util.Map c (dedup-cache-for tms)] (.clear c))
  (-retract tms datum))

(defn sweep!
  "Garbage-collect the consequence closure of `seeds`: every datum in it that is not
  a premise and is no longer *groundable* is deleted, along with the justifications
  touching it.  Returns the same shape as `retract!`, for the caller to apply to its
  own stores.

  This is `retract!`'s sweep without the retraction.  It exists because `exceptWhen`
  removes a conclusion by invalidating its justification rather than by withdrawing a
  premise: blocking suppresses groundability (`region-fixpoint`), so the conclusion is
  ungroundable and this collects it exactly as a retraction would — the trade
  docs/exceptions.md records under \"Garbage collection, not defeat\".

  Labels must already be current — `set-blocked` relabels the same region — so this
  only reads `:groundable`."
  [tms seeds]
  (observe/note-change)
  ;; removes justifications, so a bound dedup index over this TMS is cleared (see
  ;; `*dedup-cache*`)
  (when-let [^java.util.Map c (dedup-cache-for tms)] (.clear c))
  (-sweep tms seeds))

(defn snapshot
  "The network as one canonical persistent map (see `-snapshot`).  A testing and
  debugging surface — the differential oracle compares two implementations with it."
  [tms] (-snapshot tms))

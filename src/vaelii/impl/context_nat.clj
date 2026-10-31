;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.context-nat
  "The structural genlCx producer for reified-NAT contexts — docs/context-nat.md.

  A `(contextArgSubrelation F pos R)` declaration says two `F`-contexts are ordered by the
  sub-relation `R` at argument `pos`.  Two `F`-contexts are ordered when they differ only
  at declared positions and each differing argument of the sub is `R`-below the other's,
  the product order.  This namespace reads the declarations and the context NATs of `F`
  from the store and **materializes** each such `genlCx` edge as a **justified** sentex in
  CxUniverse, never a premise.  `R` is resolved by a bounded oracle: a registered pure
  comparator, else the `genlCx` closure for a sub-relation in `closure-orders` and each
  believed stored `(R a b)` fact."
  (:require [vaelii.impl.datetime :as datetime]
            [vaelii.impl.except :as exc]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.nat :as nat]
            [vaelii.impl.nat-read :as nat-read]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.special :as special]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]))

(def ^:private universal-context sx/root-context)

;; ---- the bounded R oracle -------------------------------------------------

(defn- comparator-holds?
  "True iff a registered comparator for `r` (`datetime/order-comparators`) answers that
  `a` is `R`-below `b`.  A comparator reads the two terms' shape alone, so the producer may
  call it inside the relabel loop."
  [r a b]
  (boolean (when-let [f (get datetime/order-comparators r)] (f a b))))

(def ^:private closure-orders
  "The sub-relations the `genlCx` closure answers between two contexts, before a stored
  fact: `genlMonad`, since a monad's time is Forever, so a monad that sees another is
  genlMonad-below it."
  #{'genlMonad})

(defn- r-evidence
  "The beliefs the relationship `a` `R`-below `b` rests on, one vector of handles per route
  that holds, empty when none does: `[[]]` when a comparator answers it (a pure function of
  the two expressions, already carried by the `natFormula` antecedents); else, for an `R`
  in `closure-orders`, one supporter per edge along a path from `a` up to `b` that `a` sees
  (`tax/reach-support`, a content-ordered walk), and the handle of each believed `(R a b)`
  fact, in context order.  Every route holding is a justification, so which arrived first
  decides none of them."
  [kb r a b]
  (if (comparator-holds? r a b)
    [[]]
    (concat
     (when (contains? closure-orders r)
       (let [tx (reasoning/taxonomy kb)]
         (when (and (not= a b) (tax/sees? tx a b))
           (some->> (tax/reach-support tx :genlCx a b a) (mapv first) not-empty vector))))
     (->> (kb/sentexes-matching kb (list r a b) '?ctx)
          (sort-by :context)
          (map #(vector (:id %)))))))

;; ---- reading the declarations and the context NATs ------------------------

(defn any-context-subrelations?
  "Presence check: does the KB declare any `contextArgSubrelation`?  The producer is a no-op
  otherwise — one O(1) functor count per assert, the shape `res/any-corresponding-predicates?`
  has."
  [kb]
  (pos? (reads/stored-count-with-functor (:index kb) 'contextArgSubrelation)))

(defn- subrelation-declarations
  "Believed `(contextArgSubrelation F pos R)` declarations as `[F pos R handle]`, kept
  where `(pred? F)` — all of them, or only those for one function.  A declaration is read
  as its own context believes it (`exc/believed-own?`): a computed edge is seen from every
  context, so a declaration a defeat hides where it is stated builds none."
  [kb pred?]
  (for [sx  (kb/sentexes-matching kb '(contextArgSubrelation ?f ?pos ?r) '?ctx)
        :let [[_ f pos r] (:sentence sx)]
        :when (and (pred? f) (exc/believed-own? kb (:id sx)))]
    [f pos r (:id sx)]))

(defn- context-nat-entry
  "`[k expr nat-formula-handle]` when `sx` is a believed `(natFormula K E)` map in
  CxUniverse with `K` a `cx/` constant and `E` an application of `f`, else nil."
  [kb f sx]
  (let [[_ k e] (:sentence sx)]
    (when (and (= universal-context (:context sx))
               (= 'natFormula (nm/functor (:sentence sx)))
               (jtms/in? (reasoning/tms kb) (:id sx))
               (nat-read/reified-context-symbol? k)
               (sequential? e) (= f (first e)))
      [k e (:id sx)])))

(defn- context-nats-of
  "Every believed context NAT whose expression head is `f`, as `context-nat-entry`'s
  triples, read through the inverted term index on `f`, which descends into a ground
  compound, so an expression's head is one of the sentex's posted terms.  A declaration's
  arrival reads this; a mint and an edge read `context-nats-naming`."
  [kb f]
  (->> (kb/find-sentexes kb f) (keep #(context-nat-entry kb f %)) distinct))

(defn- context-nats-naming
  "The believed context NATs of `f` whose expression names one of `terms`: one
  intersection of the term index on `f` and on each term (`kb/find-sentexes-all`)."
  [kb f terms]
  (->> terms
       (mapcat #(kb/find-sentexes-all kb [f %]))
       (keep #(context-nat-entry kb f %))
       distinct))

(defn- context-nat-of
  "The entry of the context NAT `k`'s own believed map, or nil: one argument-root read."
  [kb k]
  (some (fn [sx] (let [e (nth (:sentence sx) 2 nil)]
                   (when (sequential? e) (context-nat-entry kb (first e) sx))))
        (kb/sentexes-matching kb (list 'natFormula k '?e) universal-context)))

(defn- product-key
  "The identity of a context NAT's group under the declared positions `ps`: its expression
  with every argument at a position of `ps` masked, so two contexts share a key iff they
  agree on every undeclared argument.  `pos` is 1-based over the function's arguments,
  hence the expression index `pos` (index 0 is the functor).  A declared position past the
  expression's arity, which nothing at the assert entry point refuses, masks nothing."
  [expr ps]
  (reduce (fn [v pos] (if (and (integer? pos) (pos? (long pos)) (< (long pos) (count v)))
                        (assoc v pos '_)
                        v))
          (vec expr) ps))

(defn- declarations-by-position
  "`F`'s believed declarations as `{pos [[R declaration-handle] …]}`."
  [kb f]
  (reduce (fn [m [_ pos r declH]] (update m pos (fnil conj []) [r declH]))
          {} (subrelation-declarations kb #(= f %))))

;; ---- materialization ------------------------------------------------------

(defn- any-built?
  "Did one of the materializations `ms` add a justification?  Realizes every one."
  [ms]
  (reduce #(or %2 %1) false ms))

(defn- materialize-edge
  "Deduce `(genlCx sub super)` in CxUniverse, justified by `antes`, unless a violation
  refuses it (a genlCx edge over two `cx/` contexts is admissible except a self-edge, which
  the caller already excludes).  Idempotent: a second call with the same antecedents adds
  no justification, and a different route adds another supporter of the one edge.  What
  the edge shows the contexts under `sub` is the settle's (`special/drain-context-moves!`),
  as for an asserted or a concluded edge.  Returns true when it added a justification.

  Bare: it adds one derived sentex and one justification, and the JTMS withdraws the edge
  when an antecedent stops being believed — nothing here destroys stored knowledge, so
  nothing in this chain carries a `!`."
  [kb sub super antes]
  (let [edge (list 'genlCx sub super)
        tms  (reasoning/tms kb)]
    (when-not (special/inadmissible kb edge universal-context)
      (let [[h2 s2 new?] (kb/find-or-create-sentex kb edge universal-context)
            _            (when new? (special/derived-sentex-added kb s2 h2))
            depth        (inc (reduce max 0 (map #(jtms/depth tms %) antes)))
            antes        (vec antes)]
        (jtms/ensure-node tms h2 depth)
        (when-not (jtms/has-justification? tms 'contextArgSubrelation antes h2)
          (let [jid  (p/next-id (:records kb))
                just (jtms/->just jid 'contextArgSubrelation antes h2 {} :monotonic)]
            (p/put-justification (:records kb) just)
            (jtms/add-justification tms just)
            true))))))

(defn- pure-first
  "The positions `ps` with a comparator-resolved declaration first, so a pair fails on a
  shape read before a closure walk or a fact read."
  [decls ps]
  (sort-by (fn [pos] (if (some #(contains? datetime/order-comparators (first %)) (decls pos)) 0 1))
           ps))

(defn- pair-routes
  "The routes ordering the context of expression `esub` below that of `esup` under
  `decls` (`declarations-by-position`): one vector per choice, at each differing position,
  of a declaration and a route its `R` holds by there (`r-evidence`), holding each choice's
  declaration handle and evidence handles.  Empty when the two differ at a position `decls`
  names no declaration for, or at one where no declared `R` holds."
  [kb decls esub esup]
  (let [diff (filterv #(not= (nth esub %) (nth esup %)) (range 1 (count esub)))]
    (if (and (seq diff) (every? decls diff))
      (reduce (fn [routes pos]
                (let [a   (nth esub pos)
                      b   (nth esup pos)
                      evs (for [[r declH] (decls pos)
                                ev (r-evidence kb r a b)]
                            (into [declH] ev))]
                  (if (seq evs) (for [rt routes ev evs] (into rt ev)) (reduced ()))))
              [[]] (pure-first decls diff))
      ())))

(defn- reconcile-pairs
  "Materialize the structural genlCx edges of function `f` over the ordered pairs `pairs`
  gives, `(pairs decls)` → `[[k expr nat-formula-handle] …]` pairs, `decls` being
  `declarations-by-position`: each pair gets one justification per route
  (`pair-routes`), from both `natFormula` maps and the route.  Returns true when an edge
  gained a justification."
  [kb f pairs]
  (let [decls (declarations-by-position kb f)]
    (when (seq decls)
      (any-built?
       (for [[[ksub esub th-sub] [ksup esup th-sup]] (pairs decls)
             route (pair-routes kb decls esub esup)]
         (materialize-edge kb ksub ksup (into [th-sub th-sup] route)))))))

(defn- all-pairs
  "Every ordered pair of distinct contexts of `f` that agree on every undeclared argument
  (`product-key`): what a declaration arriving owes."
  [kb f]
  (fn [decls]
    (for [[_ nats] (group-by #(product-key (second %) (keys decls)) (context-nats-of kb f))
          x nats y nats :when (not= (first x) (first y))]
      [x y])))

(defn- comparable-terms
  "The terms the oracle can find `R`-below or `R`-above `a`, `a` among them, or nil when a
  comparator answers `R`, whose terms no index enumerates: for an `R` in
  `closure-orders`, the contexts above and below `a` in the unscoped `genlCx` closure, a
  superset of the scoped closure `r-evidence` decides a pair under; and the other end of
  every believed stored `(R a x)` and `(R x a)`."
  [kb r a]
  (when-not (contains? datetime/order-comparators r)
    (let [tx (reasoning/taxonomy kb)]
      (cond-> (-> #{a}
                  (into (map #(nth (:sentence %) 2)) (kb/sentexes-matching kb (list r a '?x) '?ctx))
                  (into (map #(nth (:sentence %) 1)) (kb/sentexes-matching kb (list r '?x a) '?ctx)))
        (and (symbol? a) (contains? closure-orders r))
        (-> (into (tax/context-up-global tx a)) (into (tax/context-down-global tx a)))))))

(defn- pairs-with
  "The pairs, each way, of the context NAT `k` with every other context of `f` that
  agrees with it on every undeclared argument and could be ordered against it: at the
  least declared position of `k`'s arity whose sub-relations no comparator answers, a
  context holding a term `comparable-terms` gives, read by term (`context-nats-naming`);
  with no such position, every context of `f`."
  [kb f k]
  (fn [decls]
    (when-let [[_ e _ :as m] (context-nat-of kb k)]
      (let [ks    (keys decls)
            key   (product-key e ks)
            p     (first (sort (for [[pos ds] decls
                                     :when (and (integer? pos) (< 0 (long pos) (count e))
                                                (not-any? #(contains? datetime/order-comparators (first %)) ds))]
                                 pos)))
            cands (if p
                    (let [ts (into #{} (mapcat #(comparable-terms kb (first %) (nth e p))) (decls p))]
                      (filter #(contains? ts (nth (second %) p nil)) (context-nats-naming kb f ts)))
                    (context-nats-of kb f))]
        (for [o cands
              :when (and (not= k (first o)) (= key (product-key (second o) ks)))
              pr [[m o] [o m]]]
          pr)))))

(defn- pairs-across
  "The pairs of `f`'s contexts that agree on every undeclared argument, whose sub holds, at a
  position `decls` orders by `r`, a term at or below `x`, and whose super holds one at or
  above `y` there: equal, or for an `r` in `closure-orders`, reached through the unscoped
  `genlCx` closure, a superset of the scoped closure `r-evidence` decides a pair under.  Each side is read by term (`context-nats-naming`), the sub side first,
  and an empty sub side reads no super side."
  [kb f r x y]
  (fn [decls]
    (let [ps     (for [[pos ds] decls :when (some #(= r (first %)) ds)] pos)
          tx     (reasoning/taxonomy kb)
          closed (and (contains? closure-orders r) (symbol? x) (symbol? y))
          side   (fn [ts] (filter (fn [[_ e]] (some #(contains? ts (nth e % nil)) ps))
                                  (context-nats-naming kb f ts)))
          subs   (side (cond-> #{x} closed (into (tax/context-down-global tx x))))]
      (when (seq subs)
        (let [ks   (keys decls)
              sups (group-by #(product-key (second %) ks)
                             (side (cond-> #{y} closed (into (tax/context-up-global tx y)))))]
          (for [s subs
                t (get sups (product-key (second s) ks))
                :when (not= (first s) (first t))]
            [s t]))))))

(defn- functions-ordered-by
  "The context functions some believed declaration orders by sub-relation `r`: the
  functions an `(R a b)` fact arriving after both contexts is new evidence in, since `R`
  is all the fact says about which function an edge belongs to."
  [kb r]
  (when (symbol? r)
    (distinct (for [[f _ r' _] (subrelation-declarations kb (constantly true))
                    :when (= r r')]
                f))))

(defn- reconcile-arrival
  "The pairs a believed `sentence` arriving can order:

  - a `(contextArgSubrelation F …)` declaration, every pair of `F`'s contexts;
  - a `(natFormula K E)` map with `K` a `cx/` constant, the mint of a context, the pairs
    `K` is in (`pairs-with`);
  - an `(R a b)` fact on a declared sub-relation, the pairs across `a` and `b`
    (`pairs-across`) in the functions declared to order by `R`; a `(genlCx a b)` edge,
    the same for each sub-relation in `closure-orders`.

  Any other sentence, including a fact stored into a `cx/` context that already exists,
  creates no pair and reconciles nothing.  Returns true when an edge gained a
  justification."
  [kb sentence]
  (when (and (sequential? sentence) (seq sentence))
    (let [[head x y] sentence]
      (cond
        (= 'contextArgSubrelation head)
        (reconcile-pairs kb x (all-pairs kb x))

        (and (= 'natFormula head) (nat-read/reified-context-symbol? x) (sequential? y) (seq y))
        (reconcile-pairs kb (first y) (pairs-with kb (first y) x))

        :else
        (any-built?
         (for [r (if (= 'genlCx head) closure-orders [head])
               f (functions-ordered-by kb r)]
           (reconcile-pairs kb f (pairs-across kb f r x y))))))))

(defn- reconcile-edge-move
  "What a `genlCx` edge `[a b]` a settle moved owes: an edge between two context NATs that
  is no longer believed, the pair `a`, `b` again, since a second route can hold it; any
  other edge `a` now sees `b` through, a computed one included, its arrival
  (`reconcile-arrival`).  An edge that left the closure owes nothing more, since each
  computed edge resting on it moves too."
  [kb [a b]]
  (if (and (nat-read/reified-context-symbol? a) (nat-read/reified-context-symbol? b)
           (not (some->> (kb/find-sentex-handle kb (list 'genlCx a b) universal-context)
                         (jtms/in? (reasoning/tms kb)))))
    (when-let [ea (context-nat-of kb a)]
      (when-let [eb (context-nat-of kb b)]
        (let [f (first (second ea))]
          (when (= f (first (second eb)))
            (reconcile-pairs kb f (constantly [[ea eb]]))))))
    (when (tax/sees? (reasoning/taxonomy kb) a b)
      (reconcile-arrival kb (list 'genlCx a b)))))

(defn- declared-heads
  "The functors whose sentences `reconcile-arrival` reads: `contextArgSubrelation`,
  `natFormula`, and every sub-relation a believed declaration names."
  [kb]
  (into '#{contextArgSubrelation natFormula}
        (map #(nth % 2)) (subrelation-declarations kb (constantly true))))

(defn- reconcile-moves*
  "`reconcile-moves` past its presence checks."
  [kb {:keys [edges arrived derived]}]
  (let [recs  (:records kb)
        tms   (reasoning/tms kb)
        heads (when (or (seq arrived) (seq derived)) (declared-heads kb))
        ss    (for [h (into (set arrived) (mapcat #(get derived %)) heads)
                    :let [s (some-> (p/get-sentex recs h) sx/sentence-of)]
                    :when (and (seq? s) (contains? heads (first s)) (jtms/in? tms h))]
                s)]
    (any-built?
     (concat (map #(reconcile-arrival kb %) (nm/sort-by-content-key identity (set ss)))
             (map #(reconcile-edge-move kb %) (sort-by (fn [e] (mapv nm/name-key e)) (set edges)))))))

(defn reconcile-moves
  "The structural genlCx maintenance the belief moves `moves` call for, once the write that
  moved them has settled.  `moves` is what `special/take-producer-moves!` answers:
  `:edges`, the `genlCx` edges the write's settles moved, each reconciled by
  `reconcile-edge-move`; `:arrived`, handles revived, and `:derived`, handles derived by
  functor, each read as an arrival when believed and of a functor `declared-heads` names.
  Edges and sentences are read in content order.  Local: the cost follows the moves and
  the contexts they name, never the context-NAT population.  Returns true when an edge
  gained a justification, which the caller settles."
  [kb {:keys [edges arrived derived] :as moves}]
  (when (and (or (seq edges) (seq arrived) (seq derived)) (any-context-subrelations? kb))
    (reconcile-moves* kb moves)))

(defn reconcile-genlCx
  "The structural-genlCx maintenance a just-asserted `sentence` and the belief moves of its
  write (`moves`, `reconcile-moves`) call for: the arrival of `sentence`
  (`reconcile-arrival`), a `genlCx` edge read with the moved edges once.  A no-op, one
  functor count, on a KB that declares no `contextArgSubrelation`.  Returns true when an
  edge gained a justification, which the caller settles."
  [kb sentence moves]
  (when (any-context-subrelations? kb)
    (let [edge? (and (sequential? sentence) (= 'genlCx (first sentence)) (= 3 (count sentence)))]
      (any-built?
       [(when-not edge? (reconcile-arrival kb sentence))
        (reconcile-moves* kb (cond-> moves edge? (update :edges (fnil conj #{}) (vec (rest sentence)))))]))))

(defn reconcile-revivals
  "The structural genlCx maintenance a teardown owes once its belief has settled: the
  belief moves of the teardown (`moves`, `reconcile-moves`), and the target of every
  `except` or `defeat` among the `removed` sentences, whose belief or visibility the removal
  gave back with no relabel.  Behind `nat/any-reified-constants?`.  Returns true when an edge
  gained a justification, which the caller settles."
  [kb moves removed]
  (when (nat/any-reified-constants? kb)
    (reconcile-moves kb (update moves :arrived (fnil into #{})
                                (keep #(or (kb/except-target %) (kb/defeat-target %)) removed)))))

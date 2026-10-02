;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.decide.arity
  "The arity family: a tuple whose length breaks the length a reader binds its functor
  to, and two predicates a `genl` edge relates whose own lengths differ.  See
  docs/nmtms.md, \"Nogoods decided at the reader\"."
  (:require [vaelii.impl.jtms :as jtms]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]))

;; ---- arity ---------------------------------------------------------------
;;
;; A tuple of `Q` whose length breaks the length `Q` is bound to is a one-member nogood,
;; and two predicates a predicate `genl` edge relates whose own lengths differ are a
;; nogood of their bindings.  The bindings are the roster spellings, read as storage:
;; `(arity P n)`, an exact-arity class membership, a `variable_arity` membership and
;; `(arityMin P m)`.  The candidate index keeps them under `::bindings`, the stored
;; tuple shapes under `::shapes`, and the shapes some stored binding breaks under
;; `::cand-shapes`; `:arity` holds the tuples of those shapes and `:arity-pairs` the
;; bindings of the pairs in `::pairs`.  Four keys are derived from those and kept with
;; them, so a binding arriving touches only the types below it: `::exact-of` (each
;; predicate's exact lengths), `::lengths` (the exact lengths bound at or above each type
;; below a binding), `::pairs-by` (the pairs by lower end, with `::pair-count` per end)
;; and `::at-conflict` (the functors whose own length differs from one above them).

(def ^:private variable-arity-classes
  "The memberships that release a relation from one exact length."
  '#{variable_arity variable_arity_predicate variable_arity_function})

(def ^:private tracked-limit
  "How many tuples of one shape `::shapes` keeps the handles of.  Past it the shape is
  `:many`, and a shape that becomes a candidate reads its tuples off the functor posting."
  64)

(defn- binding-of
  "`[P kind value]` for the sentence of a stored fact that binds a relation's length, else
  nil: `(arity P n)` and an exact-arity class membership bind `:exact n`, a
  `variable_arity` membership `:var`, and `(arityMin P m)` `:min m`."
  [s]
  (when (seq? s)
    (let [[f p v] s
          n       (count s)]
      (when (and (symbol? f) (symbol? p) (not (sx/variable? p)))
        (cond
          (and (= 3 n) (= 'arity f) (integer? v) (pos? v))    [p :exact v]
          (and (= 3 n) (= 'arityMin f) (integer? v) (pos? v)) [p :min v]
          (and (= 2 n) (tax/exact-arity-classes f))           [p :exact (tax/exact-arity-classes f)]
          (and (= 2 n) (variable-arity-classes f))            [p :var nil])))))

(defn- fact-shape
  "`[q n]` for a stored fact `sx` whose sentence is a positive tuple of `n` arguments with
  a symbol functor, else nil."
  [sx]
  (let [s (:sentence sx)]
    (when (and (nil? (:antecedent sx)) (seq? s) (<= 2 (count s)))
      (let [f (first s)]
        (when (and (symbol? f) (not= 'not f) (not (sx/variable? f)))
          [f (dec (count s))])))))

(defn- own-values
  "The `kind` values `bindings` (`{P {h [kind value context]}}`) stores of `p`."
  [bindings p kind]
  (into #{} (keep (fn [[_ [k v]]] (when (= k kind) v))) (get bindings p)))

(defn- shape-handles
  "The stored tuples of shape `[q n]`: the handles `::shapes` tracks, or for a `:many`
  shape the functor posting filtered by length."
  [kb cands [q n :as shape]]
  (let [t (get-in cands [::shapes q n])]
    (if (set? t)
      t
      (into #{} (filter #(= shape (some-> (p/get-sentex (:records kb) %) fact-shape)))
            (reads/as-stored-with-functor (:index kb) q)))))

(defn- with-binding
  "`c` with the binding `h` of `p`, `b` = `[kind value context]`, stored (`stored?`) or
  removed, `p`'s exact lengths in `::exact-of` kept with it, and `h` in `:arity-pairs`
  while `p` is an end of a pair."
  [c p h b stored?]
  (let [c  (if stored?
             (assoc-in c [::bindings p h] b)
             (let [c (update-in c [::bindings p] dissoc h)]
               (if (empty? (get-in c [::bindings p])) (update c ::bindings dissoc p) c)))
        ns (own-values (::bindings c) p :exact)
        c  (if (seq ns)
             (assoc-in c [::exact-of p] ns)
             (cond-> c (contains? (::exact-of c) p) (update ::exact-of dissoc p)))]
    (cond
      (not stored?)                        (cond-> c (:arity-pairs c) (update :arity-pairs disj h))
      (and (= :exact (first b))
           (pos? (get-in c [::pair-count p] 0))) (update c :arity-pairs (fnil conj #{}) h)
      :else                                c)))

(defn- count-end
  "`c` with the pair count of `q` moved by `d`: `q`'s exact bindings enter `:arity-pairs`
  when it becomes an end of a pair, and leave when it stops being one."
  [c q d]
  (let [k  (get-in c [::pair-count q] 0)
        k' (+ k d)
        hs (fn [] (for [[h [kind]] (get-in c [::bindings q]) :when (= :exact kind)] h))
        c  (if (zero? k') (update c ::pair-count dissoc q) (assoc-in c [::pair-count q] k'))]
    (cond
      (and (zero? k) (pos? k')) (update c :arity-pairs (fnil into #{}) (hs))
      (and (pos? k) (zero? k')) (update c :arity-pairs #(reduce disj % (hs)))
      :else                     c)))

(defn- set-pairs
  "`c` with the pairs whose lower end is `f` replaced by the set `new`, in `::pairs`, by
  lower end in `::pairs-by`, and in the pair counts of their ends."
  [c f new]
  (let [old (get-in c [::pairs-by f] #{})
        new (or new #{})]
    (if (= old new)
      c
      (let [gone (remove new old)
            came (remove old new)
            c    (-> c
                     (update ::pairs #(into (reduce disj (or % #{}) gone) came))
                     (update ::pairs-by #(if (seq new) (assoc % f new) (dissoc % f))))
            c    (reduce #(count-end %1 %2 -1) c (mapcat identity gone))]
        (reduce #(count-end %1 %2 1) c (mapcat identity came))))))

(defn- spread-lengths
  "`[c changed]`: `c` with the exact lengths `ns` added to `::lengths` of `t` and of every
  type below it missing one, and the set of types that gained one.  The walk down stops at
  a type holding all of `ns`, since every type below it holds them too."
  [w c t ns]
  (let [ls      (::lengths c)
        changed ((:specs-global-while w) t (fn [f] (let [l (get ls f)] (some #(not (contains? l %)) ns))))]
    [(if (seq changed)
       (assoc c ::lengths (persistent! (reduce (fn [m f] (assoc! m f (if-let [l (get m f)] (into l ns) ns)))
                                               (transient (or ls {})) changed)))
       c)
     changed]))

(defn- relength
  "`c` with `::lengths` of every type in `region` read again from the taxonomy, the exact
  lengths bound at or above each (`tax/genls-global-union`), one memo across `region`: a
  region below a length or an edge that left."
  [w c region]
  (let [xf   (mapcat (::exact-of c {}))
        memo (volatile! {})]
    (assoc c ::lengths
           (persistent!
            (reduce (fn [m f] (let [l ((:genls-global-union w) f xf memo)]
                                (if (seq l) (assoc! m f l) (dissoc! m f))))
                    (transient (or (::lengths c) {})) region)))))

(defn- recompute-arity
  "`c` with the arity candidates of the functors `fs` recomputed from `::lengths`, the exact
  lengths bound at or above each functor.  `extra` is nil, or a delay of the predicates
  bound to a length above the upper end of a `genl` edge stored but not yet installed.  A
  shape `[f n]` is a candidate when a length above `f` is not `n` or `f`'s `arityMin` is
  above `n`.  An `f` is in `::at-conflict` when it binds two lengths or one that differs
  from a length above it, and only such an `f` reads the predicates above it to name its
  pairs `[f g]`: `g` above `f` storing a different exact length.  An `f` binding one
  length reads the predicates binding another (`tax/genls-global-union`, a memo per
  length across `fs`), and one binding two reads every bound one (`tax/genls-global-among`,
  `memo`), through the write view `w` (`decide/write-view`)."
  [kb w c fs extra memo]
  (let [by-length (volatile! {})]
    (reduce
     (fn [c f]
       (if (and (empty? (get-in c [::shapes f])) (empty? (get-in c [::bindings f]))
                (empty? (get-in c [::pairs-by f])))
         ;; no tuple, no binding and no pair: nothing of `f` can change
         c
         (let [exact-of  (::exact-of c)
               above     (get-in c [::lengths f])
               mins      (own-values (::bindings c) f :min)
               c         (reduce
                          (fn [c n]
                            (let [shape [f n]
                                  was?  (contains? (::cand-shapes c) shape)
                                  now?  (boolean (or (some #(not= n %) above) (some #(> % n) mins)))]
                              (cond
                                (= was? now?) c
                                now?  (-> c
                                          (update ::cand-shapes (fnil conj #{}) shape)
                                          (update :arity (fnil into #{}) (shape-handles kb c shape)))
                                :else (-> c
                                          (update ::cand-shapes disj shape)
                                          (update :arity #(reduce disj % (shape-handles kb c shape)))))))
                          c (keys (get-in c [::shapes f])))
               own       (get exact-of f)
               conflict? (boolean (and (seq own) (or (< 1 (count own)) (some #(not= (first own) %) above))))
               c         (cond
                           conflict?                            (update c ::at-conflict (fnil conj #{}) f)
                           (contains? (::at-conflict c) f)      (update c ::at-conflict disj f)
                           :else                                c)]
           (set-pairs c f (when conflict?
                            (into #{}
                                  (keep (fn [g]
                                          (let [og (get exact-of g)]
                                            (when (and (not= g f) (seq og)
                                                       (some (fn [a] (some #(not= a %) og)) own))
                                              [f g]))))
                                  (if (< 1 (count own))
                                    (into ((:genls-global-among w) f exact-of memo)
                                          (some-> extra deref))
                                    ;; one length `a`: the predicates that pair with `f` are
                                    ;; those binding a length other than `a`, and the cut to
                                    ;; them holds those alone, where the cut to every bound
                                    ;; predicate is the closure once every type binds one
                                    (let [a     (first own)
                                          other (fn [g] (some #(not= a %) (get exact-of g)))
                                          m     (or (get @by-length a)
                                                    (let [m (volatile! {})] (vswap! by-length assoc a m) m))]
                                      (into ((:genls-global-union w) f (filter other) m)
                                            (filter other) (some-> extra deref))))))))))
     c fs)))

(defn- conflicts-below
  "The functors of `::at-conflict` below `t`, other than those in `skip`."
  [w c t skip]
  (into #{} (filter #(and (not (contains? skip %)) (or (= t %) ((:genl?-global w) % t))))
        (::at-conflict c)))

(defn- length-arrived
  "`c` after the exact length `n` arrives at `p`, which bound no `n` before: `n` spreads
  down from `p` to the types missing it (`spread-lengths`), which are recomputed with `p`.
  A functor below `p` that already held `n` keeps its shapes, and its pairs change only by
  `[f p]`, and only when it is in `::at-conflict`, so those are joined without a
  recompute."
  [kb w c p n]
  (let [[c changed] (spread-lengths w c p #{n})
        c           (recompute-arity kb w c (conj changed p) nil (volatile! {}))
        ex          (::exact-of c)
        op          (get ex p)]
    (reduce (fn [c f]
              (let [o (get ex f)]
                (if (some (fn [a] (some #(not= a %) op)) o)
                  (set-pairs c f (conj (get-in c [::pairs-by f] #{}) [f p]))
                  c)))
            c (conflicts-below w c p (conj changed p)))))

(defn- edge-arrived
  "`c` after the `genl` edge `sub`→`super` is stored and before it is installed: the
  lengths at or above `super` spread down from `sub`, the types that gained one are
  recomputed, and so is each functor below `sub` in `::at-conflict`, with the predicates
  bound above `super` as `extra`.  `c` unchanged when no length is bound at or above
  `super`: the edge then brings no length and no pair."
  [kb w c sub super]
  (if-let [ls (not-empty (get-in c [::lengths super]))]
    (let [[c changed] (spread-lengths w c sub ls)
          memo        (volatile! {})
          extra       (delay ((:genls-global-among w) super (::exact-of c) memo))]
      (recompute-arity kb w c (into changed (conflicts-below w c sub changed)) extra memo))
    c))

(defn- region-left
  "`c` after a length or an edge above every type of `region` leaves: the region's lengths
  are read again (`relength`) and every functor in it recomputed."
  [kb w c region]
  (recompute-arity kb w (relength w c region) region nil (volatile! {})))

(defn- arity-rebuilt
  "`c`, whose `::bindings` and `::exact-of` a replay filled, with `::lengths` spread from
  every exact binding and the candidates of every tracked functor and bound predicate
  computed, one memo across them."
  [kb w c]
  (let [c (reduce (fn [c [p ns]] (first (spread-lengths w c p ns)))
                  (dissoc c ::lengths) (::exact-of c))]
    (recompute-arity kb w c (into (set (keys (::shapes c))) (keys (::bindings c))) nil (volatile! {}))))

(defn- note-arity!
  "Keep the arity candidates in step with the fact `sx` arriving (`stored?` true) or
  leaving.  A tuple is tracked under its shape, and a tuple of a candidate shape enters
  `:arity`; a new shape is tested against `::lengths` and the functor's `arityMin`.  An
  exact length arriving at a predicate spreads to the types below it that miss it
  (`length-arrived`), and an edge arriving, a `genl` edge or a cover's edge per part
  (`tax/installed-edges`), spreads its upper end's lengths below its lower end
  (`edge-arrived`, while any exact length is bound).  A length or an edge leaving
  reads the lengths of the types below it again (`region-left`), and a binding that moves
  no length recomputes its own predicate.  An edge is not installed when its record
  is stored, so its arrival reads the upper end's lengths from `::lengths`; a departing
  edge may still be installed, which leaves a superset.  During a replay (`replay?`) a
  new shape is not tested and a binding is only recorded: `arity-rebuilt` computes the
  candidates once."
  [kb w sx stored? replay?]
  (let [cands (reasoning/nogood-candidates kb)
        h     (:id sx)
        s     (:sentence sx)]
    (when-let [[q n :as shape] (fact-shape sx)]
      (let [c @cands
            t (get-in c [::shapes q n])]
        (if stored?
          (when (or (not= :many t) (contains? (::cand-shapes c) shape))
            (swap! cands
                   (fn [c]
                     (let [t  (get-in c [::shapes q n])
                           c  (cond
                                (nil? t) (assoc-in c [::shapes q n] #{h})
                                (= :many t) c
                                (<= tracked-limit (count t)) (assoc-in c [::shapes q n] :many)
                                :else (update-in c [::shapes q n] conj h))
                           c  (if (and (nil? t) (not replay?) (seq (::bindings c))
                                       (or (some #(not= n %) (get-in c [::lengths q]))
                                           (some #(> % n) (own-values (::bindings c) q :min))))
                                (update c ::cand-shapes (fnil conj #{}) shape)
                                c)]
                       (if (contains? (::cand-shapes c) shape)
                         (update c :arity (fnil conj #{}) h)
                         c)))))
          (when (or (set? t) (contains? (:arity c) h))
            (swap! cands
                   (fn [c]
                     (let [t (get-in c [::shapes q n])
                           c (update c :arity #(some-> % (disj h)))]
                       (cond
                         (not (set? t)) c
                         (= #{h} t)     (-> c
                                            (update ::shapes (fn [m] (let [m (update m q dissoc n)]
                                                                       (if (empty? (get m q)) (dissoc m q) m))))
                                            (update ::cand-shapes #(some-> % (disj shape))))
                         :else          (update-in c [::shapes q n] disj h)))))))))
    (if replay?
      (when-let [[p kind v] (binding-of s)]
        (when (and stored? (nil? (:antecedent sx)))
          (swap! cands with-binding p h [kind v (:context sx)] true)))
      (do
        (when-let [[p kind v] (binding-of s)]
          (when (nil? (:antecedent sx))
            (swap! cands (fn [c]
                           (let [had? (contains? (get-in c [::exact-of p]) v)
                                 c    (with-binding c p h [kind v (:context sx)] stored?)
                                 has? (contains? (get-in c [::exact-of p]) v)]
                             (cond
                               (and (= :exact kind) (not had?) has?)
                               (length-arrived kb w c p v)

                               (and (= :exact kind) had? (not has?))
                               (region-left kb w c ((:specs-global w) p))

                               :else
                               (recompute-arity kb w c #{p} nil (volatile! {}))))))))
        (when (and (nil? (:antecedent sx)) (seq (::exact-of @cands)))
          (doseq [[sub super] (tax/installed-edges s)
                  :when (and (symbol? super) (not= sub super))]
            (swap! cands #(if stored?
                            (edge-arrived kb w % sub super)
                            (region-left kb w % ((:specs-global w) sub))))))))))

(defn- visible-bindings
  "`{:exact {n #{h}} :min {m #{h}} :var #{h}}`: the bindings of `p` a reader with ancestor
  set `up` reads, each IN, stated in `up` and not `hidden?`."
  [kb bindings p up hidden?]
  (let [tms (reasoning/tms kb)]
    (reduce (fn [m [h [kind v c]]]
              (if (and (or (nil? c) (contains? up c)) (jtms/in? tms h)
                       (not (and hidden? (hidden? h))))
                (if (= :var kind)
                  (update m :var (fnil conj #{}) h)
                  (update-in m [kind v] (fnil conj #{}) h))
                m))
            {} (get bindings p))))

(def ^:dynamic *arity-pass*
  "A volatile while a settle reads many readers' withdrawals: the cut of each functor's
  global closure to the bound predicates (`bound-above`), which reads no reader, and the
  reach answers of the cuts and of the pairs (`arity-nogoods`), kept for every reader of
  the settle.  nil otherwise, and each `arity-nogoods` call keeps its own."
  nil)

(defn- arity-entry
  "`*arity-pass*`'s entry for the taxonomy `tax` and `bindings` under its current `genl`
  generation, installed fresh when the pass holds none for them: `{:key :bound :memo
  :reach :pairs :neighbours :shapes}`.  The key holds `tax` itself, since a detached copy
  (`tax/detached-copy`) that moves an edge reaches the live taxonomy's next generation
  over other edges.  `:neighbours` is the scoped walks' neighbour cache
  (`tax/with-neighbours`), which a set scope filters by the edges' contexts alone, so the
  generation keys it; `:shapes` is each candidate tuple's `[context q n]`, read off its
  record once, which a handle never changes.  A new one, not kept, with no pass bound."
  [tax bindings]
  (let [k    [tax (tax/relation-gen tax :genl) bindings]
        pass *arity-pass*
        hit  (when pass
               (let [e @pass
                     [t g b] (:key e)]
                 (when (and e (identical? tax t) (= (second k) g) (identical? bindings b))
                   e)))]
    (or hit
        (let [e {:key   k
                 :bound (into #{} (keep (fn [[p hs]] (when (some (fn [[_ [kind]]] (not= :min kind)) hs) p)))
                              bindings)
                 :memo  (volatile! {})
                 :reach (volatile! {})
                 :pairs (volatile! {})
                 :neighbours (atom {})
                 :shapes (volatile! {})}]
          (when pass (vreset! pass e))
          e))))

(defn- bound-above
  "`(fn [q up])` → the predicates above `q`, `q` left out, holding an exact or
  `variable_arity` binding in `bindings`, that a reader with ancestor set `up` reaches
  over the `genl` edges stated in `up`: `q`'s global closure cut to the bound predicates
  (`tax/genls-global-among`), each kept when `up` holds every context asserting a `genl`
  edge or reaches it, read for the whole cut off one walk up from `q`
  (`tax/genls-asserted-among` over `tax/asserting-contexts-in`), with no closure built.
  The cut, its memo and the reach answers are kept in `*arity-pass*` (`arity-entry`)
  while the taxonomy, its `genl` generation and `bindings` are the ones they were read
  under."
  [tax bindings]
  (let [e      (arity-entry tax bindings)
        scopes (volatile! {})
        reach  (:reach e)]
    (fn [q up]
      (let [cut   (disj (tax/genls-global-among tax q (:bound e) (:memo e)) q)
            scope (if-let [x (find @scopes up)]
                    (val x)
                    (let [x (tax/asserting-contexts-in tax :genl up)] (vswap! scopes assoc up x) x))]
        (if (or (nil? scope) (empty? cut))
          cut
          (let [k [scope q]
                r (get @reach k ::absent)]
            (if (identical? ::absent r)
              (let [r (tax/with-neighbours (:neighbours e) #(tax/genls-asserted-among tax q cut scope))]
                (vswap! reach assoc k r) r)
              r)))))))

(defn- reader-binding
  "What binds `q`'s length at a reader, as `{:exact n :grounds #{h}}` or `{:min m :grounds
  #{h}}`, or nil.  `q`'s own bindings come first: a `variable_arity` membership leaves
  only a single `arityMin` floor, one exact length binds it and two leave it unbound.  A
  `q` with no own binding takes the one exact length the predicates above it through
  edges stated in `up` agree on, unless one of them is `variable_arity`: the bound
  predicates above it that `up` reaches (`above`, `bound-above`'s fn)."
  [kb bindings above q up hidden?]
  (let [own (visible-bindings kb bindings q up hidden?)]
    (cond
      (seq (:var own))
      (when (= 1 (count (:min own)))
        (let [[m hs] (first (:min own))] {:min m :grounds hs}))

      (seq (:exact own))
      (when (= 1 (count (:exact own)))
        (let [[n hs] (first (:exact own))] {:exact n :grounds hs}))

      :else
      ;; the predicates above grouped by the exact lengths they store, the smallest group
      ;; first: a second length visible leaves `q` unbound, so the rest go unread
      (let [cut    (above q up)
            by-len (reduce (fn [m p] (reduce #(update %1 %2 (fnil conj []) p) m
                                             (own-values bindings p :exact)))
                           {} cut)
            seen   (volatile! {})
            vis    (fn [p] (if-let [e (find @seen p)]
                             (val e)
                             (let [b (visible-bindings kb bindings p up hidden?)]
                               (vswap! seen assoc p b) b)))
            ns     (reduce (fn [acc [n ps]]
                             (if (some #(contains? (:exact (vis %)) n) ps)
                               (cond-> (conj acc n) (seq acc) reduced)
                               acc))
                           #{} (sort-by (comp count val) by-len))
            n      (first ns)]
        (when (and (= 1 (count ns))
                   (not-any? #(and (some (fn [[_ [k]]] (= :var k)) (get bindings %))
                                   (seq (:var (vis %))))
                             cut))
          {:exact n :grounds (into #{} (mapcat #(get (:exact (vis %)) n)) (get by-len n))})))))

(defn- breaks?
  "Does a tuple of `n` arguments break `binding`?"
  [binding n]
  (boolean (or (and (:exact binding) (not= n (:exact binding)))
               (and (:min binding) (< n (:min binding))))))

(defn- arity-nogoods
  "The arity nogoods a reader with ancestor set `up` reads: each candidate tuple it sees
  whose length breaks `reader-binding`, `{:members #{h} :marks grounds :kind :arity}`, and
  each pair in `::pairs` whose lower predicate reaches the upper through edges stated in
  `up` and whose own visible exact lengths differ, neither `variable_arity`, `{:members
  bindings :marks #{} :kind :arity-descension}`."
  [kb cands up hidden?]
  (let [bs    (::bindings cands)
        recs  (:records kb)
        tax   (reasoning/taxonomy kb)
        above (delay (bound-above tax bs))
        scope (delay (tax/asserting-contexts-in tax :genl up))
        e     (delay (arity-entry tax bs))
        ;; a candidate's record read once for every reader of the pass
        shape (fn [h]
                (let [m (:shapes @e)]
                  (if-let [x (find @m h)]
                    (val x)
                    (let [x (when-let [sx (p/get-sentex recs h)]
                              (into [(:context sx)] (fact-shape sx)))]
                      (vswap! m assoc h x)
                      x))))
        ;; every pair of `f` is answered off one walk up from `f`, kept for the pass
        reach (let [among (volatile! {})]
                (fn [f g sc]
                  (let [a  (or (get @among f)
                               (let [a (into #{} (map second) (get-in cands [::pairs-by f]))]
                                 (vswap! among assoc f a) a))
                        k  [sc f a]
                        pr (:pairs @e)
                        r  (get @pr k ::absent)
                        r  (if (identical? ::absent r)
                             (let [r (tax/with-neighbours (:neighbours @e) #(tax/genls-asserted-among tax f a sc))]
                               (vswap! pr assoc k r) r)
                             r)]
                    (if (contains? a g) (contains? r g) (tax/genl-asserted-in? tax f g sc)))))
        memo  (volatile! {})
        bind  (fn [q] (if-let [e (find @memo q)]
                        (val e)
                        (let [b (reader-binding kb bs @above q up hidden?)] (vswap! memo assoc q b) b)))
        ;; an upper end is the end of many pairs: its bindings are read once per call
        seen  (volatile! {})
        vis   (fn [p] (if-let [e (find @seen p)]
                        (val e)
                        (let [b (visible-bindings kb bs p up hidden?)] (vswap! seen assoc p b) b)))]
    (concat
     ;; a shape's binding is read once, and only the tuples of a shape it breaks: the
     ;; tracked handles, or a `:many` shape's off the functor posting
     (for [[q n] (::cand-shapes cands)
           :let [b (bind q)]
           :when (and b (breaks? b n))
           h (let [t (get-in cands [::shapes q n])]
               (if (set? t) t (reads/as-stored-with-functor (:index kb) q)))
           :when (contains? (:arity cands) h)
           :let [[c _ m :as x] (shape h)]
           :when (and x (= n m) (or (nil? c) (contains? up c))
                      (not (and hidden? (hidden? h))))]
       {:members #{h} :marks (:grounds b) :kind :arity})
     (for [[f g] (::pairs cands)
           :let [bf (vis f)
                 bg (vis g)]
           :when (and (empty? (:var bf)) (empty? (:var bg))
                      (= 1 (count (:exact bf))) (= 1 (count (:exact bg)))
                      (not= (key (first (:exact bf))) (key (first (:exact bg)))))
           ;; a pair holds `g` in `f`'s global closure, which is `up`'s when `up` holds
           ;; every context asserting a `genl` edge; walked last, for the pairs whose
           ;; visible lengths differ
           :when (let [sc @scope] (or (nil? sc) (reach f g sc)))]
       {:members (into (val (first (:exact bf))) (val (first (:exact bg))))
        :marks   #{}
        :kind    :arity-descension}))))

(defn arity-grounds
  "The bindings a reader with ancestor set `up` convicts the tuple `sentence` through, as
  a set of handles, empty when it convicts none: `reader-binding`'s `:grounds`."
  [kb sentence up hidden?]
  (let [[q n] (fact-shape {:sentence sentence})
        bs    (::bindings @(reasoning/nogood-candidates kb))
        b     (when q (reader-binding kb bs (bound-above (reasoning/taxonomy kb) bs) q up hidden?))]
    (if (and b (breaks? b n)) (:grounds b) #{})))

(def family
  "The arity family's entry in `decide/registry`.  The bindings are read as well as the
  candidates, so a binding moving re-decides a reader (`decide/reach-handles`)."
  {:note!     note-arity!
   :replayed  arity-rebuilt
   :handles   (fn [c] (concat (:arity c) (:arity-pairs c)))
   :watched   (fn [c] (mapcat keys (vals (::bindings c))))
   :live?     (fn [_ c] (or (seq (:arity c)) (seq (:arity-pairs c))))
   :unstamped #{::shapes ::exact-of ::lengths ::pairs-by ::pair-count ::at-conflict}
   :nogoods   arity-nogoods
   :pass      #'*arity-pass*})

;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.decide.arity
  "The arity family: a tuple whose length breaks the length a reader binds its functor
  to, and two predicates a `genl` edge relates whose own lengths differ, each placed as a
  conclusion (`chain/place-arities!`).  See docs/nmtms.md, \"A nogood placed as a
  conclusion\"."
  (:require [vaelii.impl.caches :as caches]
            [vaelii.impl.journal :as journal]
            [vaelii.impl.jtms :as jtms]
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
;; `(arityMin P m)`.  The candidate index keeps them under `::bindings`, each binding's
;; predicate under `::binding-of`, and the shapes some stored binding breaks under
;; `::cand-shapes`, a shape's lengths read off the shape roster
;; (`reads/as-stored-shape-lengths`); `:arity` holds the tuples of those shapes and `:arity-pairs` the
;; bindings of the pairs in `::pairs`.  Four keys are derived from those and kept with
;; them, so a binding arriving touches only the types below it: `::exact-of` (each
;; predicate's exact lengths), `::lengths` (the exact lengths bound at or above each type
;; below a binding), `::pairs-by` (the pairs by lower end, with `::pair-count` per end)
;; and `::at-conflict` (the functors whose own length differs from one above them).
;; `::conflict-up` holds every type at or above a functor of `::at-conflict`, closed upward
;; over the edges active at the `genl` generation `::conflict-gen`, so the functors under a
;; conflict below a type are read by a walk down that enters only its types.

(def ^:private variable-arity-classes
  "The memberships that release a relation from one exact length."
  '#{variable_arity variable_arity_predicate variable_arity_function})

(def ^:private binding-functors
  "The functors of a binding (`binding-of`), in content order."
  (into (sorted-set) cat [['arity 'arityMin] (keys tax/exact-arity-classes) variable-arity-classes]))

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

(defn- noted
  "`c` with the handles `hs` journaled (`journal/note`) and queued under `::moved` for the
  settle to place their nogoods again (`take-moved!`)."
  [c hs]
  (-> (journal/note c hs) (update ::moved (fnil into #{}) hs)))

(defn- note-placement-left!
  "Queue the arity candidates and bindings a `(contradicts …)` sentex `sx` leaving the store
  names, so the settle places their nogoods where they stand (`take-moved!`): a `genlCx`
  edge under the placement can have left with it."
  [kb sx]
  (let [s (:sentence sx)]
    (when (and (seq? s) (= 'contradicts (first s)))
      (let [cands (reasoning/nogood-candidates kb)
            c     @cands
            hs    (into #{} (comp (keep sx/handle-id)
                                  (filter #(or (contains? (:arity c) %) (contains? (::binding-of c) %))))
                        (rest s))]
        (when (seq hs)
          (swap! cands update ::moved (fnil into #{}) hs))))))

(defn- shape-handles
  "The stored tuples of shape `[q n]`: the functor's extent filtered by length."
  [kb [q _ :as shape]]
  (into #{} (filter #(= shape (some-> (p/get-sentex (:records kb) %) fact-shape)))
        (reads/as-stored-with-functor (:index kb) q)))

(defn- candidate-shape?
  "Does a tuple of `n` arguments of `q` break a length `c`'s `::lengths` holds at or above
  `q`, or an `arityMin` of `q`?"
  [c q n]
  (boolean (or (some #(not= n %) (get-in c [::lengths q]))
               (some #(> % n) (own-values (::bindings c) q :min)))))

(defn- with-binding
  "`c` with the binding `h` of `p`, `b` = `[kind value context]`, stored (`stored?`) or
  removed, `p`'s exact lengths in `::exact-of` kept with it, and `h` in `:arity-pairs`
  while `p` is an end of a pair."
  [c p h b stored?]
  (let [c  (noted c [h])
        c  (if stored?
             (-> c (assoc-in [::bindings p h] b) (assoc-in [::binding-of h] p))
             (let [c (-> c (update-in [::bindings p] dissoc h) (update ::binding-of dissoc h))]
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
      (and (zero? k) (pos? k')) (-> c (update :arity-pairs (fnil into #{}) (hs)) (noted (hs)))
      (and (pos? k) (zero? k')) (-> c (update :arity-pairs #(reduce disj % (hs))) (noted (hs)))
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

(defn- conflict-raised
  "`c` with the types above `f` added to `::conflict-up`, the walk up stopping at a type
  the set holds; `c` unchanged while the set is unbuilt (`conflict-up-current`)."
  [w c f]
  (if-let [up (when (::conflict-gen c) (::conflict-up c))]
    (assoc c ::conflict-up (into up ((:genls-global-while w) f #(or (= f %) (not (contains? up %))))))
    c))

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
       (let [lengths (reads/as-stored-shape-lengths (:index kb) f)]
         (if (and (empty? lengths) (empty? (get-in c [::bindings f]))
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
                                  now?  (let [hs (shape-handles kb shape)]
                                          (-> c
                                              (update ::cand-shapes (fnil conj #{}) shape)
                                              (update :arity (fnil into #{}) hs)
                                              (noted hs)))
                                  :else (let [hs (shape-handles kb shape)]
                                          (-> c
                                              (update ::cand-shapes disj shape)
                                              (update :arity #(reduce disj % hs))
                                              (noted hs))))))
                            c (sort lengths))
                 own       (get exact-of f)
                 conflict? (boolean (and (seq own) (or (< 1 (count own)) (some #(not= (first own) %) above))))
                 c         (cond
                             (and conflict? (contains? (::at-conflict c) f)) c
                             conflict?                       (conflict-raised w (update c ::at-conflict (fnil conj #{}) f) f)
                             (contains? (::at-conflict c) f) (update c ::at-conflict disj f)
                             :else                           c)]
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
                                              (filter other) (some-> extra deref)))))))))))
     c fs)))

(defn- conflict-up-current
  "`c` with `::conflict-up` read under the `genl` generation as it stands: built from
  `::at-conflict` when unbuilt or the relation was rebuilt from nothing, else raised from
  each type it holds that is the lower end of an edge that moved since
  (`tax/moves-since`), since no other type's parents moved.  A functor leaving
  `::at-conflict` and an edge leaving leave the set a superset, which costs the walk in
  `conflicts-below` the types it holds in excess and changes no answer."
  [w c]
  (let [tax  (:tax w)
        g    (tax/relation-gen tax :genl)
        seen (::conflict-gen c)]
    (cond
      (= g seen) c

      (or (nil? seen) (< g seen))
      (reduce #(conflict-raised w %1 %2) (assoc c ::conflict-up #{} ::conflict-gen g)
              (::at-conflict c))

      :else
      (reduce #(conflict-raised w %1 %2) (assoc c ::conflict-gen g)
              (filter (or (::conflict-up c) #{}) (tax/moves-since tax :genl seen))))))

(defn- conflicts-below
  "`[c fs]`: `c` with `::conflict-up` current, and `fs` the functors of `::at-conflict`
  below `t`, other than those in `skip`.  The walk down from `t` enters only the types of
  `::conflict-up`, and every type on a path from `t` down to such a functor is one, so it
  costs the types between `t` and the functors below it, none when no functor is."
  [w c t skip]
  (let [c  (conflict-up-current w c)
        up (::conflict-up c)
        ac (::at-conflict c)]
    [c (into #{} (filter #(and (contains? ac %) (not (contains? skip %))))
             ((:specs-global-while w) t #(contains? up %)))]))

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
        op          (get ex p)
        [c below]   (conflicts-below w c p (conj changed p))]
    (reduce (fn [c f]
              (let [o (get ex f)]
                (if (some (fn [a] (some #(not= a %) op)) o)
                  (set-pairs c f (conj (get-in c [::pairs-by f] #{}) [f p]))
                  c)))
            c below)))

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
          extra       (delay ((:genls-global-among w) super (::exact-of c) memo))
          [c below]   (conflicts-below w c sub changed)]
      (recompute-arity kb w c (into changed below) extra memo))
    c))

(defn- region-left
  "`c` after a length or an edge above every type of `region` leaves: the region's lengths
  are read again (`relength`) and every functor in it recomputed."
  [kb w c region]
  (recompute-arity kb w (relength w c region) region nil (volatile! {})))

(defn- arity-rebuilt
  "`c`, whose `::bindings` and `::exact-of` recover filled, with `::lengths` spread from
  every exact binding and the candidates of every functor a length reaches and every bound
  predicate computed, one memo across them, and `::conflict-up` built from them.  A
  functor no length reaches and no binding names holds no candidate."
  [kb w c]
  (let [c (reduce (fn [c [p ns]] (first (spread-lengths w c p ns)))
                  (dissoc c ::lengths ::conflict-up ::conflict-gen) (::exact-of c))]
    (conflict-up-current
     w (recompute-arity kb w c (into (set (keys (::lengths c))) (keys (::bindings c))) nil (volatile! {})))))

(defn- under
  "The terms of `fs` at or below one of the predicates `ps` over the unscoped `genl`
  closure (`w`, `decide/write-view`): each term's closure read, or the specializations of
  `ps` walked, whichever reads fewer."
  [w fs ps]
  (let [fs (set fs)]
    (if (< (count fs) (* 4 (count ps)))
      (into #{} (filter #(some (set ps) ((:genls-global w) %))) fs)
      (into #{} (comp (mapcat (:specs-global w)) (filter fs)) ps))))

(defn- tuples-of
  "The candidate tuples of `c` whose shape `[q n]` passes `keep?`, read by candidate shape."
  [kb c keep?]
  (let [ar (or (:arity c) #{})]
    (into #{} (comp (filter keep?)
                    (mapcat #(shape-handles kb %))
                    (filter #(contains? ar %)))
          (::cand-shapes c))))

(defn- pair-sets
  "The member sets of the pair `[f g]`: one exact binding of each, of two lengths."
  [c [f g]]
  (let [bs (::bindings c)]
    (for [[hf [kf a]] (get bs f) :when (= :exact kf)
          [hg [kg b]] (get bs g) :when (and (= :exact kg) (not= a b))]
      #{hf hg})))

(defn- note-arity!
  "Keep the arity candidates in step with the fact `sx` arriving (`stored?` true) or
  leaving.  A tuple of a candidate shape enters `:arity`, and a shape is tested against
  `::lengths` and the functor's `arityMin` when one of its tuples arrives; a candidate
  shape whose last tuple leaves the shape roster leaves `::cand-shapes`.  An
  exact length arriving at a predicate spreads to the types below it that miss it
  (`length-arrived`), and an edge arriving, a `genl` edge or a cover's edge per part
  (`tax/installed-edges`), spreads its upper end's lengths below its lower end
  (`edge-arrived`, while any exact length is bound).  A length or an edge leaving
  reads the lengths of the types below it again (`region-left`), and a binding that moves
  no length recomputes its own predicate.  An edge is not installed when its record
  is stored, so its arrival reads the upper end's lengths from `::lengths`; a departing
  edge may still be installed, which leaves a superset."
  [kb w sx stored?]
  (let [cands (reasoning/nogood-candidates kb)
        h     (:id sx)
        s     (:sentence sx)]
    (when-let [[q n :as shape] (fact-shape sx)]
      (let [c @cands]
        (if stored?
          (when (or (contains? (::cand-shapes c) shape)
                    (and (seq (::bindings c)) (candidate-shape? c q n)))
            (let [hs (when-not (contains? (::cand-shapes c) shape) (shape-handles kb shape))]
              (swap! cands
                     (fn [c]
                       (if (contains? (::cand-shapes c) shape)
                         (-> c (update :arity (fnil conj #{}) h) (noted [h]))
                         (let [hs (conj (set hs) h)]
                           (-> c
                               (update ::cand-shapes (fnil conj #{}) shape)
                               (update :arity (fnil into #{}) hs)
                               (noted hs))))))))
          (when (contains? (:arity c) h)
            (let [gone? (not (contains? (reads/as-stored-shape-lengths (:index kb) q) n))]
              (swap! cands
                     (fn [c]
                       (cond-> (-> c (update :arity #(some-> % (disj h))) (noted [h]))
                         gone? (update ::cand-shapes #(some-> % (disj shape)))))))))))
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
                           (recompute-arity kb w c #{p} nil (volatile! {}))))))
        ;; a binding leaving can leave another one convicting where it did not: the
        ;; candidates under its predicate and the pairs at it are placed again
        (when-not stored?
          (swap! cands (fn [c]
                         (let [qs (under w (map first (::cand-shapes c)) [p])]
                           (update c ::moved (fnil into #{})
                                   (concat (tuples-of kb c (fn [[q]] (contains? qs q)))
                                           (mapcat #(apply concat (pair-sets c %))
                                                   (filter #(some #{p} %) (::pairs c)))))))))))
    (when (and (nil? (:antecedent sx)) (seq (::exact-of @cands)))
      (doseq [[sub super] (tax/installed-edges s)
              :when (and (symbol? super) (not= sub super))]
        (swap! cands #(if stored?
                        (edge-arrived kb w % sub super)
                        (region-left kb w % ((:specs-global w) sub))))))))

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

(defn- bound-above
  "`(fn [q up])` → the predicates above `q`, `q` left out, holding an exact or
  `variable_arity` binding in `bindings`, that a reader with ancestor set `up` reaches
  over the `genl` edges stated in `up`: `q`'s global closure cut to the bound predicates
  (`tax/genls-global-union`, which reads the bindings of each predicate above `q` and no
  other), each kept when `up` holds every context asserting a `genl` edge or reaches it,
  read for the whole cut off one walk up from `q` (`tax/genls-asserted-among` over
  `tax/asserting-contexts-in`).  The cut's memo lives as long as the fn."
  [tax bindings]
  (let [bound? (fn [p] (some (fn [[_ [kind]]] (not= :min kind)) (get bindings p)))
        memo   (volatile! {})]
    (fn [q up]
      (let [cut   (if (empty? bindings) #{} (disj (tax/genls-global-union tax q (filter bound?) memo) q))
            scope (tax/asserting-contexts-in tax :genl up)]
        (if (or (nil? scope) (empty? cut))
          cut
          (tax/genls-asserted-among tax q cut scope))))))

(defn- reader-binding
  "What binds `q`'s length at a reader with ancestor set `up`, as `{:exact n :grounds #{h}}`
  or `{:min m :grounds #{h}}`, or nil.  `q`'s own bindings come first: a `variable_arity`
  membership leaves only a single `arityMin` floor, one exact length binds it and two
  leave it unbound.  A `q` with no own binding takes the one exact length the predicates
  above it through edges stated in `up` agree on, unless one of them is `variable_arity`:
  the bound predicates above it that `up` reaches (`above`, `bound-above`'s fn)."
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

(defn- convicts-at?
  "Does a reader with ancestor set `up` read a binding of `q` that a tuple of `n`
  arguments breaks (`reader-binding`), with the binding `hb` among its grounds when `hb`
  is given?  `above` is `bound-above`'s fn."
  [kb bindings above q n hb up hidden?]
  (let [b (reader-binding kb bindings above q up hidden?)]
    (boolean (and b (breaks? b n) (or (nil? hb) (contains? (:grounds b) hb))))))

(defn- pair-at?
  "Does a reader with ancestor set `up` read the predicates `f` and `g` bound to two
  different lengths: one exact length visible for each, neither `variable_arity`?"
  [kb bindings f g up hidden?]
  (let [bf (visible-bindings kb bindings f up hidden?)
        bg (visible-bindings kb bindings g up hidden?)]
    (boolean (and (empty? (:var bf)) (empty? (:var bg))
                  (= 1 (count (:exact bf))) (= 1 (count (:exact bg)))
                  (not= (key (first (:exact bf))) (key (first (:exact bg))))))))

;; ---- the nogoods placed as conclusions -------------------------------------
;;
;; No reader decides an arity nogood: the settle places each one where its members and
;; the binding that convicts it are seen together (`chain/place-arities!`), justified by
;; the binding and the `genl` edges up to the predicate stating it.  The index queues the
;; handles whose nogoods moved under `::moved` (`noted`).  Which binding binds a functor
;; depends on the bindings a reader sees and believes, so a reader that reads no
;; conviction through a placement is exempt from it (`exempt-at?`).

(defn held?
  "Does the candidate index `c` keep an arity candidate or the binding of a pair?"
  [c]
  (boolean (or (seq (:arity c)) (seq (:arity-pairs c)))))

(defn member?
  "Is `h` an arity candidate of `c`, or a binding of a predicate a candidate or a pair
  reads?"
  [c h]
  (or (contains? (:arity c) h) (contains? (::binding-of c) h)))

(defn moved?
  "Has the index queued a handle whose arity nogoods the settle places again
  (`take-moved!`)?"
  [c]
  (boolean (seq (::moved c))))

(defn take-moved!
  "The handles whose arity nogoods moved since the last call, and the queue emptied
  (`noted`)."
  [kb]
  (let [[old _] (swap-vals! (reasoning/nogood-candidates kb) dissoc ::moved)]
    (::moved old #{})))

(defn- shape-of
  "`[q n]` of the stored tuple `h`, or nil."
  [kb h]
  (some-> (p/get-sentex (:records kb) h) fact-shape))

(defn nogoods-holding
  "The arity nogoods `c` keeps with a member or a ground among the handles `hs`, each
  `{:members #{h} :shape [q n]}` for a candidate tuple or `{:members #{hf hg} :pair [f
  g]}` for one exact binding of each end of a pair: a candidate tuple of `hs`, and for a
  binding of `hs` the candidate tuples of a functor at or below its predicate (`w`,
  `decide/write-view`) and the pairs with its predicate at either end."
  [kb w c hs]
  (let [bo    (::binding-of c)
        ps    (into #{} (keep #(get bo %)) hs)
        pairs (filter (fn [[f g]] (or (contains? ps f) (contains? ps g))) (::pairs c))]
    (-> []
        (into (comp (filter #(contains? (:arity c) %))
                    (keep (fn [h] (when-let [sh (shape-of kb h)] {:members #{h} :shape sh}))))
              (into (set hs)
                    (when (seq ps)
                      (let [qs (under w (map first (::cand-shapes c)) ps)]
                        (tuples-of kb c (fn [[q]] (contains? qs q)))))))
        (into (for [pr pairs, ms (pair-sets c pr)] {:members ms :pair pr}))
        distinct
        vec)))

(defn members-under
  "The candidate tuples of `c` whose functor is at or below one of the predicates `ps`,
  and the bindings of the pairs whose lower end is: those a `genl` edge whose lower end is
  one of `ps` can give or take a route (`w`, `decide/write-view`)."
  [kb w c ps]
  (when (and (seq ps) (held? c))
    (let [qs (under w (map first (::cand-shapes c)) ps)
          fs (under w (keys (::pairs-by c)) ps)]
      (-> (tuples-of kb c (fn [[q]] (contains? qs q)))
          (into (comp (mapcat #(get-in c [::pairs-by %])) (mapcat #(pair-sets c %)) cat) fs)))))

(defn reached
  "The candidate tuples of `c` a binding stated in a context of `below` convicts: each
  candidate shape whose functor's own bindings, or those of a predicate above it storing
  an exact length (`w`, `decide/write-view`), include one stated there.  A pair's bindings
  are candidates, which `decide/handles-at` reads by context."
  [kb w c below]
  (when (and (seq below) (seq (:arity c)))
    (let [bs  (::bindings c)
          ex  (::exact-of c)
          in? (fn [p] (some (fn [[_ [_ _ ctx]]] (contains? below ctx)) (get bs p)))]
      (tuples-of kb c (fn [[q]] (or (in? q) (some in? ((:genls-global-among w) q ex (volatile! {})))))))))

(defn- binding-handle?
  "Is the stored record at `h` a binding (`binding-of`)?"
  [recs h]
  (boolean (some-> (p/get-sentex recs h) :sentence binding-of)))

(defn routes
  "Each way a binding convicts the arity nogood `ng` (`nogoods-holding`) over the unscoped
  taxonomy, as `{:choices [[[handle context]]] :links [[sub super]] :excluded-at f}`: for
  a tuple of shape `[q n]`, each own binding of `q` it breaks and each exact binding of a
  predicate above `q` (`w`, `decide/write-view`) it breaks, with the subsumption from `q`
  to that predicate; for a pair `[f g]`, the subsumption between the two.  A reader reads
  the bindings it sees and believes, so a route convicts only where the reader reads its
  binding as what binds `q` (`exempt-at?`).  While no binding the conviction reads is
  hidden from any context (`hidden-anywhere?`), a reader below a placement context sees
  the bindings it sees and more, and more bindings convict less, so a route is left out
  at a placement context that reads no conviction through it (`convicts-at?`,
  `pair-at?`)."
  [kb w c {:keys [members shape pair]} hidden-anywhere?]
  (let [tax (:tax w)
        bs  (::bindings c)
        up  (:context-up-global w)]
    (cond
      shape
      (let [[q n]   shape
            h       (first members)
            ps      (sort (disj ((:genls-global-among w) q (::exact-of c) (volatile! {})) q))
            above   (bound-above tax bs)
            ;; every binding of `q` and of a bound predicate above it, which is what a
            ;; reader's binding of `q` can read
            hidable (delay (boolean (some hidden-anywhere?
                                          (mapcat #(keys (get bs %))
                                                  (cons q (disj ((:genls-global-among w) q bs (volatile! {})) q))))))
            route   (fn [hb ctx links]
                      {:choices [[[hb ctx]]] :links links
                       :excluded-at (fn [pctx] (and (not @hidable)
                                                    (not (convicts-at? kb bs above q n hb (up pctx) nil))))})]
        (-> []
            (into (keep (fn [[hb [kind v ctx]]]
                          (when (or (and (= :exact kind) (not= n v)) (and (= :min kind) (> v n)))
                            (route hb ctx []))))
                  (sort-by key (get bs q)))
            (into (for [p ps
                        [hb [kind v ctx]] (sort-by key (get bs p))
                        :when (and (= :exact kind) (not= n v) (not= h hb))]
                    (route hb ctx [[q p]])))))

      pair
      (let [[f g]   pair
            hidable (delay (boolean (some hidden-anywhere? (mapcat #(keys (get bs %)) [f g]))))]
        [{:choices [[]] :links [pair]
          :excluded-at (fn [pctx] (and (not @hidable) (not (pair-at? kb bs f g (up pctx) nil))))}]))))

(defn note-except-target!
  "Queue `h` when it is a binding the index keeps, for the settle to place its nogoods
  again (`take-moved!`): an `except` of it arrived or left, which moves whether a reader
  below a placement context can read fewer bindings than that context (`routes`)."
  [kb h]
  (let [cands (reasoning/nogood-candidates kb)]
    (when (contains? (::binding-of @cands) h)
      (swap! cands update ::moved (fnil conj #{}) h))))

(defn kind-of
  "The kind the arity nogood over the member handles `ms` reports under, read off the
  candidate index `c`: `:arity` for a candidate tuple, `:arity-descension` for one binding
  of each end of a pair; else nil."
  [c ms]
  (let [bo (::binding-of c)]
    (cond
      (and (= 1 (count ms)) (contains? (:arity c) (first ms))) :arity
      (and (= 2 (count ms)) (every? #(contains? bo %) ms)
           (let [[f g] (map bo ms)] (or (contains? (::pairs c) [f g]) (contains? (::pairs c) [g f]))))
      :arity-descension)))

(defn owned?
  "Is the placed nogood over `members` with antecedents but the `genlCx` edges `core` one
  this family places (`chain/place-arities!`): one member and a binding (`binding-of`)
  among the other antecedents, or two bindings and nothing else but `genl` edges?"
  [kb members core]
  (let [recs   (:records kb)
        others (remove (set members) core)]
    (boolean
     (case (count members)
       1 (some #(binding-handle? recs %) others)
       2 (and (every? #(binding-handle? recs %) members)
              (every? #(= 'genl (some-> (p/get-sentex recs %) :sentence first)) others))
       false))))

(defn exempt-at?
  "Does a reader with ancestor set `up` read no conviction of the arity nogood over the
  handles `ms`: a candidate tuple whose length breaks no binding the reader reads
  (`convicts-at?`), or one binding of each end of a pair the reader does not read as two
  lengths (`pair-at?`).  `hidden?` names the handles the reader does not believe or see,
  or is nil.  False for any other set."
  [kb c ms up hidden?]
  (boolean
   (case (kind-of c ms)
     :arity            (when-let [[q n] (shape-of kb (first ms))]
                         (let [bs (::bindings c)]
                           (not (convicts-at? kb bs (bound-above (reasoning/taxonomy kb) bs) q n nil up hidden?))))
     :arity-descension (let [bo (::binding-of c)
                             [f g] (map bo ms)]
                         (not (pair-at? kb (::bindings c) f g up hidden?)))
     nil)))

(defn binding-grounds
  "The bindings among the antecedents `antes` of a placed arity nogood's justification."
  [kb antes]
  (filterv #(binding-handle? (:records kb) %) antes))

(def family
  "The arity family's entry in `decide/registry`.  Each nogood of it is placed as a
  conclusion (`chain/place-arities!`)."
  {:grounds   {:forced-monotonic          (into '#{arity arityMin}
                                                cat [(keys tax/exact-arity-classes)
                                                     variable-arity-classes])
               :forced-between-predicates '#{genl}}
   :note!     (fn [kb w sx stored?]
                (note-arity! kb w sx stored?)
                (when-not stored? (note-placement-left! kb sx)))
   :recovered (fn [kb w]
                (let [recs  (:records kb)
                      cands (reasoning/nogood-candidates kb)]
                  (doseq [f binding-functors
                          h (reads/as-stored-with-functor (:index kb) f)
                          :let [sx (p/get-sentex recs h)]
                          :when (and sx (nil? (:antecedent sx)))
                          :let [[p kind v] (binding-of (:sentence sx))]
                          :when p]
                    (swap! cands with-binding p h [kind v (:context sx)] true))
                  (swap! cands #(arity-rebuilt kb w %))))
   :handles   (fn [c] (concat (:arity c) (:arity-pairs c)))
   :holds?    (fn [c h] (or (contains? (:arity c) h) (contains? (:arity-pairs c) h)))})

;; ---- derived state (docs/caches.md, "The derived-state register") ----------------

(caches/register-derived
 {:id :N3 :label "Arity candidates" :kind :cache :keyed-by :functor
  :reads [:index :records :T1 :J5]
  :retired-by {:stored :K :removed :K :respelled :K :edge :K :declared :K :settle-pass :K
               :recover :R :image-install :R}
  :computed :write :imaged? :state
  :at [[:nogood-candidates :arity] [:nogood-candidates :arity-pairs]
       [:nogood-candidates ::bindings]
       [:nogood-candidates ::binding-of] [:nogood-candidates ::cand-shapes]
       [:nogood-candidates ::pairs] [:nogood-candidates ::exact-of]
       [:nogood-candidates ::lengths] [:nogood-candidates ::pairs-by]
       [:nogood-candidates ::pair-count] [:nogood-candidates ::at-conflict]
       [:nogood-candidates ::conflict-up] [:nogood-candidates ::conflict-gen]
       [:nogood-candidates ::moved]]
  :bound "one entry per stored binding, per type at or below a bound predicate and per tuple of a shape a binding breaks"
  :note "the arity declarations, read off the binding functors' extents at recover, the shapes they break, read off the shape roster, and the handles queued for the settle to place again; `::conflict-up` is brought current at the next write through the relation moves (J5), whole when the generation restarts"})

;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.decide.tuple
  "The two tuple families.  The self and converse family: a ground binary self tuple under
  `irreflexive`, and a tuple and its stored converse under `anti_symmetric`.  The
  tuple-mark family: the determinants under `functional` and `functionalInArg`, the
  `anti_transitive` chains and the `asymmetric` converse pairs.  Both find their nogoods
  from a stored tuple's own arguments and share the converse pairs.  See docs/nmtms.md,
  \"Nogoods decided at the reader\"."
  (:require [vaelii.impl.jtms :as jtms]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]))

;; ---- the self and converse family -------------------------------------------

(def ^:private converse-keys
  "Each candidate key of the self and converse family: the taxonomy props of the marks
  that read it.  `:self` holds the ground binary self tuples, `:converse` the ground
  binary tuples with a stored converse."
  {:self     #{:irreflexive}
   :converse #{:anti-symmetric :asymmetric}})

(defn- binary-tuple
  "`[a b]` for a stored fact `sx` whose sentence is a ground positive binary tuple with a
  symbol functor, else nil."
  [sx]
  (let [s (:sentence sx)]
    (when (and (nil? (:antecedent sx)) (seq? s) (= 3 (count s)))
      (let [f (nm/functor s)]
        (when (and (symbol? f) (not= 'not f) (not (sx/variable? f)) (sx/ground-term? s))
          (vec (nm/args s)))))))

(defn- symbol-pair?
  "Two plain symbols, which an all-`:monotonic` `anti_symmetric` converse or functional
  collision merges instead of convicting (`special/derive-antisymmetric-equalities`,
  `special/derive-functional-equalities`)."
  [a b]
  (and (symbol? a) (symbol? b) (not (sx/variable? a)) (not (sx/variable? b))))

(defn- converse-functors
  "The functors a converse of a tuple of `q` is read under: `q`, and every predicate
  below an `anti_symmetric` or `asymmetric` mark on `q` or above it, since the mark binds
  its whole spec subtree, read over `specs`, the unscoped spec closure: a candidate a
  reader cannot read is dropped by `nogoods-at`, and a missed one is a nogood no reader
  decides."
  [tax specs q]
  (into #{q}
        (comp (mapcat #(when (seq (tax/props tax %)) (tax/props-over tax % q)))
              (mapcat specs))
        (:converse converse-keys)))

(defn- converse-handles
  "The handles of the stored converses `(q' b a)` of `(q a b)`: one trie read under each
  of `converse-functors`, since the argument roots index neither a number nor a string."
  [kb tax specs q a b]
  (into []
        (mapcat #(reads/as-stored-at-path (:index kb) (sx/path (sx/sentex (list % b a) '?c))))
        (sort (converse-functors tax specs q))))

(defn- stored-converses
  "The handles other than `h` of the stored converses of `h`, `(q a b)`, read off the
  index (`converse-handles`) and checked against their records."
  [kb w h q a b]
  (let [recs (:records kb)]
    (into [] (filter #(and (not= h %) (= [b a] (some-> (p/get-sentex recs %) binary-tuple))))
          (converse-handles kb (:tax w) (:specs-global w) q a b))))

(def ^:dynamic ^:private *converse-tuples*
  "A volatile map `{[a b] [[q h] …]}` while `rebuild-candidates!` replays storage: each
  tuple that would read its converses is kept here instead, and `converse-pairs` joins
  them once the replay has seen every record.  nil otherwise."
  nil)

(defn- converse-pairs
  "The converse pairs of the tuples `rebuild-candidates!` kept (`*converse-tuples*`), each
  a set of two handles: each `(q a b)` with a kept `(q' b a)`, `q'` among
  `converse-functors` of `q`.  The records the replay fetched answer what
  `stored-converses` reads off the index per tuple, with no trie read and no sentence
  built, and `converse-functors` is read once per functor."
  [w tuples]
  (let [cf (memoize #(converse-functors (:tax w) (:specs-global w) %))]
    (persistent!
     (reduce-kv (fn [acc [a b] es]
                  (if-some [rs (get tuples [b a])]
                    (reduce (fn [acc [q h]]
                              (let [fs     (cf q)
                                    others (into [] (keep (fn [[q' h']]
                                                            (when (and (not= h h') (contains? fs q')) h')))
                                                 rs)]
                                (reduce #(conj! %1 (hash-set h %2)) acc others)))
                            acc es)
                    acc))
                (transient #{}) tuples))))

;; ---- the tuple marks -------------------------------------------------------
;;
;; A tuple under a `functional`, `functionalInArg` or `anti_transitive` mark on its functor
;; or above it forms its nogoods with the stored tuples its own arguments name: the tuples
;; agreeing with it on the determinant, every position but the marked one, and differing
;; at the marked one; and the steps of a chain through its two arguments.  The candidate
;; index keeps each determinant holding two fillers under `::det`, as `{[P k n det] {h
;; [filler context]}}` for the mark's predicate `P`, arity `k`, position `n` and the
;; arguments with position `n` nil, with its members by context under `::det-ctx`; each
;; chain's members under `::chains`; and each stored converse pair under `::conv`, which
;; the `asymmetric` marks read.  `::member-of` holds each member's keys, for its removal.
;; The index reads every mark over a tuple's functor anywhere, so it is a superset, and a
;; reader keeps the nogoods whose members and marks it sees.
;;
;; A determinant member is live, under `::live`, when a member with another filler sits in
;; a context some context sees together with its own; only a live member is a candidate,
;; so a determinant whose fillers no context sees together costs no reader anything.  A
;; reader decides every pair, chain and converse pair.  Liveness reads the unscoped
;; `genlCx` closure, so `::ts-gen` holds the generation it was read at, and `sync-tuples`
;; reads it again when it moved.

(defn- fact-tuple
  "`[f args]` for a stored fact `sx` whose sentence is a ground positive tuple with a
  symbol functor, else nil."
  [sx]
  (let [s (:sentence sx)]
    (when (and (nil? (:antecedent sx)) (seq? s) (<= 2 (count s)))
      (let [f (first s)]
        (when (and (sx/plain-symbol? f) (not= 'not f) (sx/ground-term? s))
          [f (vec (rest s))])))))

(defn- tuple-marks?
  "Does the taxonomy hold a `functional`, `functionalInArg` or `anti_transitive` mark?
  Three map reads."
  [tax]
  (boolean (or (seq (tax/props tax :functional))
               (seq (tax/functional-in-arg-predicates tax))
               (seq (tax/props tax :anti-transitive)))))

(defn- tuples-live?
  "Can the tuple-mark candidates `c` form a nogood: a live determinant member or a chain
  is stored while the taxonomy holds a tuple mark, or a converse pair is stored while
  some predicate carries an `asymmetric` mark."
  [tax c]
  (boolean (or (and (or (seq (::live c)) (seq (::chains c))) (tuple-marks? tax))
               (and (seq (::conv c)) (seq (tax/props tax :asymmetric))))))

(defn- tuple-members
  "The handles of the tuple-mark candidates `c`: the live determinant members and the
  members of every chain and converse pair."
  [c]
  (-> #{}
      (into cat (vals (::live c)))
      (into cat (::chains c))
      (into cat (::conv c))))

(defn- stored-specs
  "The predicates at or below `p` holding a stored fact, in content order."
  [kb w p]
  (into (sorted-set)
        (filter #(pos? (reads/stored-count-with-functor (:index kb) %)))
        ((:specs-global w) p)))

(defn- tuples-at
  "`{h [args context]}` of the stored positive tuples of a functor in `fs` whose arguments
  are `args` at every position `args` does not hold nil, `(count args)` of them.  Per
  functor, one trie read under a variable context when the bound positions lead, else one
  intersection of the bound symbol positions' argument roots, since those index neither a
  number nor a string, else the trie read."
  [kb fs args]
  (let [idx   (:index kb)
        recs  (:records kb)
        k     (count args)
        lead? (every? nil? (drop-while some? args))
        roots (into [] (keep-indexed (fn [i a] (when (sx/plain-symbol? a) [(inc i) a]))) args)
        probe (fn [g]
                (if (or lead? (empty? roots))
                  (reads/as-stored-at-path
                   idx (sx/path (sx/sentex (apply list g (map-indexed
                                                          (fn [i a] (if (nil? a) (symbol (str "?t" i)) a))
                                                          args))
                                           '?c)))
                  (reads/as-stored-with-args idx g roots)))]
    (into {}
          (for [g fs
                h (probe g)
                :let [sx (p/get-sentex recs h)
                      [f as] (some-> sx fact-tuple)]
                :when (and (= g f) (= k (count as))
                           (every? true? (map #(or (nil? %1) (= %1 %2)) args as)))]
            [h [as (:context sx)]]))))

(def ^:dynamic ^:private *functor-marks*
  "A volatile map while `rebuild-candidates!` replays storage, holding each functor's
  marks as `found-for` reads them (`det-marks`, the `anti_transitive` marks above it):
  both walk the functor's supertypes, the replay offers every stored tuple, and the
  taxonomy holds still under it, so a functor's are read once rather than once per
  tuple, and each kind's roster cut is read off one memo (`roster-marks`) rather than a
  closure per functor.  nil otherwise."
  nil)

(defn- functor-marks
  "`(f)`, held in `*functor-marks*` under `k` while it is bound."
  [k f]
  (if-some [m *functor-marks*]
    (let [v (get @m k ::absent)]
      (if (identical? ::absent v)
        (let [v (f)] (vswap! m assoc k v) v)
        v))
    (f)))

(defn- roster-marks
  "`tax/props-over` of `kind` on `q` with no context.  While `*functor-marks*` is bound,
  read off the roster's cut with one memo per kind and roster (`tax/props-over-among`)."
  [tax kind q]
  (if (some? *functor-marks*)
    (tax/props-over-among tax kind q
                          (functor-marks [::memo kind (get-in @tax [:props kind])] #(volatile! {})))
    (tax/props-over tax kind q)))

(defn- det-marks
  "`[P n]` for every `functional` mark on `q` or above it, at position 2 of a binary
  tuple, and every `functionalInArg` mark there at a position a tuple of `k` arguments
  has.  Unscoped."
  [tax q k]
  (cond-> (into #{} (filter (fn [[_ n]] (<= n k))) (tax/functional-in-arg-over tax q))
    (= 2 k) (into (map #(vector % 2)) (roster-marks tax :functional q))))

(defn- co-visible
  "The keys of `by` (a map keyed by context) some context sees together with `c`, nil
  among them when `by` holds it: read from `c`'s descendants' ancestor sets, or by asking
  each key for a descendant it shares with `c`, whichever reads fewer contexts.  The
  write view `w`, since a scoped read asks a reader's withdrawal, which reads this."
  [w c by]
  (if (nil? c)
    (set (keys by))
    (let [ups  (:context-up-global w)
          down ((:context-down-global w) c)
          up   (ups c)]
      (cond-> (if (< (* (count down) (count up)) (count by))
                (into #{} (comp (mapcat ups) (filter #(contains? by %)))
                      down)
                (into #{} (filter #(and (some? %)
                                        (or (= c %)
                                            (boolean (some down ((:context-down-global w) %))))))
                      (keys by)))
        (contains? by nil) (conj nil)))))

(defn- link
  "`c` with the members of `ms` recorded under `k`."
  [c ms k]
  (reduce (fn [c h] (update-in c [::member-of h] (fnil conj #{}) k)) c ms))

(defn- unlink
  "`c` with `k` dropped from the records of the members `ms`."
  [c ms k]
  (reduce (fn [c h]
            (let [left (disj (get-in c [::member-of h] #{}) k)]
              (if (empty? left)
                (update c ::member-of dissoc h)
                (assoc-in c [::member-of h] left))))
          c ms))

(defn- det-partners
  "The members of determinant `key` with a filler other than `h`'s, in a context some
  context sees together with `h`'s."
  [w c key h]
  (let [g      (get-in c [::det key])
        [v cx] (get g h)
        by     (get-in c [::det-ctx key])]
    (for [c' (co-visible w cx by)
          h' (get by c')
          :when (and (not= h h') (not= v (first (get g h'))))]
      h')))

(defn- classify-det-member
  "`c` with the member `h` of determinant `key` live, with its partners, when it has one
  (`det-partners`)."
  [w c key h]
  (let [ps (det-partners w c key h)]
    (if (empty? ps)
      c
      (update-in c [::live key] (fnil into #{}) (conj ps h)))))

(defn- add-det-member
  "`c` with `h`, filling `v` in context `cx`, a member of determinant `key`."
  [w c key h v cx]
  (as-> c c
    (assoc-in c [::det key h] [v cx])
    (update-in c [::det-ctx key cx] (fnil conj #{}) h)
    (link c [h] [::det key])
    (classify-det-member w c key h)))

(defn- sync-tuples
  "`c` with `::live` read again when the `genlCx` generation moved since `::ts-gen`: one
  pass over the determinants."
  [w c]
  (let [gen (tax/relation-gen (:tax w) :genlCx)]
    (if (= gen (::ts-gen c 0))
      c
      (as-> c c
        (dissoc c ::live)
        (reduce-kv (fn [c key g] (reduce #(classify-det-member w %1 key %2) c (keys g)))
                   c (::det c))
        (assoc c ::ts-gen gen)))))

(defn- found-for
  "The determinants and chains the stored tuple `h`, `(q args…)` in context `cx`, is a
  member of, read from storage: `{:det {key {h [filler context]}} :chains #{members}}`.
  A new determinant is kept when it holds two fillers, and a chain when it has two
  members or three.  A determinant `dets` (`::det`) holds already takes the tuple with no
  read, so an empty or a wide determinant is read once, when its second filler arrives."
  [kb w dets h q args cx]
  (let [tax (:tax w)
        k   (count args)
        det (into {}
                  (keep (fn [[p n]]
                          (let [d   (assoc args (dec n) nil)
                                key [p k n d]
                                v   (nth args (dec n))]
                            (if (contains? dets key)
                              [key {h [v cx]}]
                              (let [g (into {h [v cx]}
                                            (map (fn [[h' [as c']]] [h' [(nth as (dec n)) c']]))
                                            (tuples-at kb (stored-specs kb w p) d))]
                                (when (< 1 (count (into #{} (map first) (vals g))))
                                  [key g]))))))
                  (functor-marks [:det q k] #(det-marks tax q k)))
        anti (when (= 2 k)
               (functor-marks [:anti q] #(roster-marks tax :anti-transitive q)))
        chains (into #{}
                     (comp (mapcat
                            (fn [p]
                              (let [fs    (stored-specs kb w p)
                                    [a b] args
                                    at    (fn [x y] (keys (tuples-at kb fs [x y])))]
                                (concat
                                 ;; the direct step: (a m) and (m b)
                                 (for [[s1 [[_ m]]] (tuples-at kb fs [a nil]), s2 (at m b)]
                                   (hash-set s1 s2 h))
                                 ;; the first step: (b c) and the direct (a c)
                                 (for [[s2 [[_ c]]] (tuples-at kb fs [b nil]), cl (at a c)]
                                   (hash-set h s2 cl))
                                 ;; the second step: (z a) and the direct (z b)
                                 (for [[s1 [[z _]]] (tuples-at kb fs [nil a]), cl (at z b)]
                                   (hash-set s1 h cl))))))
                           (filter #(< 1 (count %))))
                     anti)]
    {:det det :chains chains}))

(defn- add-found
  "`c` with `found-for`'s answer merged in."
  [w c {:keys [det chains]}]
  (as-> c c
    (reduce-kv (fn [c key g]
                 (reduce-kv (fn [c h [v cx]]
                              (if (contains? (get-in c [::det key]) h)
                                c
                                (add-det-member w c key h v cx)))
                            c g))
               c det)
    (reduce (fn [c ms]
              (if (contains? (::chains c) ms)
                c
                (-> c (update ::chains (fnil conj #{}) ms) (link ms [::chains ms]))))
            c chains)))

(defn- add-conv
  "`c` with the stored tuple `h` and each of its stored converses `others` recorded as a
  pair under `::conv`."
  [c h others]
  (reduce (fn [c o]
            (let [ms #{h o}]
              (if (contains? (::conv c) ms)
                c
                (-> c (update ::conv (fnil conj #{}) ms) (link ms [::conv ms])))))
          c others))

(defn- drop-det-member
  "`c` with `h` gone from determinant `key`: the determinant goes when one filler is
  left, and a partner left with none is no longer live."
  [w c key h]
  (let [[_ cx] (get-in c [::det key h])
        ps     (det-partners w c key h)
        c      (-> c
                   (update-in [::det key] dissoc h)
                   (update-in [::det-ctx key cx] disj h)
                   (update-in [::live key] #(some-> % (disj h))))
        g      (get-in c [::det key])]
    (if (< 1 (count (into #{} (map first) (vals g))))
      (reduce (fn [c h'] (if (seq (det-partners w c key h'))
                           c
                           (update-in c [::live key] disj h')))
              c ps)
      (-> c
          (update ::det dissoc key)
          (update ::det-ctx dissoc key)
          (update ::live dissoc key)
          (unlink (keys g) [::det key])))))

(defn- drop-tuple
  "`c` with the tuple `h` gone from every determinant, chain and converse pair it is a
  member of: a chain or a pair goes whole."
  [w c h]
  (reduce (fn [c [kind key :as k]]
            (case kind
              ::det (drop-det-member w c key h)
              (-> c (update kind disj key) (unlink (disj key h) k))))
          (update c ::member-of dissoc h)
          (get-in c [::member-of h])))

(defn- note-tuple!
  "Keep the tuple-mark candidates in step with the fact `sx` arriving (`stored?` true) or
  leaving.  An arriving tuple reads its determinants and chains (`found-for`) while the
  taxonomy holds a tuple mark; a leaving one reads nothing."
  [kb w sx stored?]
  (let [cands (reasoning/nogood-candidates kb)]
    (if stored?
      (when (tuple-marks? (:tax w))
        (when-let [[q args] (fact-tuple sx)]
          (let [found (found-for kb w (::det @cands) (:id sx) q args (:context sx))]
            (when (or (seq (:det found)) (seq (:chains found)))
              (swap! cands #(add-found w (sync-tuples w %) found))))))
      (when (contains? (::member-of @cands) (:id sx))
        (swap! cands #(drop-tuple w (sync-tuples w %) (:id sx)))))))

(defn- note-converse!
  "Keep the self tuples and the converse candidates in step with the fact `sx` arriving
  (`stored?` true) or leaving (`note-candidate!`)."
  [kb w sx stored?]
  (when-let [[a b] (binary-tuple sx)]
    (let [q     (nm/functor (:sentence sx))
          h     (:id sx)
          cands (reasoning/nogood-candidates kb)]
      (cond
        (not stored?)
        (when (or (contains? (:self @cands) h) (contains? (:converse @cands) h))
          (swap! cands (fn [m] (-> m (update :self disj h) (update :converse disj h)))))

        (= a b)
        (swap! cands update :self (fnil conj #{}) h)

        (and (symbol-pair? a b)
             (not-any? #(seq (tax/props (:tax w) %)) (:converse converse-keys)))
        nil

        (some? *converse-tuples*)
        (vswap! *converse-tuples* update [a b] (fnil conj []) [q h])

        :else
        (let [others (stored-converses kb w h q a b)]
          (when (seq others)
            (swap! cands #(-> (sync-tuples w %)
                              (update :converse (fnil into #{}) (conj others h))
                              (add-conv h others)))))))))

(defn offer!
  "Offer the stored fact `sx` to the converse and tuple-mark candidates again, or with
  `only` `:converse` to the converse ones alone: a mark or a predicate `genl` edge
  arriving over stored tuples makes candidates their store did not read
  (`decide/offer!`)."
  [kb w sx only]
  (note-converse! kb w sx true)
  (when-not (= :converse only) (note-tuple! kb w sx true)))

(defn- marks-over
  "The `[mark-handle P]` pairs of `prop` a reader with ancestor set `up` reads over
  predicate `q`: `P` is `q` or above it through predicate edges asserted in `up`, and the
  mark is IN, stated in `up` and not hidden (`hidden?`, or nil)."
  [kb prop q up hidden?]
  (let [tax    (reasoning/taxonomy kb)
        marked (tax/props tax prop)]
    (when (seq marked)
      (let [tms (reasoning/tms kb)]
        (for [p (sort (filter marked (tax/genls-asserted-in tax q up)))
              [h c] (sort (tax/prop-supporter-contexts tax prop p))
              :when (and (or (nil? c) (contains? up c)) (jtms/in? tms h)
                         (not (and hidden? (hidden? h))))]
          [h p])))))

(defn- seen-tuple
  "`[sx a b]` for the candidate `h` when a reader with ancestor set `up` sees it, else nil."
  [kb h up hidden?]
  (when-let [sx (p/get-sentex (:records kb) h)]
    (when (and (or (nil? (:context sx)) (contains? up (:context sx)))
               (not (and hidden? (hidden? h))))
      (when-let [[a b] (binary-tuple sx)] [sx a b]))))

(defn monotonic-member?
  "Is `h` a `:monotonic` member of a collision, which a merge needs of every member
  (docs/reference.md, decision 6)?  Its class, or its premise strength while a network
  defeat decided before a restrengthening holds it OUT: a `:monotonic` member is never a
  loser, so the next settle releases it."
  [tms h]
  (or (= :monotonic (jtms/defeat-class tms h)) (= :monotonic (jtms/premise-strength tms h))))

(defn- merges?
  "Does the converse pair `h`, `o` over `a` and `b` merge the two terms instead of forming
  a nogood: two symbols, both members `:monotonic`."
  [tms a b h o]
  (and (symbol-pair? a b) (monotonic-member? tms h) (monotonic-member? tms o)))

(defn- converse-nogoods
  "The self and converse nogoods a reader with ancestor set `up` reads: a self tuple under
  a visible `irreflexive` mark, and a converse pair under one visible `anti_symmetric`
  mark over both functors.  A pair of two symbols with both members `:monotonic` merges
  and comes back under `:kind :merge`.  A tuple's converses are read under the unscoped
  `converse-functors`, a superset, and each is kept only when the reader sees it and a
  mark over both functors."
  [kb cands up hidden?]
  (let [tms   (reasoning/tms kb)
        tax   (reasoning/taxonomy kb)
        specs #(tax/specs-global tax %)]
    (concat
     (for [h (sort (:self cands))
           :let [[sx] (seen-tuple kb h up hidden?)]
           :when sx
           :let [ms (marks-over kb :irreflexive (nm/functor (:sentence sx)) up hidden?)]
           :when (seq ms)]
       {:members #{h} :marks (into #{} (map first) ms) :kind :irreflexive})
     (for [h (sort (:converse cands))
           :let [[sx a b] (seen-tuple kb h up hidden?)]
           :when sx
           :let [m1 (marks-over kb :anti-symmetric (nm/functor (:sentence sx)) up hidden?)]
           :when (seq m1)
           o (sort (converse-handles kb tax specs (nm/functor (:sentence sx)) a b))
           :when (not= o h)
           :let [[sx2] (seen-tuple kb o up hidden?)]
           :when sx2
           :let [m2 (marks-over kb :anti-symmetric (nm/functor (:sentence sx2)) up hidden?)
                 ps (into #{} (map peek) m2)
                 ms (concat (filter #(ps (peek %)) m1)
                            (filter #(contains? (into #{} (map peek) m1) (peek %)) m2))]
           :when (seq ms)]
       {:members #{h o} :marks (into #{} (map first) ms)
        :kind    (if (merges? tms a b h o) :merge :anti-symmetric)}))))

(defn- mark-supporters
  "`{handle context}` of the marks `prop` states of `p`: a taxonomy prop, or
  `[:functional-in-arg n]`."
  [tax prop p]
  (if (keyword? prop)
    (tax/prop-supporter-contexts tax prop p)
    (tax/functional-in-arg-supporter-contexts tax p (second prop))))

(defn- marked-by
  "The predicates carrying `prop` (`mark-supporters`), as a set."
  [tax prop]
  (if (keyword? prop)
    (tax/props tax prop)
    (into #{} (keep (fn [[q ns]] (when (contains? ns (second prop)) q)))
          (tax/functional-in-arg-table tax))))

(defn- mark-reader
  "`(fn [prop q])` → `{P #{mark-handle}}`, memoized: the marks of `prop` a reader with
  ancestor set `up` reads over predicate `q`.  `P` is `q` or above it through predicate
  edges asserted in `up`, and each mark is IN, stated in `up` and not hidden (`hidden?`,
  or nil)."
  [kb up hidden?]
  (let [tax   (reasoning/taxonomy kb)
        tms   (reasoning/tms kb)
        memo  (volatile! {})
        ups   (volatile! {})
        up-of (fn [q] (or (get @ups q)
                          (let [v (tax/genls-asserted-in tax q up)] (vswap! ups assoc q v) v)))]
    (fn [prop q]
      (if-let [e (find @memo [prop q])]
        (val e)
        (let [marked (marked-by tax prop)
              v      (if (empty? marked)
                       {}
                       (into {}
                             (keep (fn [p]
                                     (let [hs (into #{}
                                                    (keep (fn [[h c]]
                                                            (when (and (or (nil? c) (contains? up c))
                                                                       (jtms/in? tms h)
                                                                       (not (and hidden? (hidden? h))))
                                                              h)))
                                                    (mark-supporters tax prop p))]
                                       (when (seq hs) [p hs]))))
                             (filter marked (up-of q))))]
          (vswap! memo assoc [prop q] v)
          v)))))

(defn- common-marks
  "The handles of the `prop` marks `marks` (`mark-reader`) reads on one predicate over
  every functor of `fs`, restricted to `p` when given."
  ([marks prop fs] (common-marks marks prop fs nil))
  ([marks prop fs p]
   (let [ms (map #(marks prop %) fs)
         ps (reduce (fn [acc m] (into #{} (filter #(contains? m %)) acc))
                    (if p #{p} (set (keys (first ms))))
                    ms)]
     (into #{} (mapcat #(get (first ms) %)) ps))))

(defn- same-class-at?
  "Do the symbols `a` and `b` denote one thing through equality edges a reader with
  ancestor set `up` sees: each with a supporter IN, stated in `up` and not hidden?  The
  scoped election `res/same-class-in?` makes, over the reader's ancestor set and with no
  withdrawal read, since this runs inside one."
  [kb up hidden? a b]
  (let [tax (reasoning/taxonomy kb)]
    (boolean
     (and (tax/merged? tax a) (tax/merged? tax b)
          (let [tms  (reasoning/tms kb)
                recs (:records kb)
                vis? (memoize (fn [h] (and (jtms/in? tms h) (not (and hidden? (hidden? h)))
                                           (let [c (:context (p/get-sentex recs h))]
                                             (or (nil? c) (contains? up c))))))
                rep  (fn [t] (if (tax/class-fully-visible? tax t vis?)
                               (tax/representative tax t)
                               (second (tax/scoped-class tax t vis?))))]
            (= (rep a) (rep b)))))))

(defn- member-reader
  "`(fn [h])` → `[functor context]` of the stored tuple `h`, or nil, memoized."
  [kb]
  (let [recs (:records kb)]
    (memoize (fn [h] (when-let [sx (p/get-sentex recs h)]
                       (when-let [[f] (fact-tuple sx)] [f (:context sx)]))))))

(defn- read-spec
  "The nogood a reader reads of `spec`, `{:members :marks :kind}`, or nil: none unless it
  sees every member, in `up` and not `hidden?`.  `spec` is a determinant pair
  `{:family :det :members :key :fillers}`, a chain `{:family :chain :members}` or a
  converse pair `{:family :converse :members}`.  A determinant pair under a `functional`
  or `functionalInArg` mark on the determinant's predicate over both functors is
  `:functional`; `:merge` when both fillers are symbols and both members `:monotonic`,
  which `special/derive-functional-equalities` merges; and nothing when the fillers are
  one class at the reader (`same-class-at?`).  A chain under one `anti_transitive` mark
  over every functor is `:anti-transitive`, and a converse pair under one `asymmetric`
  mark over both functors `:asymmetric`.  `marks` is `mark-reader`'s and `member`
  `member-reader`'s."
  [kb marks member up hidden? spec]
  (let [ms  (:members spec)
        inf (map member ms)]
    (when (every? (fn [[h [f c]]] (and f (or (nil? c) (contains? up c))
                                       (not (and hidden? (hidden? h)))))
                  (map vector ms inf))
      (let [fs (into #{} (map first) inf)]
        (case (:family spec)
          :det
          (let [[p k n] (:key spec)
                hs      (-> (if (= 2 k n) (common-marks marks :functional fs p) #{})
                            (into (common-marks marks [:functional-in-arg n] fs p)))
                [v1 v2] (:fillers spec)]
            (when (seq hs)
              (cond
                (and (symbol-pair? v1 v2)
                     (every? #(monotonic-member? (reasoning/tms kb) %) ms))
                {:members ms :marks hs :kind :merge}

                (and (symbol-pair? v1 v2) (same-class-at? kb up hidden? v1 v2))
                nil

                :else
                {:members ms :marks hs :kind :functional})))

          :chain
          (let [hs (common-marks marks :anti-transitive fs)]
            (when (seq hs) {:members ms :marks hs :kind :anti-transitive}))

          :converse
          (let [hs (common-marks marks :asymmetric fs)]
            (when (seq hs) {:members ms :marks hs :kind :asymmetric})))))))

(defn- tuple-nogoods
  "The tuple-mark nogoods a reader with ancestor set `up` decides (`read-spec`).  Each
  determinant contributes the pairs of its live members the reader sees, so a
  determinant read by a reader seeing one member costs a filter of its live members."
  [kb c up hidden?]
  (when (tuples-live? (reasoning/taxonomy kb) c)
    (let [marks   (mark-reader kb up hidden?)
          member  (member-reader kb)
          seen?   (fn [h] (let [[_ cx] (member h)]
                            (and (or (nil? cx) (contains? up cx))
                                 (not (and hidden? (hidden? h))))))
          dets    (for [[key live] (::live c)
                        :let [g  (get-in c [::det key])
                              hs (sort (filter seen? live))]
                        [i h1] (map-indexed vector hs)
                        h2 (drop (inc i) hs)
                        :let [v1 (first (get g h1)) v2 (first (get g h2))]
                        :when (not= v1 v2)]
                    {:family :det :members #{h1 h2} :key key :fillers [v1 v2]})
          specs   (concat dets
                          (for [ms (::chains c)] {:family :chain :members ms})
                          (for [ms (::conv c)] {:family :converse :members ms}))]
      (for [spec specs
            :let [ng (read-spec kb marks member up hidden? spec)]
            :when ng]
        ng))))

(def converse-family
  "The self and converse family's entry in `decide/registry`.  A replay keeps the tuples
  by their arguments and joins them after it (`converse-pairs`)."
  {:note!     (fn [kb w sx stored? _] (note-converse! kb w sx stored?))
   :replay    (fn [] {#'*converse-tuples* (volatile! {})})
   :replayed  (fn [_ w c]
                (let [pairs (converse-pairs w @*converse-tuples*)]
                  (if (seq pairs)
                    (reduce (fn [c ms] (let [[h o] (seq ms)] (add-conv c h [o])))
                            (update c :converse (fnil into #{}) cat pairs)
                            pairs)
                    c)))
   :handles   (fn [c] (concat (:self c) (:converse c)))
   :live?     (fn [tax c] (some (fn [[k props]] (and (seq (get c k)) (some #(seq (tax/props tax %)) props)))
                                converse-keys))
   :unstamped #{}
   :nogoods   converse-nogoods})

(def marks-family
  "The tuple-mark family's entry in `decide/registry`.  Liveness reads the `genlCx`
  closure, so a moved generation syncs `::live` (`sync-tuples`), and a determinant reads
  the equality edges, since two fillers of one class form no nogood."
  {:note!     (fn [kb w sx stored? _] (note-tuple! kb w sx stored?))
   :replay    (fn [] {#'*functor-marks* (volatile! {})})
   :synced?   (fn [tax c] (= (tax/relation-gen tax :genlCx) (::ts-gen c 0)))
   :sync      sync-tuples
   :handles   tuple-members
   :live?     tuples-live?
   :unstamped #{::member-of ::det ::det-ctx ::ts-gen}
   :stamp     (fn [tax c] (when (seq (::live c)) (tax/equality-edges tax)))
   :nogoods   tuple-nogoods})

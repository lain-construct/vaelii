;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.qcn
  "Path consistency over a relation algebra `{:universe :identity :compose :converse}` and
  a network `{[i j] → #{base relations}}`, both directions stored, an unrecorded pair the
  universe.  Pure data: no KB, context or belief.  A pass runs over bitmasks and answers
  relation sets.  See docs/qcn.md."
  (:require [clojure.set :as set]
            [vaelii.impl.caches :as caches]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.types.qcn :as qcn-types])
  (:import [java.util ArrayDeque BitSet LinkedHashSet]
           [vaelii.impl.types.qcn IRelationOps]))

(defn constraint
  "The constraint on `[i j]` in `net` under `algebra`: the identity on the diagonal,
  the recorded set, else the universe (unknown)."
  [net {:keys [universe identity]} i j]
  (if (= i j) identity (get net [i j] universe)))

(defn- unsatisfiable-as-given?
  "Is one recorded constraint unsatisfiable before any tightening: empty, or a diagonal
  constraint excluding the identity?  The loop reports neither (docs/qcn.md, \"Path
  consistency\")."
  [identity [[i j] rels]]
  (or (empty? rels)
      (and (= i j) (empty? (set/intersection rels identity)))))

(defn unsatisfiable-pairs
  "The pairs of `net` unsatisfiable before any tightening (`unsatisfiable-as-given?`).
  Empty when only composition empties a constraint."
  [net {:keys [identity]}]
  (into #{} (keep (fn [[pair :as entry]]
                    (when (unsatisfiable-as-given? identity entry) pair)))
        net))

(defn components
  "The connected components of `net`'s constraint graph, each a set of nodes: two nodes
  share one when a chain of recorded pairs joins them.  In content order, by each
  component's least node under `nm/print-key`."
  [net]
  (let [adj (reduce (fn [m [a b]] (-> m (update a (fnil conj #{}) b) (update b (fnil conj #{}) a)))
                    {} (keys net))]
    (loop [todo (set (keys adj)), out []]
      (if-let [start (first todo)]
        (let [comp (loop [seen #{start}, frontier [start]]
                     (if-let [x (peek frontier)]
                       (let [new (remove seen (adj x))]
                         (recur (into seen new) (into (pop frontier) new)))
                       seen))]
          (recur (reduce disj todo comp) (conj out comp)))
        (nm/sort-by-content-key #(nm/print-key (nm/min-by-content-key nm/print-key compare %))
                                compare out)))))

(defn drop-nodes
  "`m`, a map keyed by `[a b]` pairs, less every pair naming a node in `drop`."
  [m drop]
  (if (empty? drop)
    m
    (into {} (remove (fn [[[a b]]] (or (contains? drop a) (contains? drop b)))) m)))

(defn select-nodes
  "`m`, a map keyed by `[a b]` pairs, restricted to the pairs whose two nodes are in `keep`."
  [m keep]
  (into {} (filter (fn [[[a b]]] (and (contains? keep a) (contains? keep b)))) m))

;; ---- bitmask relation sets ----------------------------------------------
;; docs/qcn.md, "Bitmasks, not sets".

(def ^:private max-base-relations
  "The most base relations a compiled algebra may have: the bits a long holds."
  62)

(def ^:private dense-table-limit
  "The largest whole-mask composition table built, in entries; over it the table covers
  base relations only."
  (bit-shift-left 1 18))

(def ^:private decode-cache-limit 8192)

(defn- compile-algebra
  "Compile a relation algebra into its bitmask form:

    {:universe :identity  the two constants, as masks
     :ops                 an `IRelationOps` — compose and converse over masks
     :encode :decode      #{base relations} ↔ mask
     :no-op?              does the universe compose to itself?}

  Throws `:unknown-option` past `max-base-relations`."
  [{:keys [universe identity compose converse]}]
  (let [rels (into [] (sort-by nm/name-key universe))
        k    (count rels)]
    (when (> k max-base-relations)
      (throw (ex-info (str "relation algebra has " k " base relations; "
                           max-base-relations " is the most a constraint mask holds")
                      {:type :unknown-option :mismatch :bad-value :base-relations k :limit max-base-relations})))
    (let [bit       (into {} (map-indexed (fn [i r] [r (bit-shift-left 1 i)])) rels)
          ;; a relation outside the universe encodes to nothing
          mask      (fn [s] (reduce (fn [^long m r] (bit-or m (long (get bit r 0)))) 0 s))
          conv-base (long-array (map (fn [r] (mask (converse #{r}))) rels))
          comp-base (long-array (for [a rels b rels] (mask (compose #{a} #{b}))))
          size      (bit-shift-left 1 k)
          dense?    (and (<= k 20) (<= (* k size) dense-table-limit))
          conv-tbl  (long-array (if dense? size 0))
          comp-tbl  (long-array (if dense? (* k size) 0))]
      (when dense?
        ;; ascending, so `s & (s-1)` — `s` without its lowest relation — is always the
        ;; entry just filled in.
        (dotimes [i (dec size)]
          (let [s    (inc i)
                low  (Long/numberOfTrailingZeros s)
                rest (bit-and s (dec s))]
            (aset conv-tbl s (bit-or (aget conv-tbl rest) (aget conv-base low)))
            (dotimes [r k]
              (aset comp-tbl (+ (* r size) s)
                    (bit-or (aget comp-tbl (+ (* r size) rest))
                            (aget comp-base (+ (* r k) low))))))))
      (let [^IRelationOps ops (if dense?
                                (qcn-types/->DenseOps comp-tbl conv-tbl size)
                                (qcn-types/->SparseOps comp-base conv-base k))
            cache (atom {})
            decode
            (fn [^long m]
              (caches/read-through
               cache (caches/limit-of :relation-decode decode-cache-limit) m
               #(into #{} (keep-indexed (fn [i r] (when (bit-test m i) r))) rels)))
            uni (mask universe)]
        {:universe uni
         :identity (mask identity)
         :ops      ops
         :encode   mask
         :decode   decode
         ;; the atom `decode` closes over, carried out so the cache row can count it
         :decode-cache cache
         :no-op?   (= uni (.compose ops uni uni))}))))

(defonce ^{:private true
           :doc "Compiled algebras, keyed on the algebra map itself, cleared wholesale at
  `compiled-cache-limit`."}
  compiled-cache
  (atom {}))

(def ^:private compiled-cache-limit 64)

(defn- compiled
  "The bitmask form of `algebra`, built on first use."
  [algebra]
  (caches/read-through compiled-cache (caches/limit-of :compiled-algebras compiled-cache-limit) algebra
                       #(compile-algebra algebra)))

;; ---- the pass over masks -------------------------------------------------
;; Every entry point below runs one step (`stepper`) over a run-local `long[n*n]`.

(defn- encode
  "Nodes to indices, and the network to a flat array of masks.  A diagonal pair and a
  pair naming a node outside `nodes` go to `:aside` (and `:aside-support`) untouched."
  [net support nodes {:keys [^long universe encode no-op?]}]
  (let [node-vec (into [] (distinct) nodes)
        n        (count node-vec)
        index    (into {} (map-indexed (fn [i x] [x i])) node-vec)
        masks    (long-array (* n n) universe)
        recorded (BitSet. (* n n))
        sup      (when support (object-array (* n n)))]
    (loop [entries (seq net), aside (transient {}), aside-sup (transient {})]
      (if-let [[[a b :as pair] rels] (first entries)]
        (let [i (index a), j (index b)]
          (if (and i j (not= a b))
            (let [p (int (+ (* (long i) n) (long j)))]
              (aset masks p (long (encode rels)))
              (.set recorded p)
              (when sup (aset sup p (get support pair)))
              (recur (next entries) aside aside-sup))
            (recur (next entries)
                   (assoc! aside pair rels)
                   (if-let [s (get support pair)] (assoc! aside-sup pair s) aside-sup))))
        ;; `fixpoint-by-queue` seeds from the recorded pairs only under `no-op?`
        {:masks masks :recorded recorded :sup sup :n n :node-vec node-vec :index index
         :no-op? no-op? :aside (persistent! aside)
         :aside-support (persistent! aside-sup)}))))

(defn- decode-net
  "The tightened array back to a network: the recorded pairs plus the entries `encode`
  set aside.  An unrecorded pair stays absent."
  [{:keys [^longs masks ^BitSet recorded ^long n node-vec aside]} decode]
  (loop [p (.nextSetBit recorded 0), acc (transient aside)]
    (if (neg? p)
      (persistent! acc)
      (recur (.nextSetBit recorded (inc p))
             (assoc! acc [(node-vec (quot p n)) (node-vec (rem p n))]
                     (decode (aget masks p)))))))

(defn- decode-support
  "The support array back to `{[i j] → #{handle}}`, over the same pairs."
  [{:keys [^objects sup ^BitSet recorded ^long n node-vec aside-support]}]
  (loop [p (.nextSetBit recorded 0), acc (transient aside-support)]
    (if (neg? p)
      (persistent! acc)
      (recur (.nextSetBit recorded (inc p))
             (if-let [s (aget sup p)]
               (assoc! acc [(node-vec (quot p n)) (node-vec (rem p n))] s)
               acc)))))

(defn- union3
  "The union of the support at three array positions: a narrowing constraint's own prior
  support and the supports of the two that composed to narrow it."
  [^objects sup ^long a ^long b ^long c]
  (-> (or (aget sup a) #{})
      (into (or (aget sup b) #{}))
      (into (or (aget sup c) #{}))))

(defn- stepper
  "The tightening step for one run: `(fn [i j k])` applying `R(i,k) ∩= R(i,j)∘R(j,k)` over
  node indices, writing both directions and their support (`union3`), with three
  outcomes —

    nil                                     nothing narrowed
    :narrowed                               the array now holds the tighter constraint
    {::inconsistent [i k] ::culprits …}     the constraint emptied

  Under `no-op?` a triple whose two inputs are both the universe is skipped."
  [{:keys [^longs masks ^objects sup ^BitSet recorded ^long n]}
   {:keys [^long universe no-op?] :as compiled}]
  (let [^IRelationOps ops (:ops compiled)]
    (fn [^long i ^long j ^long k]
      (let [pij (+ (* i n) j)
            pjk (+ (* j n) k)
            rij (aget masks pij)
            rjk (aget masks pjk)]
        (when-not (and no-op? (== universe rij) (== universe rjk))
          (let [pik (+ (* i n) k)
                rik (aget masks pik)
                new (bit-and rik (.compose ops rij rjk))]
            (cond
              (== new rik) nil

              (zero? new)
              {::inconsistent [i k] ::culprits (when sup (union3 sup pik pij pjk))}

              :else
              (let [pki (+ (* k n) i)]
                (aset masks (int pik) new)
                (aset masks (int pki) (.converse ops new))
                (.set recorded (int pik))
                (.set recorded (int pki))
                (when sup
                  (let [s (union3 sup pik pij pjk)]
                    (aset sup (int pik) s)
                    (aset sup (int pki) s)))
                :narrowed))))))))

(defn- walk-triples
  "Apply `f` to every ordered triple (i j k) of distinct indices below `n`, in index
  order, stopping at the first inconsistency report — a map — which it returns."
  [^long n f]
  (loop [i 0, j 0, k 0]
    (cond
      (== i n)                       nil
      (== j n)                       (recur (inc i) 0 0)
      (== k n)                       (recur i (inc j) 0)
      (or (== i j) (== j k) (== i k)) (recur i j (inc k))
      :else                          (let [r (f i j k)]
                                       (if (map? r) r (recur i j (inc k)))))))

(defn- walk-reading
  "Apply `f` to the triples that read the constraint on `[a b]`: `(a b m)` and `(m a b)`
  for every other `m`.  Stops at the first report."
  [^long n ^long a ^long b f]
  (loop [m 0]
    (cond
      (== m n)                nil
      (or (== m a) (== m b))  (recur (inc m))
      :else                   (let [r (f a b m)]
                                (if (map? r)
                                  r
                                  (let [r2 (f m a b)]
                                    (if (map? r2) r2 (recur (inc m)))))))))

(defn- sweep
  "Tighten over every triple, recording into `changed` the array positions that narrowed.
  Returns nil, or the inconsistency report."
  [step ^long n ^LinkedHashSet changed]
  (walk-triples n (fn [^long i ^long j ^long k]
                    (let [r (step i j k)]
                      (when (identical? :narrowed r)
                        (.add changed (Long/valueOf (+ (* i n) k)))
                        (.add changed (Long/valueOf (+ (* k n) i))))
                      r))))

(defn- drain
  "The arc queue (PC-2): pop a pair, tighten the triples that read it, enqueue whatever
  that narrows, until the queue empties.  Returns nil, or the inconsistency report.
  `budget` caps the pops, past which it returns `::over-budget` with the array narrowed
  so far."
  ([step n seed] (drain step n seed Long/MAX_VALUE))
  ([step ^long n ^LinkedHashSet seed ^long budget]
   (let [queue  (ArrayDeque. seed)
         queued (LinkedHashSet. seed)
         push!  (fn [^long p]
                  (let [b (Long/valueOf p)]
                    (when (.add queued b) (.add queue b))))
         visit  (fn [^long i ^long j ^long k]
                  (let [r (step i j k)]
                    (when (identical? :narrowed r)
                      (push! (+ (* i n) k))
                      (push! (+ (* k n) i)))
                    r))]
     (loop [pops 0]
       (let [p (.poll queue)]
         (cond
           (nil? p)         nil
           (> pops budget)  ::over-budget
           :else            (let [pl (long p)]
                              (.remove queued p)
                              (if-let [bad (walk-reading n (quot pl n) (rem pl n) visit)]
                                bad
                                (recur (inc pops))))))))))

(defn- fixpoint-by-sweep
  "Sweep every triple, and sweep again while anything narrowed."
  [step ^long n _state]
  (loop []
    (let [changed (LinkedHashSet.)
          bad     (sweep step n changed)]
      (cond
        bad                bad
        (.isEmpty changed) nil
        :else              (recur)))))

(defn- recorded-seeds
  "The recorded array positions, both directions, as a queue seed."
  [^BitSet recorded ^long n]
  (let [seeds (LinkedHashSet.)]
    (loop [p (.nextSetBit recorded 0)]
      (when-not (neg? p)
        (.add seeds (Long/valueOf p))
        (.add seeds (Long/valueOf (+ (* (rem p n) n) (quot p n))))
        (recur (.nextSetBit recorded (inc p)))))
    seeds))

(defn- fixpoint-by-queue
  "The driver of `path-consistent`: drain or sweep, by comparing the two visit counts
  (docs/qcn.md, \"The arc queue\").  The first look drains from `recorded-seeds` under
  `no-op?` and a budget of one sweep's pops, and sweeps when the seed is too large or the
  budget runs out; after a sweep, the changed pairs drain while they cost less than
  another sweep."
  [step ^long n state]
  (let [sweep-cost (* n (max 0 (dec n)))
        sweeping   (fn []
                     (loop []
                       (let [changed (LinkedHashSet.)
                             bad     (sweep step n changed)]
                         (cond
                           bad                                  bad
                           (.isEmpty changed)                   nil
                           (< (* 2 (.size changed)) sweep-cost) (drain step n changed)
                           :else                                (recur)))))
        seeds      (when (:no-op? state)
                     (let [^LinkedHashSet s (recorded-seeds (:recorded state) n)]
                       (when (< (* 2 (.size s)) sweep-cost) s)))]
    (if (nil? seeds)
      (sweeping)
      (let [r (drain step n seeds (quot sweep-cost 2))]
        (if (identical? ::over-budget r) (sweeping) r)))))

(defn- fixpoint-from
  "The warm-started driver, for an array path-consistent except at `seed-pairs`: drain
  from those, or hand over to `fixpoint-by-queue` when they cost more than a sweep."
  [seed-pairs]
  (fn [step ^long n state]
    (let [index (:index state)
          seeds (LinkedHashSet.)]
      (doseq [[a b] seed-pairs
              :let  [i (index a), j (index b)]
              :when (and i j (not= a b))]
        (.add seeds (Long/valueOf (+ (* (long i) n) (long j))))
        (.add seeds (Long/valueOf (+ (* (long j) n) (long i)))))
      (cond
        (.isEmpty seeds)                              nil
        (< (* 2 (.size seeds)) (* n (max 0 (dec n)))) (drain step n seeds)
        :else                                         (fixpoint-by-queue step n state)))))

(defn- given-inconsistency
  "The inconsistency report for a network unsatisfiable before any tightening, or nil,
  blaming the smallest such pair under `nm/print-key`."
  [net support algebra]
  (let [bad (unsatisfiable-pairs net algebra)]
    (when (seq bad)
      (let [pair (nm/min-by-content-key nm/print-key compare bad)]
        {::inconsistent pair ::culprits (get support pair #{})}))))

(defn- run
  "Every entry point's run: `given-inconsistency`, else encode, run `driver` to the
  fixpoint, decode.  Returns `{:net … :support …}` or the inconsistency report, its pair
  named in nodes."
  [net support nodes algebra driver]
  (or (given-inconsistency net support algebra)
      (let [c     (compiled algebra)
            state (encode net support nodes c)
            bad   (driver (stepper state c) (:n state) state)]
        (if bad
          (let [[i k] (::inconsistent bad)
                nv    (:node-vec state)]
            {::inconsistent [(nv i) (nv k)] ::culprits (::culprits bad)})
          {:net     (decode-net state (:decode c))
           :support (when support (decode-support state))}))))

(defn path-consistent-naive
  "`path-consistent` by repeated full sweeps of every triple: the same arguments and
  answer, kept as the reference `qcn_queue_test` holds the arc queue against."
  [net nodes algebra]
  (let [outcome (run net nil nodes algebra fixpoint-by-sweep)]
    (if (::inconsistent outcome) :inconsistent (:net outcome))))

(defn path-consistent
  "Enforce composition closure over `net` across `nodes`: for every triple (i j k),
  tighten R(i,k) ∩= R(i,j)∘R(j,k), to the greatest fixpoint below `net`.  Returns the
  tightened network, or `:inconsistent` when a constraint empties or one is unsatisfiable
  as given (`unsatisfiable-as-given?`, over the whole network whatever `nodes` holds).

  Each constraint is a subset of the algebra's universe.  `nodes` must name every node
  the network mentions: a node left out takes part in no triple.  Extra nodes change
  nothing, and the order of `nodes` changes nothing."
  [net nodes algebra]
  (let [outcome (run net nil nodes algebra fixpoint-by-queue)]
    (if (::inconsistent outcome) :inconsistent (:net outcome))))

;; ---- warm-starting: semi-naive over the network --------------------------
;; docs/qcn.md, "Warm-starting: semi-naive over the network".

(defn narrowing-of?
  "Is `net` a pointwise narrowing of `prior`: is every pair's constraint at most as wide,
  a pair `net` does not record being the universe?  The precondition of
  `path-consistent-from`, checked by the caller against the network `prior`'s answer was
  computed from."
  [net prior {:keys [universe]}]
  (every? (fn [[pair rels]] (set/subset? (get net pair universe) rels)) prior))

(defn path-consistent-from
  "`path-consistent` for `net`, warm-started from `prior`, the answer for an earlier
  network `net` narrows (`narrowing-of?`): it closes `prior ∩ net`, revisiting only the
  triples reading a pair where `net` is stricter.  `nodes` need name only the nodes
  neither network mentions; the rest are read off the merged network.  A `prior` that
  fails the precondition, or comes from another algebra, yields a network tighter than
  `net` licenses."
  [net prior nodes algebra]
  (let [{:keys [universe]} algebra
        merged (reduce-kv (fn [m pair rels]
                            (assoc m pair (set/intersection (get net pair universe) rels)))
                          net prior)
        seeds  (into [] (keep (fn [[pair rels]]
                                (when-not (= rels (get prior pair universe)) pair)))
                     merged)
        ns'    (into (set nodes) (mapcat identity) (keys merged))
        outcome (run merged nil ns' algebra (fixpoint-from seeds))]
    (if (::inconsistent outcome) :inconsistent (:net outcome))))

(defn path-consistent-with-support
  "`path-consistent`, carrying support from the asserted `support` `{[i j] → #{handle}}`:
  a tightened constraint's support is its own prior support and that of the two
  constraints that narrowed it.  Returns `{:network … :support …}`, or
  `{:inconsistent [i j] :culprits #{handle}}` for the pair that emptied.  The support is
  one witness, not minimal and not every derivation, and every handle in it was read into
  the network (docs/qcn.md, \"Support\")."
  [net support nodes algebra]
  (let [outcome (run net (or support {}) nodes algebra fixpoint-by-queue)]
    (if-let [pair (::inconsistent outcome)]
      {:inconsistent pair :culprits (or (::culprits outcome) #{})}
      {:network (:net outcome) :support (:support outcome)})))

;; ---- what the algebras hold, declared -----------------------------------
;; Process-wide and keyed on the algebra value; neither row offers a clear (docs/caches.md).

(caches/register-cache
 {:cache    :compiled-algebras
  :label    "Compiled algebras"
  :scope    :process
  :unit     "algebras"
  :limit    (caches/limit-thunk :compiled-algebras compiled-cache-limit)
  :counters nil
  :note     (str "Each relation algebra's composition and converse tables, in bitmask "
                 "form, keyed on the algebra itself. One entry per calculus in use, so "
                 "this fills once and never turns over; the bound is for a caller "
                 "building algebras on the fly.")
  :read     (fn [_] {:entries (count @compiled-cache)})})

(caches/register-cache
 {:cache    :relation-decode
  :label    "Relation decode tables"
  :scope    :process
  :unit     "masks"
  :limit    (caches/limit-thunk :relation-decode decode-cache-limit)
  :counters nil
  :note     (str "One decoded relation set per bitmask the tightening pass has handed "
                 "back, held per compiled algebra — so the limit is per algebra and the "
                 "count here is the total across all of them.")
  :read     (fn [_] {:entries (reduce + 0 (map #(count @(:decode-cache %))
                                               (vals @compiled-cache)))})})

(caches/register-derived
 {:id :K2 :label "Compiled algebras" :cache :compiled-algebras :kind :cache :keyed-by :value
  :holds-content? false
  :reads [] :retired-by {} :computed :read :imaged? false :var #'compiled-cache
  :value (fn [_] (set (keys @compiled-cache)))
  :note "content-keyed by algebra value; cleared at the bound"})

(caches/register-derived
 {:id :K3 :label "Relation decode tables" :cache :relation-decode :kind :cache
  :holds-content? false
  :keyed-by :value :reads [:K2] :retired-by {:caches-cleared :W} :computed :read
  :imaged? false :var #'compiled-cache
  :value (fn [_] (into {} (map (fn [[a c]] [a (some-> (:decode-cache c) deref)]))
                       @compiled-cache))
  :note "content-keyed by mask, per algebra; cleared at the bound"})

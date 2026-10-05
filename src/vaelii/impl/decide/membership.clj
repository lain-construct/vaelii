;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.decide.membership
  "The membership families: two memberships of one term whose types a separation holds
  apart (`disjoint`), and a membership under a cover's whole beside a denial of each part
  (`covering`).  See docs/nmtms.md, \"Nogoods decided at the reader\"."
  (:require [vaelii.impl.protocols :as p]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]))

;; ---- the membership families ---------------------------------------------
;;
;; A `disjoint` nogood is two memberships of one term whose types a separation a reader
;; sees holds apart, and a `covering` nogood is a membership under a cover's whole with
;; one denial of each part or of a supertype of it.  Both are keyed by the term, so the
;; candidate index keeps each term holding two memberships, or a membership and a denial,
;; under `::mem` as `{x {h [type context positive?]}}`, read off the term's unary roster
;; once and kept in step after.  `::tpairs` holds each pair of types some kept term
;; holds, `{[ta tb] #{x}}`, and `::sep` the pairs the unscoped taxonomy separates with no
;; `orthogonal` read, `::spared` those of them a stored `orthogonal` exempts,
;; both read again over `::tpairs` when `tax/separation-stamp` moves (`sync-memberships`),
;; which reads no membership.  A term holding a separated pair, or a membership under a cover
;; beside a denial, is live under `::live-mem`, and its memberships and denials there are
;; the family's candidates under `:membership`.  `::denied` holds the kept terms with a
;; denial.

(def ^:dynamic ^:private *membership-entries*
  "A volatile map `{x {h [type context positive?]}}` while `rebuild-candidates!` replays
  storage: each membership and denial is kept here instead, and the replay's end keeps
  the terms `held?` names.  nil otherwise."
  nil)

(defn- membership-of
  "`[x t positive?]` for a stored fact `sx` whose sentence is `(t x)` or `(not (t x))`
  with `t` and `x` plain symbols, else nil."
  [sx]
  (when (nil? (:antecedent sx))
    (let [s   (:sentence sx)
          neg (sx/negation? s)
          b   (if neg (second s) s)]
      (when (and (seq? b) (= 2 (count b)))
        (let [[t x] b]
          (when (and (sx/plain-symbol? t) (not= 'not t) (sx/plain-symbol? x))
            [x t (not neg)]))))))

(defn- term-entries
  "`{h [t context positive?]}` of the stored memberships and denials of `x`, read off its
  unary roster (`p/unary-sentexes-with-arg`, a superset filtered here), so the facts
  holding `x` at argument 1 of a longer tuple are not fetched."
  [kb x]
  (let [recs (:records kb)]
    (into {}
          (keep (fn [h]
                  (when-let [sx (p/get-sentex recs h)]
                    (when-let [[x' t pos] (membership-of sx)]
                      (when (= x x') [h [t (:context sx) pos]])))))
          (p/unary-sentexes-with-arg (:index kb) x))))

(defn- held?
  "Can the entries `m` of one term form a nogood: two memberships, or a membership and a
  denial?"
  [m]
  (let [pos (count (filter #(nth % 2) (vals m)))]
    (or (< 1 pos) (and (pos? pos) (< pos (count m))))))

(defn- type-pairs
  "The pairs of distinct types the memberships among the entries `m` hold, each sorted."
  [m]
  (let [ts (into (sorted-set) (keep (fn [[t _ pos]] (when pos t))) (vals m))]
    (for [[i a] (map-indexed vector ts), b (drop (inc i) ts)] [a b])))

(defn- separation-tests
  "`(fn [[a b]])` → how the unscoped taxonomy separates the types `a` and `b`: nil when
  it does not with no `orthogonal` read, `:spared` when it does and a stored `orthogonal`
  exempts the pair, `:sep` otherwise.  An `orthogonal` exempts the pair only at a reader
  that sees it, so a reader may read a `:spared` pair separated.  Each type's
  separation frame is read once per call (`tax/disjointness-test`), so a type no
  declaration reaches reads its supertype closure once and tests no partner."
  [tax]
  (let [strict (memoize #(tax/disjointness-test tax % nil (constantly false)))
        exempt (when (tax/orthogonals? tax) (memoize #(tax/disjointness-test tax % nil)))
        sep?   (fn [test a b] (or ((test a) b) ((test b) a)))]
    (fn [[a b]]
      (when (sep? strict a b)
        (if (and exempt (not (sep? exempt a b))) :spared :sep)))))

(defn- combinations
  "The cartesian product of the collections `colls`, each product a vector."
  [colls]
  (reduce (fn [acc c] (for [xs acc x c] (conj xs x))) [[]] colls))

(defn- term-nogoods
  "The membership nogoods of term `x` (`::mem`), each `{:members #{h} :kind k}`: two
  memberships of distinct types a separation holds apart, `:disjoint`, and a membership
  under a cover's whole with, for each part, a denial of the part or of a supertype of
  it, `:cover`, one nogood per choice of denials.  Read by a reader with ancestor set
  `up`, over its entries in `up` and not `hidden?` (or nil), through the separations,
  covers, exceptions and `genl` edges some supporter states in `up` (`tax/disjoint?` and
  `tax/covers-over` over an ancestor set), with no belief callback, so this runs inside
  the reader's own withdrawal.  With `up` nil it reads every entry through the write
  view `w` (`decide/write-view`), the separated pairs read off `::sep`, and a pair of
  `::spared` gives a nogood marked `:spared? true`."
  [tax w c x up hidden?]
  (let [m     (get-in c [::mem x])
        vis   (filterv (fn [[h [_ cx]]] (and (or (nil? up) (nil? cx) (contains? up cx))
                                             (not (and hidden? (hidden? h)))))
                       m)
        pos   (filterv #(nth (val %) 2) vis)
        neg   (filterv #(not (nth (val %) 2)) vis)
        sep   (::sep c #{})
        spare (::spared c #{})
        sep?  (if up
                (memoize (fn [a b] (or (tax/disjoint? tax a b up) (tax/disjoint? tax b a up))))
                (fn [a b] (contains? sep (if (neg? (compare a b)) [a b] [b a]))))
        above (if up #(tax/genls-asserted-in tax % up) (:genls-global w))]
    (concat
     (for [[i [h1 [t1]]] (map-indexed vector pos)
           [h2 [t2]]     (drop (inc i) pos)
           :when (and (not= t1 t2) (sep? t1 t2))]
       (cond-> {:members #{h1 h2} :kind :disjoint}
         (and (nil? up) (contains? spare (if (neg? (compare t1 t2)) [t1 t2] [t2 t1])))
         (assoc :spared? true)))
     (when (and (seq neg) (seq (tax/coverings tax)))
       (for [[h [s]]   pos
             [_ parts] (distinct (tax/covers-over tax s up))
             :let [per (for [p (distinct parts)
                             :let [ups (above p)]]
                         (for [[d [q]] neg :when (contains? ups q)] d))]
             :when (every? seq per)
             combo (combinations per)]
         {:members (into #{h} combo) :kind :cover})))))

(defn- scoped-reads
  "`(fn [x up ng])` → does a reader with ancestor set `up` read the kept nogood `ng` of
  term `x`: every context asserting a `genl` edge or a declaration
  (`tax/asserting-contexts`) is in `up` and `ng` is not `:spared?`, so the reader reads
  what the unscoped taxonomy reads, or `term-nogoods` over `up` finds it.  A `:spared?`
  nogood takes the second path, since the exception exempts it only at a reader that
  sees one.  The second is memoized per term and ancestor set.  No belief callback is
  read, so this runs inside a withdrawal and inside the candidate index's own update."
  [tax c]
  (let [ground (tax/asserting-contexts tax)
        whole? (memoize (fn [up] (every? #(contains? up %) ground)))
        reads  (memoize (fn [x up] (into #{} (map :members) (term-nogoods tax nil c x up nil))))]
    (fn [x up {:keys [members spared?]}]
      (or (and (not spared?) (whole? up)) (contains? (reads x up) members)))))

(defn- place-term
  "`c` with term `x`'s nogoods read again through the unscoped taxonomy (`term-nogoods`),
  kept under `::ngs` while it has one; their members are under `::live-mem` and in step
  in `:membership`.  A term with no separated pair (`::sep`) and no denial under a stored
  cover has none, and is read no further."
  [w c x]
  (let [tax (:tax w)
        old (get-in c [::live-mem x])
        m   (get-in c [::mem x])
        sep (::sep c #{})
        ngs (when (and m (or (some #(contains? sep %) (type-pairs m))
                             (and (contains? (::denied c) x) (seq (tax/coverings tax)))))
              (not-empty (vec (term-nogoods tax w c x nil nil))))
        new (not-empty (into #{} (mapcat :members) ngs))]
    (as-> c c
      (if (seq ngs) (assoc-in c [::ngs x] ngs) (update c ::ngs #(some-> % (dissoc x))))
      (if (= old new)
        c
        (-> c
            (update :membership #(into (reduce disj (or % #{}) old) new))
            (update ::live-mem #(if new (assoc (or % {}) x new) (dissoc % x))))))))

(defn- index-pair
  "`c` with the type pair `pr` under each of its two types in `::by-type` (`f` conj or
  disj)."
  [c pr f]
  (reduce (fn [c t] (let [ps (f (get-in c [::by-type t] #{}) pr)]
                      (if (seq ps) (assoc-in c [::by-type t] ps) (update c ::by-type dissoc t))))
          c pr))

(defn- set-term
  "`c` with term `x`'s entries replaced by `m`, dropped when `m` is not `held?`:
  `::mem`, `::tpairs`, `::by-type`, `::denied`, `::sep` and `::spared` in step, a pair new to
  `::tpairs` tested against the taxonomy as it stands, and `x` placed (`place-term`)."
  [w c x m]
  (let [m    (when (and (seq m) (held? m)) m)
        sep? (separation-tests (:tax w))
        was  (set (type-pairs (get-in c [::mem x])))
        now (set (type-pairs m))
        c   (as-> c c
              (if m (assoc-in c [::mem x] m) (update c ::mem dissoc x))
              (if (some #(not (nth % 2)) (vals m))
                (update c ::denied (fnil conj #{}) x)
                (update c ::denied #(some-> % (disj x))))
              (reduce (fn [c pr]
                        (let [xs (disj (get-in c [::tpairs pr]) x)]
                          (if (empty? xs)
                            (-> c (update ::tpairs dissoc pr) (update ::sep #(some-> % (disj pr)))
                                (update ::spared #(some-> % (disj pr))) (index-pair pr disj))
                            (assoc-in c [::tpairs pr] xs))))
                      c (remove now was))
              (reduce (fn [c pr]
                        (let [fresh? (not (contains? (::tpairs c) pr))
                              c      (cond-> (update-in c [::tpairs pr] (fnil conj #{}) x)
                                       fresh? (index-pair pr conj))
                              how    (when fresh? (sep? pr))]
                          (cond-> c
                            how             (update ::sep (fnil conj #{}) pr)
                            (= :spared how) (update ::spared (fnil conj #{}) pr))))
                      c (remove was now)))]
    (place-term w c x)))

(defn- membership-synced?
  "Is `c`'s membership index read under the taxonomy as it stands: the declarations
  (`tax/separation-stamp`), each roster the identical value, and the `genl` generation?
  A roster equal and not identical answers false, and `sync-memberships` takes the
  taxonomy's (docs/nmtms.md, \"How a settle finds the clashes\")."
  [tax c]
  (let [seen (::sep-stamp c)]
    (and (some? seen)
         (let [st (tax/separation-stamp tax)]
           (and (= (count st) (count seen)) (every? true? (map identical? st seen))))
         (= (tax/relation-gen tax :genl) (::genl-seen c)))))

(defn- sync-memberships
  "`c` with `::sep` and the kept nogoods read again under the taxonomy as it stands.  When
  a declaration moved (`tax/separation-stamp`), or the `genl` relation was rebuilt from
  nothing, every pair of `::tpairs` is tested again.  When only `genl` edges moved, the
  pairs holding a type at or below the lower end of a moved edge are (`tax/moves-since`,
  `::by-type`), since no other type's closure moved.  The terms holding a pair tested
  and separated (every one tested when the edges moved), and the terms with a denial, are
  placed again; on a full test, so is every term holding nogoods.  Reads no membership."
  [w c]
  (let [tax  (:tax w)
        st   (tax/separation-stamp tax)
        g    (tax/relation-gen tax :genl)
        seen (::genl-seen c)
        test (separation-tests tax)
        full (or (not= st (::sep-stamp c)) (nil? seen) (< g seen))
        prs  (cond full        (keys (::tpairs c))
                   (not= g seen) (into #{}
                                       (comp (mapcat (:specs-global w))
                                             (mapcat #(get-in c [::by-type %])))
                                       (tax/moves-since tax :genl seen))
                   :else       nil)
        [sep spared] (reduce (fn [[sep spared] pr]
                               (let [how (test pr)]
                                 [(if how (conj sep pr) (disj sep pr))
                                  (if (= :spared how) (conj spared pr) (disj spared pr))]))
                             (if full [#{} #{}] [(::sep c #{}) (::spared c #{})]) prs)
        xs   (cond-> (into #{} (mapcat #(get-in c [::tpairs %])) (if full sep prs))
               (or full (not= g seen)) (into (::denied c))
               full                    (into (keys (::ngs c))))
        c    (assoc c ::sep sep ::spared spared ::sep-stamp st ::genl-seen g)]
    (reduce #(place-term w %1 %2) c xs)))

(defn- add-held
  "`c` with the kept term `x`'s entries `m` and its type pairs recorded, and no separation
  read: `rebuild-candidates!`' step, which leaves the separations to `sync-memberships`."
  [c x m]
  (as-> c c
    (assoc-in c [::mem x] m)
    (if (some #(not (nth % 2)) (vals m)) (update c ::denied (fnil conj #{}) x) c)
    (reduce (fn [c pr] (-> c (update-in [::tpairs pr] (fnil conj #{}) x) (index-pair pr conj)))
            c (type-pairs m))))

(defn- note-membership!
  "Keep the membership candidates in step with the fact `sx` arriving (`stored?` true) or
  leaving.  A membership or a denial of a kept term joins it with no read.  One of a term
  not kept reads the term's unary roster once (`term-entries`), and keeps the term
  when it holds two memberships or a membership and a denial.  A term that read holds
  denials and no membership is noted under `::no-pos`, so a further denial of it reads
  nothing, and its first membership reads the roster once and keeps it.  A declaration
  arriving reads nothing here: `sync-memberships` reads its separations over `::tpairs`."
  [kb w sx stored?]
  (when-let [[x t pos] (membership-of sx)]
    (let [h     (:id sx)
          e     [t (:context sx) pos]
          cands (reasoning/nogood-candidates kb)]
      (cond
        (some? *membership-entries*)
        (when stored? (vswap! *membership-entries* assoc-in [x h] e))

        (contains? (::mem @cands) x)
        (swap! cands (fn [c]
                       (let [c (if (membership-synced? (:tax w) c) c (sync-memberships w c))
                             m (get-in c [::mem x])]
                         (set-term w c x (if stored? (assoc m h e) (dissoc m h))))))

        (and stored? (not pos) (contains? (::no-pos @cands) x))
        nil

        stored?
        (let [m (assoc (term-entries kb x) h e)]
          (cond
            (held? m)
            (swap! cands (fn [c]
                           (-> (if (membership-synced? (:tax w) c) c (sync-memberships w c))
                               (update ::no-pos #(some-> % (disj x)))
                               (as-> c (set-term w c x (merge m (get-in c [::mem x])))))))

            (not-any? #(nth % 2) (vals m))
            (swap! cands update ::no-pos (fnil conj #{}) x)))))))

(defn- membership-nogoods
  "The membership nogoods a reader with ancestor set `up` decides, each `{:members :marks
  #{} :kind :definitional? true}`: each live term's nogoods (`::ngs`) whose members the
  reader sees, in `up` and not `hidden?`, and that the reader reads (`scoped-reads`).  `:definitional?` has `losers` read a nogood
  again once the reader withdraws a ground it was found through or an equality supporter."
  [kb c up hidden?]
  (when (seq (::live-mem c))
    (let [reads? (scoped-reads (reasoning/taxonomy kb) c)]
      (for [x (keys (::live-mem c))
            :let [m (get-in c [::mem x])]
            {:keys [members] :as ng} (get-in c [::ngs x])
            :when (and (every? (fn [h] (let [cx (second (get m h))]
                                         (and (or (nil? cx) (contains? up cx))
                                              (not (and hidden? (hidden? h))))))
                               members)
                       (reads? x up ng))]
        {:members members :marks #{} :kind (:kind ng) :definitional? true}))))

(defn membership-vantages
  "The most general contexts of `ctxs`, over the unscoped `genlCx` closure, that read the
  membership nogood `members`: each sees every member's context and reads the nogood over its unscoped ancestor set, with no
  `except` read (`scoped-reads`).  nil when `members` is no membership nogood the candidate
  index keeps.  `c` is the candidate index as `decide/synced` answers it."
  [kb c members ctxs]
  (let [[x ng] (some (fn [[x ngs]] (some #(when (= members (:members %)) [x %]) ngs)) (::ngs c))]
    (when x
      (let [tax    (reasoning/taxonomy kb)
            reads? (scoped-reads tax c)
            m      (get-in c [::mem x])
            mcs    (into #{} (keep #(second (get m %))) members)
            at     (fn [cx] (let [up (tax/context-up-global tax cx)]
                              (and (every? #(contains? up %) mcs) (reads? x up ng))))]
        ;; maximal over the unscoped closure the readers decide over, as belief reads it
        (let [cs (into #{} (filter at) ctxs)
              up #(tax/context-up-global tax %)]
          (into #{} (remove (fn [c] (some #(and (not= c %) (contains? (up c) %)
                                                (not (contains? (up %) c)))
                                          cs)))
                cs))))))

(def family
  "The membership family's entry in `decide/registry`.  A replay keeps each term's entries
  and keeps the terms `held?` names after it, with no separation read: the first read
  after it tests every pair once (`sync-memberships`)."
  {:note!     (fn [kb w sx stored? _] (note-membership! kb w sx stored?))
   :replay    (fn [] {#'*membership-entries* (volatile! {})})
   :replayed  (fn [_ _ c]
                (let [held (into {} (filter #(held? (val %))) @*membership-entries*)]
                  (if (seq held)
                    (dissoc (reduce-kv add-held c held) ::sep-stamp ::genl-seen)
                    c)))
   :synced?   (fn [tax c] (or (empty? (::mem c)) (membership-synced? tax c)))
   :sync      sync-memberships
   :handles   :membership
   :live?     (fn [_ c] (seq (:membership c)))
   :unstamped #{::mem ::tpairs ::sep ::spared ::sep-stamp ::live-mem ::denied ::ngs
                ::by-type ::genl-seen ::no-pos}
   :nogoods   membership-nogoods})

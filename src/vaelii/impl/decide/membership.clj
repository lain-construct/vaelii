;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.decide.membership
  "The membership families: two memberships of one term whose types a separation holds
  apart (`disjoint`), and a membership under a cover's whole beside a denial of each part
  (`covering`), placed as nogoods (`chain/place-memberships!`).  See docs/nmtms.md, \"A
  nogood placed as a conclusion\"."
  (:require [vaelii.impl.caches :as caches]
            [vaelii.impl.journal :as journal]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
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
;; once and kept in step after.  `::by-type` holds the kept terms by the types their
;; memberships hold, `{t {x #{h}}}`, one entry per membership.  `::sep` holds, per kept
;; term, the pairs of its types the unscoped taxonomy separates with no exception read,
;; `{x {[ta tb] how}}`, `how` `:spared` when a stored `siblingDisjointException` exempts the pair and
;; `:sep` otherwise.  A pair is tested when its second type arrives at the term, and again
;; when `tax/separation-stamp` or a `genl` edge moves over one of its types
;; (`sync-memberships`), which reads no membership.  A term holding a separated pair, or a
;; membership under a cover beside a denial, is live under `::live-mem`, and its
;; memberships and denials there are the family's candidates under `:membership`.
;; `::denied` holds the kept terms with a denial, and `::moved` the terms whose nogoods
;; the settle places again (`take-moved!`).  Recover keeps the terms of two unary
;; predicates (`reads/as-stored-unary-multi-terms`) and of a unary body stored in both
;; polarities that hold two memberships or a membership and a denial, read off their
;; unary rosters (`recovered-terms`).

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
  denial?  Reads entries until they answer it."
  [m]
  (true? (reduce (fn [[p n] [_ _ pos]]
                   (let [p (cond-> p pos inc)
                         n (cond-> n (not pos) inc)]
                     (if (or (< 1 p) (and (pos? p) (pos? n))) (reduced true) [p n])))
                 [0 0] (vals m))))

(defn- separation-tests
  "`(fn [a])` → nil when no separation reaches the type `a` over the unscoped taxonomy
  (`tax/separation-test`), else `(fn [b])` → how it separates `a` and `b`: nil when it
  does not with no exception read, `:spared` when it does and a stored
  `siblingDisjointException` exempts the pair, `:sep` otherwise.  An exception exempts the pair only at a reader
  that sees it, so a reader may read a `:spared` pair separated.  The unscoped test is
  symmetric, so `a`'s test alone decides each pair."
  [tax]
  (let [exc? (tax/sib-exceptions? tax)]
    (fn [a]
      (when-let [strict (tax/separation-test tax a nil (constantly false))]
        (let [exempt (when exc? (tax/disjointness-test tax a nil))]
          (fn [b]
            (when (strict b)
              (if (and exempt (not (exempt b))) :spared :sep))))))))

(defn- pair-of [a b] (if (neg? (compare a b)) [a b] [b a]))

(defn- untest
  "`c` with the separated pairs of term `x` holding type `t` dropped."
  [c x t]
  (let [left (into {} (remove #(some #{t} (key %))) (get-in c [::sep x]))]
    (if (seq left) (assoc-in c [::sep x] left) (update c ::sep dissoc x))))

(defn- test-type
  "`c` with the pair of type `t` and each other type term `x` holds tested (`test`,
  `separation-tests`), and the separated ones under `::sep`.  Tests no partner when no
  separation reaches `t`."
  [test c x t]
  (if-let [f (test t)]
    (reduce (fn [c b]
              (if-let [how (and (not= b t) (f b))]
                (assoc-in c [::sep x (pair-of t b)] how)
                c))
            c (into #{} (keep (fn [[b _ pos]] (when pos b))) (vals (get-in c [::mem x]))))
    c))

(defn- add-entry
  "`c` with the entry `e` of handle `h` added to term `x`: a membership under `::by-type`,
  its type tested against the term's others when it is new to the term (`test-type`), or
  a denial under `::denied`."
  [test c x h [t _ pos :as e]]
  (let [c (assoc-in c [::mem x h] e)]
    (if-not pos
      (update c ::denied (fnil conj #{}) x)
      (let [fresh? (empty? (get-in c [::by-type t x]))
            c      (update-in c [::by-type t x] (fnil conj #{}) h)]
        (if fresh? (test-type test c x t) c)))))

(defn- drop-type
  "`c` with term `x` out of `::by-type` under type `t`, and the separated pairs of `x`
  holding `t` dropped."
  [c x t]
  (let [xs (dissoc (get-in c [::by-type t]) x)]
    (untest (if (seq xs) (assoc-in c [::by-type t] xs) (update c ::by-type dissoc t)) x t)))

(defn- remove-entry
  "`c` with handle `h`'s entry removed from term `x`: a membership's type leaves the term
  when no other membership of `x` holds it (`drop-type`), and `x` leaves `::denied` with
  its last denial."
  [c x h]
  (if-let [[t _ pos] (get-in c [::mem x h])]
    (let [c (update-in c [::mem x] dissoc h)]
      (if-not pos
        (if (some #(not (nth % 2)) (vals (get-in c [::mem x])))
          c
          (update c ::denied #(some-> % (disj x))))
        (let [hs (disj (get-in c [::by-type t x]) h)]
          (if (seq hs) (assoc-in c [::by-type t x] hs) (drop-type c x t)))))
    c))

(defn- drop-term
  "`c` with term `x` and every row naming it dropped."
  [c x]
  (as-> c c
    (reduce #(drop-type %1 x %2) c (into #{} (keep (fn [[t _ pos]] (when pos t)))
                                         (vals (get-in c [::mem x]))))
    (-> c (update ::mem dissoc x) (update ::sep dissoc x) (update ::denied #(some-> % (disj x))))))

(defn- combinations
  "The cartesian product of the collections `colls`, each product a vector."
  [colls]
  (reduce (fn [acc c] (for [xs acc x c] (conj xs x))) [[]] colls))

(defn- term-nogoods
  "The membership nogoods of term `x` (`::mem`), each `{:members #{h} :kind k}`: two
  memberships of a pair of types a separation holds apart (`::sep`, a superset over every
  reader), `:disjoint`, marked `:spared? true` for a pair a stored exception exempts;
  and a membership under a cover's whole with, for each part, a denial of the part or of
  a supertype of it, `:cover`, one nogood per choice of denials.  Read through the write
  view `w` (`decide/write-view`)."
  [tax w c x]
  (concat
   (for [[[a b] how] (get-in c [::sep x])
         h1 (get-in c [::by-type a x])
         h2 (get-in c [::by-type b x])]
     (cond-> {:members #{h1 h2} :kind :disjoint}
       (= :spared how) (assoc :spared? true)))
   (when (and (contains? (::denied c) x) (seq (tax/coverings tax)))
     (let [m     (get-in c [::mem x])
           pos   (filterv #(nth (val %) 2) m)
           neg   (filterv #(not (nth (val %) 2)) m)
           above (:genls-global w)]
       (for [[h [s]]   pos
             [_ parts] (distinct (tax/covers-over tax s nil))
             :let [per (for [p (distinct parts)
                             :let [ups (above p)]]
                         (for [[d [q]] neg :when (contains? ups q)] d))]
             :when (every? seq per)
             combo (combinations per)]
         {:members (into #{h} combo) :kind :cover})))))

(defn- place-term
  "`c` with term `x`'s nogoods read again through the unscoped taxonomy (`term-nogoods`),
  kept under `::ngs` while it has one; their members are under `::live-mem` and in step
  in `:membership`.  A term with no separated pair (`::sep`) and no denial under a stored
  cover has none, and is read no further.  A term whose nogoods moved, or every term
  holding one when `force?`, is queued under `::moved` with the members of its nogoods
  before and after, for the settle to place (`take-moved!`)."
  [w c x force?]
  (let [tax (:tax w)
        old (get-in c [::live-mem x])
        was (get-in c [::ngs x])
        ngs (when (or (seq (get-in c [::sep x]))
                      (and (contains? (::denied c) x) (seq (tax/coverings tax))))
              (not-empty (vec (term-nogoods tax w c x))))
        new (not-empty (into #{} (mapcat :members) ngs))]
    (as-> c c
      (if (and (or was ngs) (or force? (not= (set was) (set ngs))))
        (update-in c [::moved x] (fnil into #{}) (concat old new))
        c)
      (if (seq ngs) (assoc-in c [::ngs x] ngs) (update c ::ngs #(some-> % (dissoc x))))
      (if (= old new)
        c
        (-> c
            (update :membership #(into (reduce disj (or % #{}) old) new))
            (journal/note (concat old new))
            (update ::live-mem #(if new (assoc (or % {}) x new) (dissoc % x))))))))

(defn- types-under
  "The types `::by-type` holds at or below one of the types `ends` over the unscoped
  `genl` closure (`w`, `decide/write-view`).  Reads the types `::by-type` holds or the
  specializations of `ends`, whichever is fewer."
  [w c ends]
  (when (seq ends)
    (let [held (::by-type c)
          ends (set ends)]
      (if (< (count held) (* 4 (count ends)))
        (filter #(some ends ((:genls-global w) %)) (keys held))
        (distinct (filter #(contains? held %) (mapcat (:specs-global w) ends)))))))

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
  "`c` with `::sep` and the kept nogoods read again under the taxonomy as it stands.  The
  pairs holding a type at or below a type whose separations the declarations moved
  (`tax/separation-moves`), or at or below the lower end of a moved `genl` edge
  (`tax/moves-since`), are tested again (`types-under`), since no other pair's separation
  moved.  With no stamp to compare, or the `genl` relation rebuilt from nothing, every
  kept term's pairs are.  The terms tested are placed again, and so are the terms with a
  denial when the declarations or the edges moved; every one is queued when an edge
  moved.  On a full test every term holding nogoods is placed again too.  Reads no
  membership."
  [w c]
  (let [tax    (:tax w)
        st     (tax/separation-stamp tax)
        old    (::sep-stamp c)
        g      (tax/relation-gen tax :genl)
        seen   (::genl-seen c)
        test   (separation-tests tax)
        full   (or (nil? old) (nil? seen) (< g seen))
        ;; an edge moving can move a nogood's routes with its members unmoved
        edge?  (or (nil? seen) (not= g seen))
        decl?  (not= st old)
        retest (fn [c x ts] (reduce #(test-type test (untest %1 x %2) x %2) c ts))
        [c xs] (if full
                 [(reduce-kv (fn [c x m]
                               (retest c x (into #{} (keep (fn [[t _ pos]] (when pos t))) (vals m))))
                             (assoc c ::sep {}) (::mem c))
                  (keys (::mem c))]
                 (let [ends (cond-> #{}
                              decl? (into (tax/separation-moves old st))
                              edge? (into (tax/moves-since tax :genl seen)))
                       hits (for [t (types-under w c ends), x (keys (get-in c [::by-type t]))] [x t])]
                   [(reduce (fn [c [x t]] (retest c x [t])) c hits) (map first hits)]))
        xs     (cond-> (set xs)
                 (or decl? edge?) (into (::denied c))
                 full             (into (keys (::ngs c))))
        c      (assoc c ::sep-stamp st ::genl-seen g)]
    (reduce #(place-term w %1 %2 edge?) c xs)))

(defn- add-held
  "`c` with the kept term `x`'s entries `m` recorded, and no separation read:
  `rebuild-candidates!`' step, which leaves the separations to `sync-memberships`."
  [c x m]
  (reduce-kv (fn [c h e] (add-entry (constantly nil) c x h e)) c m))

(defn- recovered-terms
  "The terms recover reads the entries of: those the unary roster lists two or more
  predicates of, and the arguments of the unary bodies stored in both polarities.  Every
  term holding two memberships of distinct types, or a membership and a denial, is one."
  [kb]
  (let [idx (:index kb)]
    (into (into #{} (filter sx/plain-symbol?) (reads/as-stored-unary-multi-terms idx))
          (keep (fn [b] (when (and (= 2 (count b)) (sx/plain-symbol? (first b))
                                   (sx/plain-symbol? (second b)))
                          (second b))))
          (reads/as-stored-opposed-bodies idx))))

(defn- note-membership!
  "Keep the membership candidates in step with the fact `sx` arriving (`stored?` true) or
  leaving.  A membership or a denial of a kept term joins it with no roster read, and a
  membership's type new to the term is tested against the term's other types
  (`add-entry`).  One of a term not kept reads the term's unary roster once
  (`term-entries`), and keeps the term when it holds two memberships or a membership and
  a denial.  A term that read holds denials and no membership is noted under `::no-pos`,
  so a further denial of it reads nothing, and its first membership reads the roster once
  and keeps it.  A declaration arriving reads nothing here: `sync-memberships` reads its
  separations over `::by-type`."
  [kb w sx stored?]
  (when-let [[x t pos] (membership-of sx)]
    (let [h     (:id sx)
          e     [t (:context sx) pos]
          cands (reasoning/nogood-candidates kb)
          sync  #(if (membership-synced? (:tax w) %) % (sync-memberships w %))
          place (fn [c] (place-term w (if (held? (get-in c [::mem x])) c (drop-term c x)) x false))]
      (cond
        (contains? (::mem @cands) x)
        (swap! cands (fn [c]
                       (let [c (sync c)]
                         (place (if stored?
                                  (add-entry (separation-tests (:tax w)) c x h e)
                                  (remove-entry c x h))))))

        (and stored? (not pos) (contains? (::no-pos @cands) x))
        nil

        stored?
        (let [m (assoc (term-entries kb x) h e)]
          (cond
            (held? m)
            (swap! cands (fn [c]
                           (let [c    (-> (sync c) (update ::no-pos #(some-> % (disj x))))
                                 test (separation-tests (:tax w))]
                             (place (reduce-kv (fn [c h e]
                                                 (if (get-in c [::mem x h]) c (add-entry test c x h e)))
                                               c m)))))

            (not-any? #(nth % 2) (vals m))
            (swap! cands update ::no-pos (fnil conj #{}) x)))))))

(defn- note-placement-left!
  "Queue the term of the membership nogood a `(contradicts …)` sentex `sx` leaving the
  store placed, with its members, so the settle places the nogood where it stands
  (`take-moved!`): a `genlCx` edge under the placement can have left with it."
  [kb sx]
  (let [s (:sentence sx)]
    (when (and (seq? s) (= 'contradicts (first s)))
      (let [cands (reasoning/nogood-candidates kb)
            hs    (into #{} (keep sx/handle-id) (rest s))
            xs    (into #{} (comp (keep #(p/get-sentex (:records kb) %)) (keep membership-of)
                                  (map first))
                        hs)]
        (when (and (= 1 (count xs)) (contains? (::mem @cands) (first xs)))
          (swap! cands update-in [::moved (first xs)] (fnil into #{}) hs))))))

(defn moved?
  "Has the index queued a term whose nogoods the settle places again (`take-moved!`)?"
  [c]
  (boolean (seq (::moved c))))

(defn take-moved!
  "`{x #{h}}`, the terms whose nogoods moved since the last call, each with the members of
  its nogoods before and after the move, and the queue emptied (`place-term`)."
  [kb]
  (let [[old _] (swap-vals! (reasoning/nogood-candidates kb) dissoc ::moved)]
    (::moved old {})))

(defn terms-of
  "The terms of the memberships and denials among the handles `hs` that the candidate
  index `c` keeps."
  [kb c hs]
  (let [recs (:records kb)]
    (into #{} (comp (keep #(p/get-sentex recs %)) (keep membership-of) (map first)
                    (filter #(contains? (::mem c) %)))
          hs)))

(defn terms-under
  "The kept terms with a nogood (`::ngs`) holding a type at or below one of the types
  `ends` over the unscoped `genl` closure (`w`, `decide/write-view`), in a membership
  (`types-under`) or a denial: those whose nogoods a separation over `ends` arriving can
  give a route."
  [w c ends]
  (when (and (seq ends) (seq (::ngs c)))
    (let [ngs   (::ngs c)
          ends  (set ends)
          under (memoize (fn [t] (some ends ((:genls-global w) t))))]
      (-> #{}
          (into (comp (mapcat #(keys (get-in c [::by-type %]))) (filter #(contains? ngs %)))
                (types-under w c ends))
          (into (filter (fn [x] (and (contains? ngs x)
                                     (some #(under (first %)) (vals (get-in c [::mem x]))))))
                (::denied c))))))

(defn nogoods-terms
  "The kept terms holding a nogood under the candidate index `c`."
  [c]
  (keys (::ngs c)))

(defn nogoods-of
  "Term `x`'s nogoods under the candidate index `c`, each `{:members #{h} :kind k}`."
  [c x]
  (get-in c [::ngs x]))

(defn- member-types
  "`[x positive negative]` for the member handles `ms` of one term's nogood: the term, the
  types it is held in and the types it is denied, or nil when some member is not a stored
  membership or denial of one term."
  [recs ms]
  (let [es (map #(some-> (p/get-sentex recs %) membership-of) ms)]
    (when (and (seq es) (every? some? es) (apply = (map first es)))
      [(ffirst es)
       (into (sorted-set) (keep (fn [[_ t pos]] (when pos t))) es)
       (into (sorted-set) (keep (fn [[_ t pos]] (when-not pos t))) es)])))

(defn kind-of
  "The kind of the membership nogood over the member handles `ms`, read off their
  sentences: `:disjoint` for two memberships of one term in distinct types, `:cover` for
  one membership of a term beside denials of it, else nil."
  [recs ms]
  (when-let [[_ pos neg] (member-types recs ms)]
    (cond
      (and (empty? neg) (= 2 (count pos) (count ms))) :disjoint
      (and (= 1 (count pos)) (seq neg))               :cover)))

(defn routes
  "Each way the declarations convict the membership nogood `ng` over the unscoped
  taxonomy, as `tax/separation-routes` answers for a `:disjoint` one: `{:keys #{k} :links
  [[sub super]] :pair [x y]}`, the flat-cache keys read, the `genl` subsumptions climbed
  and the separated pair.  For a `:cover` one, a cover over a whole above the held type
  with a member denial at or above each part: the cover's key, the subsumption from the
  held type to the whole and from each part to the first such denial's type, and no
  pair.  Empty when the members are not one term's.  Read over the write view `w`
  (`decide/write-view`): a route is a superset over every reader, and the placement
  decides which contexts see it."
  [w recs {:keys [members kind]}]
  (when-let [[_ pos neg] (member-types recs members)]
    (case kind
      :disjoint
      (when (= 2 (count pos))
        (let [[a b] (seq pos)] (tax/separation-routes (:tax w) a b)))
      :cover
      (when (= 1 (count pos))
        (let [s (first pos)]
          (for [[whole parts] (distinct (tax/covers-over (:tax w) s nil))
                :let [qs (map (fn [p] (first (filter #(contains? ((:genls-global w) p) %) neg)))
                              parts)]
                :when (every? some? qs)
                [ps kind] (tax/covers-of (:tax w) whole)
                :when (= ps parts)]
            {:keys #{[:cover [whole parts] kind]}
             :links (into [] (remove (fn [[a b]] (= a b)))
                          (cons [s whole] (map vector parts qs)))})))
      nil)))

(defn exempt-at?
  "Does a reader with ancestor set `up` read no separation of the membership nogood
  `members` while the KB stores a `siblingDisjointException`: two memberships of one term
  whose types `tax/disjoint?` over `up` does not separate.  An exception the reader sees removes a
  separation its placement reads, the one read below a placement that seeing more takes
  away (docs/taxonomy.md).  False for any other nogood."
  [tax recs members up]
  (boolean
   (and (tax/sib-exceptions? tax)
        (= 2 (count members))
        (when-let [[_ pos neg] (member-types recs members)]
          (and (empty? neg) (= 2 (count pos))
               (let [[a b] (seq pos)]
                 (not (or (tax/disjoint? tax a b up) (tax/disjoint? tax b a up)))))))))

(def family
  "The membership family's entry in `decide/registry`.  Recover keeps the entries of the
  terms `recovered-terms` names that `held?` holds, with no separation read: the first
  read after it tests every pair once (`sync-memberships`)."
  {:grounds   {:forced-monotonic '#{disjoint covering partition sibling_disjoint siblingDisjointException}}
   :note!     (fn [kb w sx stored?]
                (note-membership! kb w sx stored?)
                (when-not stored? (note-placement-left! kb sx)))
   :recovered (fn [kb _]
                (let [held (into {} (comp (map (fn [x] [x (term-entries kb x)]))
                                          (filter #(held? (second %))))
                                 (sort (recovered-terms kb)))]
                  (when (seq held)
                    (swap! (reasoning/nogood-candidates kb)
                           #(dissoc (reduce-kv add-held % held) ::sep-stamp ::genl-seen)))))
   :synced?   (fn [tax c] (or (empty? (::mem c)) (membership-synced? tax c)))
   :sync      (fn [_ w c] (sync-memberships w c))
   :handles   :membership
   :holds?    (fn [c h] (contains? (:membership c) h))})

;; ---- derived state (docs/caches.md, "The derived-state register") ----------------

(caches/register-derived
 {:id :N5 :label "Membership candidates" :kind :cache :keyed-by :term
  :reads [:index :records :T1 :T2 :J5]
  :retired-by {:stored :K :removed :K :respelled :K :edge :K :declared :S :edge-belief :K
               :settle-pass :K :recover :R :image-install :R}
  :computed :read :imaged? :state
  :at [[:nogood-candidates :membership] [:nogood-candidates ::mem]
       [:nogood-candidates ::sep] [:nogood-candidates ::sep-stamp]
       [:nogood-candidates ::live-mem] [:nogood-candidates ::denied]
       [:nogood-candidates ::ngs] [:nogood-candidates ::by-type]
       [:nogood-candidates ::genl-seen] [:nogood-candidates ::no-pos]
       [:nogood-candidates ::moved]]
  :bound "the stored memberships and denials of each term holding two memberships, or a membership and a denial"
  :note "the unary members, the kept terms by type and each term's separated type pairs, read off a term's unary roster at its first write and at recover; synced at a read by `tax/separation-stamp` and the relation moves (J5)"})

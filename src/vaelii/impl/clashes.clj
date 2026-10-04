;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.clashes
  "The clashes a reader reads: the hard clashes and dilemmas of every nogood family as
  reports, each with the declarations it convicts through, the re-read of a definitional
  nogood under a reader's withdrawal (`res/*reread*`), and the disjointness clashes no
  single writer could see.  Nothing here writes belief.  See docs/nmtms.md, \"A clash is
  reported, never stored\"."
  (:require [clojure.set :as set]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.decide :as decide]
            [vaelii.impl.decide.arity :as arity]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.strength :as strength]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]))

;; ---- the definitional re-read ----------------------------------------------

(defn- reads-clash?
  "Does a member of `nogood` form a definitional violation whose opposing handles are the
  other members?  `opposing` is `(fn [h])` → the opposing-handle sets of the violations
  member `h`'s sentence forms at the vantage (`checks/arbitrable-violations`)."
  [opposing nogood]
  (boolean
   (some (fn [h]
           (let [others (disj nogood h)]
             (some #(every? % others) (opposing h))))
         nogood)))

(defn- reread-each
  "The member sets of the definitional nogoods `ngs` that `reader` still convicts when it
  withdraws `provisional`.  Each is re-asked through `reads-clash?` against a detached
  copy of the taxonomy (`tax/detached-copy`), with `res/*provisional*` answering
  `provisional` for `reader`, so the closures the re-read walks are memoized in the copy
  and never in the live taxonomy, whose memo is stamped on what readers read
  (docs/nmtms.md, \"A defeat is scoped to its vantage\").  A member's violations are
  asked once per call, so the nogoods of a term holding `p` separated types read `p`
  violation sets, not one per nogood.  `reread-at` is this under the pass caches."
  [kb reader provisional ngs]
  (let [recs  (:records kb)
        probe (assoc kb :reasoning
                     (atom (assoc (reasoning/of kb)
                                  :taxonomy (tax/detached-copy (reasoning/taxonomy kb)))))
        w     (let [{:keys [region in]} provisional
                    out (into #{} (remove in) region)]
                {:region region :in in :out out})
        opposing (memoize
                  (fn [h]
                    (when-let [s (p/get-sentex recs h)]
                      (mapv #(set (checks/opposing-handles %))
                            (checks/arbitrable-violations probe (:sentence s) reader)))))]
    (binding [res/*provisional* (assoc res/*provisional* reader w)]
      (into #{} (comp (filter #(reads-clash? opposing (:members %)))
                      (map :members))
            ngs))))

(defn- reread-at
  "`res/*reread*`: `reread-each` holding the pass caches (`tax/*closure-pass-cache*`).
  A re-read is a read-only pass over a still taxonomy with one reading bound, and every
  definitional nogood of a round is re-asked in it, so the `genl?` answers, the filtered
  edges and the separation frames one nogood reads serve the rest, which share their
  types, their contexts and the edges above them."
  [kb reader provisional ngs]
  (binding [tax/*closure-pass-cache*      (atom {})
            tax/*visible-neighbours-cache* (atom {})
            tax/*separation-frame-cache*  (atom {})]
    (reread-each kb reader provisional ngs)))

(alter-var-root #'res/*reread* (constantly reread-at))

;; ---- the reports -----------------------------------------------------------

(defn- clash-report
  "A clash as a report map, the shape docs/nmtms.md (\"A clash is reported,
  never stored\") shows: the members as `:sides` in content order, each with its
  justifications.  `:kind` is the definitional violation's `:type`, `:inherited`, or nil
  for a rebuttal.  `:inherited` and `:vantages` appear only on the reports that carry
  them; the weighing contexts ride the metadata (`report-vantages`)."
  [kb {:keys [nogood priority sentence kind inherited vantages] ::keys [vantage-verdicts]}]
  (let [tms   (reasoning/tms kb)
        recs  (:records kb)
        ;; a side's justifications in `core/supporting-justifications`' content order
        jkey  (kb/justification-content-key kb)
        ;; Sides by sentence then context, which identify a sentex, so no handle enters
        ;; the key; `report_order_test` scans the `sort-by` line below for one.
        sides (->> nogood
                   (map (fn [h]
                          (let [s (p/get-sentex recs h)]
                            {:handle h :sentence (sx/sentence-of s) :context (:context s)
                             :defeat-class (jtms/defeat-class tms h)
                             :justifications (->> (jtms/supports tms h)
                                                  (keep #(p/get-justification recs %))
                                                  ;; keyed once per justification
                                                  (nm/sort-by-content-key jkey nm/compare-form))})))
                   (sort-by (juxt :sentence :context) nm/compare-form)
                   vec)]
    (-> (cond-> {:nogood nogood :priority priority :sentence sentence
                 :handles (mapv :handle sides)
                 :kind kind
                 :sides sides}
          inherited (assoc :inherited inherited)
          ;; `{vantage handle}`, on a vantage disagreement only
          vantage-verdicts (assoc :vantages vantage-verdicts))
        ;; metadata stays off the wire and out of `=`
        (vary-meta assoc ::vantages vantages))))

(defn report-vantages
  "The contexts that weighed report `r`'s clash, or nil for one the network weighed
  alone.  `core/contradictions`' reader arity keeps a report for a reader at or below
  one of them."
  [r]
  (::vantages (meta r)))

(defn- marks-over-all
  "The predicates carrying prop mark `kind` over every functor of `tuples` at `v`."
  [tax kind tuples v]
  (reduce set/intersection (map #(set (tax/props-over tax kind (nm/functor %) v)) tuples)))

(defn- chain?
  "Do the binary `tuples` fill the three roles of an `anti_transitive` chain, `(a b)`, `(b c)`
  and `(a c)`, with no tuple left over?"
  [tuples]
  (let [ts (set tuples)]
    (boolean (some (fn [[t1 t2 t3]]
                     (let [[a b] (nm/args t1) [b' c] (nm/args t2) [a' c'] (nm/args t3)]
                       (and (= b b') (= a a') (= c c') (= ts (hash-set t1 t2 t3)))))
                   (for [x ts y ts z ts] [x y z])))))

(defn- ground-keys
  "The flat-cache keys a definitional conviction of the member sentences `sens` reads at
  vantage `v`, found from the members' shape: the separations of two memberships of one
  term; the `functional` and `functionalInArg` marks over two tuples differing at one
  position; the `asymmetric` and `anti_symmetric` marks over a converse pair, the
  `irreflexive` mark over a self tuple and the `anti_transitive` mark over a chain; the
  covers whose every part a denial in `sens` rules out for the whole's member; and the
  separations of the two types a lone `(orthogonal a b)` names.  A `genl` edge is no
  flat-cache entry, so an `orthogonal` convicted through one alone reads nothing, as a
  `disjoint` over related types does.  A shape no conviction has reads nothing."
  [tax sens v]
  (let [pos    (filterv #(not (sx/negation? %)) sens)
        denied (mapv second (filter sx/negation? sens))
        args   #(vec (nm/args %))
        binary (and (empty? denied) (every? #(= 2 (nm/arity %)) pos))
        marks  (fn [kinds] (for [k kinds, q (marks-over-all tax k pos v)] [:prop k q]))]
    (into #{}
          cat
          [(when (and (empty? denied) (= 2 (count pos)) (apply = (map nm/arity pos)))
             (let [[s t] pos
                   diff  (keep-indexed (fn [i [x y]] (when (not= x y) (inc i)))
                                       (map vector (args s) (args t)))
                   n     (first diff)]
               (cond
                 (and (= 1 (nm/arity s)) (= (args s) (args t)) (not= (nm/functor s) (nm/functor t)))
                 (tax/separating-keys tax (nm/functor s) (nm/functor t) v)

                 (= 1 (count diff))
                 (concat (when (= 2 n (nm/arity s)) (marks [:functional]))
                         (for [[q m :as qm] (tax/functional-in-arg-over tax (nm/functor s) v)
                               :when (and (= m n)
                                          (contains? (set (tax/functional-in-arg-over
                                                           tax (nm/functor t) v))
                                                     qm))]
                           [:functional-in-arg q n])))))
           (when (and binary (= 2 (count pos)))
             (let [[[a b] [c d]] (map args pos)]
               (when (and (not= a b) (= a d) (= b c))
                 (marks [:asymmetric :anti-symmetric]))))
           (when (and binary (= 1 (count pos)) (apply = (args (first pos))))
             (marks [:irreflexive]))
           (when (and (empty? denied) (= 1 (count pos)) (= 'orthogonal (nm/functor (first pos)))
                      (= 2 (nm/arity (first pos))))
             (let [[a b] (args (first pos))]
               (tax/separating-keys tax a b v)))
           (when (and binary (<= 2 (count pos) 3) (chain? pos))
             (marks [:anti-transitive]))
           (when (and (= 1 (count pos)) (seq denied) (= 1 (nm/arity (first pos)))
                      (every? #(and (= 1 (nm/arity %))
                                    (= (args (first pos)) (args %)))
                              denied))
             (let [w (nm/functor (first pos))
                   ds (map nm/functor denied)]
               (for [[whole parts] (tax/covers-over tax w v)
                     :when (every? (fn [p] (some #(contains? (tax/genls tax p v) %) ds)) parts)
                     [ps kind] (tax/covers-of tax whole)
                     :when (= ps parts)]
                 [:cover [whole parts] kind])))])))

(defn clash-grounds
  "The declarations report `r` convicts through, as `{:handle :sentence :context}` maps in
  content order: the believed supporters of the flat-cache entries its conviction reads
  (`ground-keys`) that one of its vantages sees, or the whole KB for a report weighed at
  none; for an `:arity` clash, the bindings each vantage convicts the tuple through
  (`arity/arity-grounds`), over the unscoped ancestor set the reader decides over
  (`read-clashes`).  No `genl` edge is named.  Empty for a rebuttal, an
  `:inherited` clash and an `:arity-descension` clash, whose reasons are members
  (docs/nmtms.md, \"A clash is reported, never stored\")."
  [kb r]
  (if (contains? #{nil :inherited :arity-descension} (:kind r))
    []
    (let [tax  (reasoning/taxonomy kb)
          tms  (reasoning/tms kb)
          recs (:records kb)
          sens (mapv :sentence (:sides r))
          at   (fn [v]
                 (if (= :arity (:kind r))
                   (let [v (if (symbol? v) v (:context (first (:sides r))))]
                     (arity/arity-grounds kb (first sens) (tax/context-up-global tax v)
                                          (res/except-hidden-fn kb v)))
                   (mapcat #(tax/visible-supporters tax % v) (ground-keys tax sens v))))]
      (->> (or (seq (report-vantages r)) [nil])
           (into #{} (mapcat at))
           (into [] (comp (filter #(jtms/in? tms %))
                          (keep #(p/get-sentex recs %))
                          (map (fn [s] {:handle (:id s) :sentence (sx/sentence-of s)
                                        :context (:context s)}))))
           (sort-by (juxt :sentence :context) nm/compare-form)
           vec))))

(defn with-grounds
  "`reports` with each one's `clash-grounds` under `:grounds`, read now: a declaration
  can move under a report whose members did not, so the grounds ride no memo."
  [kb reports]
  (mapv #(assoc % :grounds (clash-grounds kb %)) reports))

(defn- report-order
  "One clash report's sort key: each side's sentence then its context, in side order.
  Compared by `nm/compare-form`; no handle enters it."
  [r]
  (mapv (juxt :sentence :context) (:sides r)))

(defn ranked
  "`reports` in content order (`report-order`).  Every reader of `conflicts-of` or
  `contradictions-of` owes this call, since those hold the order the candidate index
  answered in."
  [reports]
  (nm/sort-by-content-key report-order nm/compare-form reports))

(defn- read-clashes*
  "`read-clashes`' answer, computed.  Every context below a candidate's own context is
  asked for the nogoods it reads (`decide/nogoods-at`) and decides each as its own
  withdrawal decided it (`res/verdicts`), which reads a definitional nogood again through
  a ground that context withdraws.  A nogood is reported at the most general contexts
  that read it hard, or read it as a dilemma.  A nogood whose deciding contexts take
  different members OUT is a dilemma too, carrying `{vantage handle}`, and that report
  stands for the dilemma a reader below the disagreeing contexts reads.  An inherited
  clash carries its discovery's `:sentence` and `:inherited` map.  A report whose
  members' classes and supports and whose vantages are the last reading's is that
  reading's, kept in `:read-reports`.  The ancestor set is `tax/context-up-global`, the
  one `res/withdrawal` decides over, so a report names what the reader's belief reads."
  [kb]
  (let [tax   (reasoning/taxonomy kb)
        recs  (:records kb)
        tms   (reasoning/tms kb)
        ctxs  (into #{}
                    (comp (keep #(:context (p/get-sentex recs %)))
                          (mapcat #(tax/context-down tax %)))
                    (decide/candidate-handles kb))
        ;; the discovery's map of each inherited clash a context decides
        found-by (volatile! {})
        found (reduce
               (fn [acc v]
                 (let [vds (delay (res/verdicts kb v))]
                   (reduce (fn [acc {:keys [members kind report]}]
                             (if-let [d (get @vds members)]
                               (do (when report (vswap! found-by assoc [kind members] report))
                                   (if (keyword? d)
                                     (update-in acc [[kind members] d] (fnil conj #{}) v)
                                     (update-in acc [[kind members] :defeat (:defeat d)]
                                                (fnil conj #{}) v)))
                               acc))
                           acc
                           (decide/nogoods-at kb (tax/context-up-global tax v)
                                              (res/except-hidden-fn kb v)))))
               {} (sort ctxs))
        general (fn [vs] (into #{} (remove (fn [v] (some #(and (not= v %) (tax/sees? tax v %)) vs)))
                               vs))
        ;; the last reading's reports, reused where the members' classes and supports
        ;; and the report's vantages are the ones it was built from
        memo    @(reasoning/read-reports kb)
        built   (volatile! {})
        report (fn [[kind members :as km] vs split]
                 (let [vantages (if split (set (keys split)) (general vs))
                       k        [kind members vantages split
                                 (into {} (map (fn [h] [h [(jtms/defeat-class tms h)
                                                           (jtms/supports tms h)]]))
                                       members)]
                       r        (or (get memo k)
                                    (let [rebuttal? (contains? #{:negation :inherited} kind)
                                          sens (sort nm/compare-form
                                                     (map #(:sentence (p/get-sentex recs %)) members))
                                          rank (reduce max (map #(strength/rank-of
                                                                  (jtms/defeat-class tms %))
                                                                members))
                                          inh  (get @found-by km)]
                                      ;; a negation pair reports as a rebuttal with no
                                      ;; `:kind` and the body first; an inherited clash in
                                      ;; the rebuttal range, as its discovery stated it
                                      (clash-report kb (cond-> {:nogood   members
                                                                :kind     (when-not (= :negation kind) kind)
                                                                :vantages vantages
                                                                :priority (if rebuttal? rank (+ 2 rank))
                                                                :sentence (cond
                                                                            inh (:sentence inh)
                                                                            (= :negation kind)
                                                                            (let [b (first (remove sx/negation? sens))]
                                                                              (list 'contradicts b (list 'not b)))
                                                                            :else (apply list 'contradicts sens))}
                                                         inh   (assoc :inherited (:inherited inh))
                                                         split (assoc ::vantage-verdicts split)))))]
                   (vswap! built assoc k r)
                   r))
        ;; a nogood whose readers disagree is reported once, carrying each verdict: the
        ;; dilemma a reader below the disagreeing ones reads is that report's
        split-of (into {} (keep (fn [[k m]]
                                  (when (< 1 (count (:defeat m)))
                                    [k (into {} (for [[h vs] (:defeat m), v (general vs)] [v h]))])))
                       found)
        answer {:conflicts      (into [] (keep (fn [[k m]] (when-let [vs (:hard m)] (report k vs nil))))
                                      found)
                :contradictions (-> []
                                    (into (keep (fn [[k m]]
                                                  (when-let [vs (:dilemma m)]
                                                    (when-not (contains? split-of k) (report k vs nil)))))
                                          found)
                                    (into (map (fn [[k split]] (report k nil split))) split-of))}]
    (reset! (reasoning/read-reports kb) @built)
    answer))

(defn read-clashes
  "The hard clashes and the dilemmas of every nogood family, as `{:conflicts [report]
  :contradictions [report]}` in `clash-report`'s shape, each report's vantages the most
  general contexts that decided it so.  Empty unless `decide/live?`.  Cached in
  `:withdrawn` with no watch, so every settle point drops it (`res/reconcile-withdrawn!`)."
  [kb]
  (if-not (decide/live? kb)
    {:conflicts [] :contradictions []}
    ;; a reader of a settle's held belief neither reads nor fills the cache; the readers
    ;; of every context share each family's pass cache
    (decide/with-pass false
      (jtms/through-cache
       (reasoning/tms kb) #(read-clashes* kb)
       #(let [cache (reasoning/withdrawn kb)
              m     @cache
              hit   (get m ::read-clashes ::absent)]
          (if (identical? ::absent hit)
            (let [rs (read-clashes* kb)]
              (res/install-withdrawn! cache (::res/gen m) ::read-clashes rs)
              rs)
            hit))))))

(defn conflicts-of
  "The conflict reports (`read-clashes`), unordered: `ranked` orders them."
  [kb] (:conflicts (read-clashes kb)))

(defn contradictions-of
  "The dilemma reports (`read-clashes`), unordered: `ranked` orders them."
  [kb] (:contradictions (read-clashes kb)))

;; ---- the clash no single writer could see ---------------------------------
;;
;; `exposed-clashes`' per-term clash reader and the believed-content reads it takes
;; (docs/contexts.md).

(defn- believed-xf
  "A transducer from handles to the believed, positive sentexes among them.  Belief is
  `jtms/in?`, so a superseded spelling drops out with a defeated one."
  [kb]
  (comp (filter #(jtms/in? (reasoning/tms kb) %))
        (keep #(p/get-sentex (:records kb) %))
        (filter #(not (sx/negative? %)))))

(defn- believed-at-arg1
  "The believed, positive sentexes posted on `term`'s argument-1 root, or nil for a
  non-symbol `term`."
  [kb term]
  (when (symbol? term)
    (into [] (believed-xf kb) (reads/as-stored-with-arg (:index kb) 1 term))))

(defn believed-memberships
  "The believed positive unary memberships of `x`, as `[type context handle]` triples,
  in content order."
  [kb x]
  ;; `compare` on the symbols: a keyfn runs per comparison and would allocate each time.
  ;; Symbols order by namespace then name.
  (sort (fn [[t1 c1] [t2 c2]]
          (let [r (compare t1 t2)] (if (zero? r) (compare c1 c2) r)))
        (into []
              (keep (fn [s]
                      (let [sen (:sentence s)]
                        (when (and (sequential? sen) (= 2 (count sen))
                                   (symbol? (first sen))
                                   (= x (second sen)))
                          [(first sen) (:context s) (:id s)]))))
              (believed-at-arg1 kb x))))

(defn- exposure-probes
  "`{:disjoint? (fn [t1 t2]) :visible-from (fn [t1 c1 t2 c2])}` over the taxonomy `tax`,
  each memoized for one pass.  `:disjoint?` reads no `siblingDisjointException`, since a
  reader that does not see one reads the pair separated.  `:visible-from` is the maximal
  common descendant contexts of the first disjointness witness that shares one with `c1`
  and `c2`, kept where the scoped `disjoint?` holds, or nil; it enumerates witnesses only
  after the scoped `disjoint?` at some common descendant of `c1` and `c2` says one exists
  (docs/contexts.md)."
  [tax]
  (let [dj  (volatile! {})
        vis (volatile! {})
        memo (fn [v k f]
               (if-let [e (find @v k)]
                 (val e)
                 (let [r (f)] (vswap! v assoc k r) r)))]
    {:disjoint?
     (fn [t1 t2] (memo dj [t1 t2] #((tax/disjointness-test tax t1 nil (constantly false)) t2)))
     :visible-from
     (fn [t1 c1 t2 c2]
       (memo vis [t1 c1 t2 c2]
             #(when (some (fn [k] (tax/disjoint? tax t1 t2 k))
                          (tax/common-descendants tax [c1 c2]))
                (some (fn [w]
                        (let [m (into #{} (filter (fn [k] (tax/disjoint? tax t1 t2 k)))
                                      (tax/maximal-common-descendant-contexts
                                       tax (into [c1 c2] w)))]
                          (when (seq m) m)))
                      (distinct (tax/disjointness-witnesses tax t1 t2))))))}))

(defn- exposed-clashes-for-term
  "The `:disjoint` entries for the jointly-visible clashes among `x`'s believed
  memberships.  `probes` is `exposure-probes`' answer."
  [kb x {:keys [disjoint? visible-from]}]
  (let [ms (believed-memberships kb x)]
    (for [i (range (count ms))
          j (range (inc i) (count ms))
          :let  [[t1 c1] (nth ms i)
                 [t2 c2] (nth ms j)]
          :when (and (not= t1 t2) (disjoint? t1 t2))
          :let  [mx (visible-from t1 c1 t2 c2)]
          :when mx]
      {:violation :disjoint
       :detail    {:term         x
                   :held         [[t1 c1] [t2 c2]]
                   :visible-from mx
                   :message      (str "disjointness clash exposed: " x " holds " t1
                                      " (in " c1 ") and " t2 " (in " c2
                                      "), jointly visible from "
                                      (pr-str (vec (sort nm/compare-form mx))))}})))

(defn separations?
  "Does the KB separate any two types, by a `disjoint` pair, a disjoint metatype, a
  `sibling_disjoint` parent or a `partition`/`separating` cover?  Four set-emptiness reads
  and no walk.  The covers are read because `separation-frame` reads them
  (docs/taxonomy.md)."
  [tax]
  (boolean (or (seq (tax/disjoint-pairs tax))
               (seq (tax/disjoint-metatypes tax))
               (seq (tax/sibling-disjoints tax))
               (seq (tax/separating-covers tax)))))

(defn exposed-clashes
  "`core/exposed-clashes`' body: every jointly-visible disjointness clash the KB holds,
  in `violations`' entry shape, filed nowhere.  A term is a candidate iff it holds two
  believed memberships, so the walk over every stored sentex finds each candidate and
  takes no instance budget.  The `separations?` gate answers `[]` with no record fetched
  for a KB that separates nothing."
  [kb]
  (let [tax (reasoning/taxonomy kb)]
    (if-not (separations? tax)
      []                                             ; nothing separates anything
      (let [probes (exposure-probes tax)
            terms  (into #{}
                         (comp (believed-xf kb)
                               (keep (fn [s]
                                       (let [sen (:sentence s)]
                                         (when (and (sequential? sen) (= 2 (count sen))
                                                    (symbol? (first sen))
                                                    (symbol? (second sen)))
                                           (second sen))))))
                         (p/sentex-ids (:records kb)))]
        (into [] (comp (mapcat #(exposed-clashes-for-term kb % probes))
                       (distinct))
              ;; terms are symbols — a bare sort is the same content order
              (sort terms))))))

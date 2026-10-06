;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.integrity
  "Bounded, read-only KB integrity reporting: the passes `kb-integrity` runs under a work
  meter (`vaelii.impl.budget`).  `vaelii.core` requires this namespace; it requires
  `predall` and `provers`, which also sit below `vaelii.core`.  See docs/integrity.md."
  (:require [clojure.string :as str]
            [vaelii.impl.budget :as budget]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.predall :as predall]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.impl.violations :as violations]))

(def integrity-opt-keys
  "The options `kb-integrity` reads: three cooperative bounds and the categories to run."
  #{:max-work :max-ms :max-results :categories})

(defn- specified-findings
  "Audit one declared predicate at a time, stopping after the first finding beyond
  `remaining` proves that the result bound truncated the sweep."
  [kb context remaining]
  (loop [audits (predall/specified-declaration-audits kb context)
         findings {}]
    (if-let [[declaration result] (first audits)]
      (if (or (= :gap (:status result)) (seq (:violations result)))
        (if (and remaining (>= (count findings) remaining))
          {:status :truncated :reason :max-results :findings findings}
          (do
            (budget/record! :all-specified-violations [declaration result])
            (recur (rest audits) (assoc findings declaration result))))
        (recur (rest audits) findings))
      {:status :complete :findings findings})))

;; ---- genl-arg-widening: a predicate genl edge that widens an argument type ----

(defn- own-arg-types
  "`{position #{type …}}` from the `arg` declarations `context` sees written on `pred`
  itself — the domain its author declared, before any super-predicate's declaration is
  read into it."
  [kb pred context]
  (reduce (fn [m [_ b]]
            (budget/spend!)
            (let [n (get b '?n) t (get b '?t)]
              (if (and (integer? n) (symbol? t) (not (sx/variable? t)))
                (update m n (fnil conj #{}) t)
                m)))
          {}
          (res/matches-visible kb (list 'arg pred '?n '?t) context)))

(defn- constraining-arg-types
  "`[position type declaring-predicate]` for every `arg` declaration binding `pred`'s
  tuples from `context`: `pred`'s own and every visible super-predicate's, read through
  `res/constraining-predicates`, the closure `assert`'s argument check reads."
  [kb pred context]
  (for [p     (res/constraining-predicates kb 'arg pred context)
        [_ b] (res/matches-visible kb (list 'arg p '?n '?t) context)
        :let  [n (get b '?n) t (get b '?t)]
        :when (and (integer? n) (symbol? t) (not (sx/variable? t)))]
    [n t p]))

(defn- declared-predicates
  "The predicates carrying a visible `arg` declaration of their own, in print order: the
  one open read of this pass, a census of declarations rather than of any extent."
  [kb context]
  (->> (res/matches-visible kb '(arg ?p ?n ?t) context)
       (keep (fn [[_ b]]
               (budget/spend!)
               (let [p (get b '?p)]
                 (when (and (symbol? p) (not (sx/variable? p))) p))))
       distinct
       (sort-by nm/print-key)))

(defn- edge-widenings
  "The findings for one visible edge `(genl spec super)`: each position where a type
  `spec` declares is subsumed by none of the types `super`'s constraint demands there.
  A `spec` position carrying several declared types is their intersection, so it is
  compatible with a demanded type as soon as one of them is subsumed by it."
  [kb tx spec own super context]
  (for [[n tq declared-on] (sort-by (fn [[n t p]] [n (nm/print-key t) (nm/print-key p)])
                                    (distinct (constraining-arg-types kb super context)))
        :let  [tps (get own n)]
        :when (seq tps)
        :when (do (budget/spend!)
                  (not-any? #(or (= % tq) (tax/genl? tx % tq context)) tps))
        tp    (sort-by nm/print-key tps)]
    (cond-> {:spec spec :genl super :arg n :spec-type tp :genl-type tq}
      (not= declared-on super) (assoc :genl-type-declared-on declared-on))))

(defn- widening-findings
  "Audit every visible predicate `genl` edge out of a predicate that declares its own
  argument types, one edge at a time, stopping after the first finding beyond
  `remaining` proves that the result bound truncated the sweep."
  [kb context remaining]
  (let [tx (reasoning/taxonomy kb)]
    (loop [findings []
           units    (for [spec  (declared-predicates kb context)
                          :let  [own (own-arg-types kb spec context)]
                          super (sort-by nm/print-key (tax/direct-genls tx spec context))
                          :when (not= super spec)
                          finding (do (budget/spend!)
                                      (edge-widenings kb tx spec own super context))]
                      finding)]
      (if-let [finding (first units)]
        (if (and remaining (>= (count findings) remaining))
          {:status :truncated :reason :max-results :findings findings}
          (do
            (budget/record! :genl-arg-widening finding)
            (recur (conj findings finding) (rest units))))
        {:status :complete :findings findings}))))

;; ---- not-under-thing: a candidate type with no genl path to thing ----

(defn- unrooted-type?
  "Is `term` a type `context` sees declared `unary_predicate` that reaches `thing` by no
  `genl` path visible from `context`?  `thing` itself is the root, never unrooted."
  [kb tx term context]
  (and (not= 'thing term)
       (do (budget/spend!)
           (seq (res/matches-visible kb (list 'unary_predicate term) context)))
       (do (budget/spend!)
           (not (tax/genl? tx term 'thing context)))))

(defn- not-under-thing-findings
  "Audit each ground symbol of `candidate-terms` in print order, one term at a time,
  stopping after the first finding beyond `remaining` proves that the result bound
  truncated the sweep."
  [kb candidate-terms context remaining]
  (let [tx (reasoning/taxonomy kb)]
    (loop [findings []
           units    (for [term (->> candidate-terms
                                    (filter #(and (symbol? %) (not (sx/variable? %))))
                                    (sort-by nm/print-key))
                          :when (unrooted-type? kb tx term context)]
                      {:term term})]
      (if-let [finding (first units)]
        (if (and remaining (>= (count findings) remaining))
          {:status :truncated :reason :max-results :findings findings}
          (do
            (budget/record! :not-under-thing finding)
            (recur (conj findings finding) (rest units))))
        {:status :complete :findings findings}))))

;; ---- implicit-genl: a genl edge a cover forces but the closure does not hold ----

(defn- stated-grounds
  "The believed sentences stating the flat-cache entries `ks` that `context` sees, in
  content order: what a reader is shown as the declarations a finding rests on."
  [kb tx ks context]
  (let [tms  (reasoning/tms kb)
        recs (:records kb)]
    (->> ks
         (into #{} (mapcat #(tax/visible-supporters tx % context)))
         (into #{} (comp (filter #(jtms/in? tms %))
                         (keep #(p/get-sentex recs %))
                         (map sx/sentence-of)))
         (sort nm/compare-form)
         vec)))

(defn- visible-covers
  "The covering declarations `context` sees over `term`'s visible supertypes and over
  `thing`, as distinct `[whole parts]`: `thing` is read beside the closure because every
  type is a specialization of it, so a type the closure has not yet placed under `thing`
  is still covered by what covers `thing`."
  [tx term context]
  (->> (concat (tax/covers-over tx term context) (tax/covers-over tx 'thing context))
       distinct
       (sort-by (fn [[whole parts]] [(nm/print-key whole) (mapv nm/print-key parts)]))))

(defn- cover-sentences
  "The believed sentences declaring the cover `[whole parts]` that `context` sees."
  [kb tx whole parts context]
  (stated-grounds kb tx
                  (for [[ps kind] (tax/covers-of tx whole) :when (= ps parts)]
                    [:cover [whole parts] kind])
                  context))

(defn- suggestible-type?
  "Is `term` a type as `context` reads it: declared with arity one (`unary_predicate`, or
  any other spelling `kb/relation-arity` reads), or, with no arity visible, the subtype
  of some visible `genl` edge.  An individual, and a relation of two or more places
  whose `genl` edges are predicate specializations, are never suggested a type edge."
  [kb tx term context]
  (let [n (do (budget/spend!) (kb/relation-arity kb term context))]
    (or (= 1 n)
        (and (nil? n)
             (do (budget/spend!)
                 (seq (tax/direct-genls tx term context)))))))

(defn- cover-suggestion
  "The suggestion one visible cover `[whole parts]` forces on `term`, or nil: when the
  disjointness test separates `term` from every part but one, every instance of `term`
  is an instance of the remaining part, so `(genl term part)` holds; it is a finding
  only when the `genl` closure does not already hold it.  A term separated from every
  part is empty and forced under none; one left two parts or more is forced under none."
  [kb tx term [whole parts] context]
  (when-not (or (= term whole) (some #{term} parts))
    (let [excluded (filterv (fn [part]
                              (budget/spend!)
                              (tax/disjoint? tx term part context))
                            parts)
          left     (remove (set excluded) parts)]
      (when (= 1 (count left))
        (let [part (first left)]
          (budget/spend!)
          (when-not (tax/genl? tx term part context)
            {:term term
             :genl part
             :cover (cover-sentences kb tx whole parts context)
             :disjoint-from (mapv (fn [x]
                                    {:part x
                                     :grounds (stated-grounds
                                               kb tx (tax/separating-keys tx term x context)
                                               context)})
                                  (sort-by nm/print-key excluded))}))))))

(defn- implicit-genl-findings
  "Audit each ground candidate that `suggestible-type?` accepts as a type in `context`,
  in print order, against each visible cover over it, one cover at a time, stopping after
  the first finding beyond `remaining` proves that the result bound truncated the sweep."
  [kb candidate-terms context remaining]
  (let [tx (reasoning/taxonomy kb)]
    (loop [findings []
           units    (for [term (->> candidate-terms
                                    (filter #(and (symbol? %) (not (sx/variable? %))))
                                    (sort-by nm/print-key))
                          :when (suggestible-type? kb tx term context)
                          cover (visible-covers tx term context)
                          :let  [finding (do (budget/spend!)
                                             (cover-suggestion kb tx term cover context))]
                          :when finding]
                      finding)]
      (if-let [finding (first units)]
        (if (and remaining (>= (count findings) remaining))
          {:status :truncated :reason :max-results :findings findings}
          (do
            (budget/record! :implicit-genl finding)
            (recur (conj findings finding) (rest units))))
        {:status :complete :findings findings}))))

;; ---- orthogonal-over-separation: an orthogonal that lifts a stated separation ----

(defn- stated-records
  "The believed sentexes stating the flat-cache entries `ks` that `context` sees, as
  `{:handle :sentence :context}` maps in content order — the shape `conflicts` names a
  clash's grounds in, so a reader can drop one by its handle."
  [kb tx ks context]
  (let [tms  (reasoning/tms kb)
        recs (:records kb)]
    (->> ks
         (into #{} (mapcat #(tax/visible-supporters tx % context)))
         (into [] (comp (filter #(jtms/in? tms %))
                        (keep #(p/get-sentex recs %))
                        (map (fn [s] {:handle (:id s) :sentence (sx/sentence-of s)
                                      :context (:context s)}))))
         (sort-by (juxt :sentence :context) nm/compare-form)
         vec)))

(defn- visible-orthogonals
  "Every believed `(orthogonal a b)` over two ground symbols that `context` sees, as
  `[a b record]` in content order: the one open read of this pass, a census of
  declarations, which are few, rather than of any extent."
  [kb context]
  (let [tms  (reasoning/tms kb)
        recs (:records kb)]
    (->> (res/matches-visible kb '(orthogonal ?a ?b) context)
         (keep (fn [[h b]]
                 (budget/spend!)
                 (let [a (get b '?a) c (get b '?b)]
                   (when (and (symbol? a) (not (sx/variable? a))
                              (symbol? c) (not (sx/variable? c))
                              (jtms/in? tms h))
                     (when-let [s (p/get-sentex recs h)]
                       [a c {:handle h :sentence (sx/sentence-of s) :context (:context s)}])))))
         (into [] (distinct))
         (sort-by (fn [[_ _ r]] [(:sentence r) (:context r)]) nm/compare-form))))

(defn- orthogonal-separation
  "The finding for one visible `(orthogonal a b)`, or nil: the stated separations
  `context` sees over the pair with no `orthogonal` exempting any of them — an explicit
  `disjoint`, a `partition` or `separating` roster, a `sibling_disjoint` parent or a
  `disjoint_metatype` — over `a` and `b` or over a supertype of each.  The `orthogonal`
  lifts exactly these, so `disjoint?` reads the pair apart and cannot show them."
  [kb tx [a b orthogonal] context]
  (budget/spend!)
  (let [ks (tax/separating-keys tx a b context (constantly false))]
    (when (seq ks)
      (let [separated-by (stated-records kb tx ks context)]
        (when (seq separated-by)
          {:orthogonal orthogonal :separated-by separated-by})))))

(defn- orthogonal-over-separation-findings
  "Audit every visible `orthogonal` declaration, one at a time, stopping after the first
  finding beyond `remaining` proves that the result bound truncated the sweep."
  [kb context remaining]
  (let [tx (reasoning/taxonomy kb)]
    (loop [findings []
           units    (keep #(orthogonal-separation kb tx % context)
                          (visible-orthogonals kb context))]
      (if-let [finding (first units)]
        (if (and remaining (>= (count findings) remaining))
          {:status :truncated :reason :max-results :findings findings}
          (do
            (budget/record! :orthogonal-over-separation finding)
            (recur (conj findings finding) (rest units))))
        {:status :complete :findings findings}))))

;; ---- shared by the three ontology-engineering passes below ----

(defn- bounded-findings
  "Record each finding of the lazy `units` under `category`, one at a time, stopping
  after the first finding beyond `remaining` proves that the result bound truncated
  the sweep."
  [category units remaining]
  (loop [findings []
         units    units]
    (if-let [finding (first units)]
      (if (and remaining (>= (count findings) remaining))
        {:status :truncated :reason :max-results :findings findings}
        (do
          (budget/record! category finding)
          (recur (conj findings finding) (rest units))))
      {:status :complete :findings findings})))

(defn- handle-records
  "The believed sentexes among `handles`, as `{:handle :sentence :context}` maps in
  content order — the shape `stated-records` names a declaration in."
  [kb handles]
  (let [tms  (reasoning/tms kb)
        recs (:records kb)]
    (->> handles
         (into [] (comp (filter #(jtms/in? tms %))
                        (keep #(p/get-sentex recs %))
                        (map (fn [s] {:handle (:id s) :sentence (sx/sentence-of s)
                                      :context (:context s)}))))
         (sort-by (juxt :sentence :context) nm/compare-form)
         vec)))

(defn- stated-pairs
  "Every believed **premise** `(functor a b)` over two distinct ground symbols that
  `context` sees, as `[a b record]` in content order: the one open read of a pass over
  stated declarations, a census of declarations rather than of any extent.  A sentence a
  rule derived is no premise and is not read."
  [kb functor context]
  (let [tms  (reasoning/tms kb)
        recs (:records kb)]
    (->> (res/matches-visible kb (list functor '?a '?b) context)
         (keep (fn [[h b]]
                 (budget/spend!)
                 (let [a (get b '?a) c (get b '?b)]
                   (when (and (symbol? a) (not (sx/variable? a))
                              (symbol? c) (not (sx/variable? c))
                              (not= a c)
                              (jtms/in? tms h)
                              (jtms/premise? tms h))
                     (when-let [s (p/get-sentex recs h)]
                       [a c {:handle h :sentence (sx/sentence-of s) :context (:context s)}])))))
         (into [] (distinct))
         (sort-by (fn [[_ _ r]] [(:sentence r) (:context r)]) nm/compare-form))))

;; ---- twin-genls: sibling types with one direct genl set, a missing common parent ----

(defn- twin-groups
  "`{genl-set #{type …}}` over every type the taxonomy holds whose direct `genl` set, as
  `context` reads it, names two types or more besides `thing`.  A type is read as
  `suggestible-type?` reads one."
  [kb tx context]
  (reduce (fn [groups t]
            (budget/spend!)
            (let [gs (when (symbol? t) (tax/direct-genls tx t context))]
              (if (and (>= (count (disj (set gs) 'thing)) 2)
                       (suggestible-type? kb tx t context))
                (update groups (set gs) (fnil conj #{}) t)
                groups)))
          {}
          (tax/types tx)))

(defn- twin-genls-findings
  "Group every type by its direct `genl` set, and report each set two types or more
  share, in print order of the set and then of its types."
  [kb context remaining]
  (let [tx (reasoning/taxonomy kb)]
    (bounded-findings
     :twin-genls
     (->> (twin-groups kb tx context)
          (keep (fn [[gs ts]]
                  (when (> (count ts) 1)
                    {:types (vec (sort-by nm/print-key ts))
                     :genls (vec (sort-by nm/print-key gs))})))
          (sort-by (fn [{:keys [types genls]}]
                     [(mapv nm/print-key genls) (mapv nm/print-key types)])))
     remaining)))

;; ---- derivable-stated-edge: a stated genl or disjoint that holds without itself ----

(defn- path-avoiding
  "The shortest visible `genl` path `[a … b]` from `a` to `b` that does not walk the
  edge `a`→`b` itself, or nil."
  [tx a b context]
  (loop [frontier [a] parent {a nil}]
    (when (seq frontier)
      (let [step (for [n frontier
                       g (sort-by nm/print-key (tax/direct-genls tx n context))
                       :when (not (and (= n a) (= g b)))
                       :when (not (contains? parent g))]
                   (do (budget/spend!) [g n]))
            parent' (reduce (fn [m [g n]] (if (contains? m g) m (assoc m g n))) parent step)]
        (if (contains? parent' b)
          (vec (reverse (take-while some? (iterate parent' b))))
          (recur (vec (distinct (map first step))) parent'))))))

(defn- derivable-genl
  "The finding for one stated `(genl a b)`, or nil: another believed supporter of the
  edge (the same sentence stated again, a rule's derivation, a roster installing it), or
  another `genl` path from `a` to `b` that does not walk the edge."
  [kb tx [a b stated] context]
  (budget/spend!)
  (let [others (handle-records kb (disj (tax/genl-edge-supporters tx a b context)
                                        (:handle stated)))]
    (if (seq others)
      {:stated stated :also-stated-by others}
      (when (some (fn [p]
                    (budget/spend!)
                    (and (not= p b) (tax/genl? tx p b context)))
                  (tax/direct-genls tx a context))
        (when-let [path (path-avoiding tx a b context)]
          {:stated stated :path path})))))

(defn- derivable-disjoint
  "The finding for one stated `(disjoint a b)`, or nil: the separations `context` sees
  over the pair, or over a supertype of each, besides this one statement — another
  supporter of the same pair, a separation of two supertypes, a `partition` or
  `separating` roster, a `sibling_disjoint` parent or a `disjoint_metatype`."
  [kb tx [a b stated] context]
  (budget/spend!)
  (let [k    [:disjoint #{a b}]
        same (handle-records kb (disj (tax/visible-supporters tx k context)
                                      (:handle stated)))
        apart (stated-records kb tx (disj (tax/separating-keys tx a b context) k) context)]
    (when (or (seq same) (seq apart))
      {:stated stated :separated-by (vec (concat same apart))})))

(defn- derivable-stated-edge-findings
  "Audit every visible stated `genl`, then every visible stated `disjoint`, one at a
  time, in content order."
  [kb context remaining]
  (let [tx (reasoning/taxonomy kb)]
    (bounded-findings
     :derivable-stated-edge
     (concat (keep #(derivable-genl kb tx % context) (stated-pairs kb 'genl context))
             (keep #(derivable-disjoint kb tx % context) (stated-pairs kb 'disjoint context)))
     remaining)))

;; ---- disjoint-could-be-partition: a disjoint whose pair a known cover exhausts ----

(defn- partition-sentence [whole parts]
  (apply list 'partition whole (sort-by nm/print-key parts)))

(defn- pairwise-disjoint?
  "Does `context` read every two of `parts` apart?"
  [tx parts context]
  (every? (fn [[x y]] (budget/spend!) (tax/disjoint? tx x y context))
          (for [x parts y parts :when (neg? (compare (nm/print-key x) (nm/print-key y)))]
            [x y])))

(defn- partition-candidates
  "The suggestions one stated `(disjoint a b)` gives, in print order of the whole: each
  visible `covering` naming both whose parts `context` reads pairwise apart (basis
  `:covering`), and each common direct parent whose direct specs are exactly the pair
  and that no visible cover already names them under (basis `:sole-specs`)."
  [kb tx [a b stated] context]
  (budget/spend!)
  (let [covers   (tax/covers-naming-visible tx a context)
        named?   (fn [whole kind]
                   (some (fn [[w ps k]] (and (= w whole) (= k kind) (some #{b} ps)))
                         covers))
        covering (for [[whole parts kind] covers
                       :when (and (= :covering kind) (some #{b} parts)
                                  (not= whole a) (not= whole b)
                                  (not (named? whole :partition))
                                  (pairwise-disjoint? tx parts context))]
                   {:disjoint stated :suggest (partition-sentence whole parts)
                    :basis :covering
                    :cover (cover-sentences kb tx whole parts context)})
        covered  (into #{} (map #(second (:suggest %))) covering)
        sole     (for [c (sort-by nm/print-key
                                  (filter (set (tax/direct-genls tx b context))
                                          (tax/direct-genls tx a context)))
                       :when (and (not= c a) (not= c b)
                                  (not (covered c))
                                  (not (named? c :partition))
                                  (do (budget/spend!)
                                      (= #{a b} (disj (set (tax/direct-specs tx c context))
                                                      c))))]
                   {:disjoint stated :suggest (partition-sentence c [a b])
                    :basis :sole-specs})]
    (sort-by #(nm/print-key (second (:suggest %))) (concat covering sole))))

(defn- disjoint-could-be-partition-findings
  "Audit every visible stated `disjoint`, one at a time, in content order."
  [kb context remaining]
  (let [tx (reasoning/taxonomy kb)]
    (bounded-findings
     :disjoint-could-be-partition
     (mapcat #(partition-candidates kb tx % context) (stated-pairs kb 'disjoint context))
     remaining)))

;; ---- missing-arg: a declared argument position no declaration types ----

(def ^:private positional-kinds
  "The declarations that type one numbered position, `(K P n T)`."
  '[arg genlArg quotedArg])

(def ^:private rest-kinds
  "The declarations that type position `n` and every later one, `(K P n T)`."
  '[argAndRest argAndRestGenl])

(def ^:private every-kinds
  "The declarations that type every position, `(K P T)`."
  '[args argsGenl])

(defn- declared-rows
  "The ground `[pos type]` rows of every `(kind q pos type)` (or `(kind q type)`, `pos`
  nil, when `pos?` is false) visible from `context` over `pred` and each super-predicate
  `res/constraining-predicates` reads for `kind`."
  [kb kind pred pos? context]
  (for [q     (distinct (cons pred (res/constraining-predicates kb kind pred context)))
        [_ b] (res/matches-visible kb (if pos? (list kind q '?n '?t) (list kind q '?t))
                                   context)
        :let  [n (get b '?n) t (get b '?t)]
        :when (and (some? t) (not (sx/variable? t))
                   (or (not pos?) (integer? n)))]
    (do (budget/spend!) [n t])))

(defn- typed-positions
  "`{:at #{n …} :from n-or-nil :every? bool}` for `pred` as `context` reads its
  declarations: the positions one declaration types, the first position a rest form
  types onward, and whether a form types them all.  The binary `arg1`/`arg2`/`arg3`
  projections are read on `pred` itself."
  [kb pred context]
  {:at     (into (set (for [k positional-kinds [n _] (declared-rows kb k pred true context)] n))
                 (for [[k n] '[[arg1 1] [arg2 2] [arg3 3]]
                       :when (do (budget/spend!)
                                 (seq (res/matches-visible kb (list k pred '?t) context)))]
                   n))
   :from   (some->> (for [k rest-kinds [n _] (declared-rows kb k pred true context)] n)
                    seq (apply min))
   :every? (boolean (some #(seq (declared-rows kb % pred false context)) every-kinds))})

(defn- arity-census
  "`{pred n-or-:variable}` over every predicate `context` sees declared an arity: an
  `(arity P n)`, an exact-arity class membership, or `variable_arity_predicate`.  A
  predicate told two different arities is skipped, as `kb/relation-arity` reads it."
  [kb context]
  (let [subjects (fn [pattern]
                   (keep (fn [[_ b]]
                           (budget/spend!)
                           (let [p (get b '?p)]
                             (when (and (symbol? p) (not (sx/variable? p))) p)))
                         (res/matches-visible kb pattern context)))
        fixed    (distinct (concat (subjects '(arity ?p ?n))
                                   (mapcat #(subjects (list % '?p))
                                           (keys tax/exact-arity-classes))))]
    (merge (into {} (map (fn [p] [p :variable])) (subjects '(variable_arity_predicate ?p)))
           (into {} (keep (fn [p]
                            (budget/spend!)
                            (when-let [n (kb/relation-arity kb p context)] [p n])))
                 fixed))))

(defn- arity-min
  "The least `arityMin` `context` sees declared of `pred`, or 1."
  [kb pred context]
  (or (some->> (res/matches-visible kb (list 'arityMin pred '?n) context)
               (keep (fn [[_ b]] (let [n (get b '?n)] (when (integer? n) n))))
               seq (apply min))
      1))

(defn- missing-positions
  "The finding for one predicate of declared arity `arity`, or nil: each position 1..n
  (1..`arityMin` for a variable arity, and `:rest` for its tail) no declaration types.
  A unary predicate's one position is typed by any visible `genl` edge out of it, which
  says of its members what `(arg P 1 T)` would."
  [kb tx pred arity context]
  (budget/spend!)
  (let [{:keys [at from every?]} (typed-positions kb pred context)
        typed?  (fn [n] (or every? (contains? at n) (and from (>= n from))))
        n       (if (= :variable arity) (arity-min kb pred context) arity)
        missing (cond-> (vec (remove typed? (range 1 (inc n))))
                  (and (= :variable arity) (not every?) (not (and from (<= from (inc n)))))
                  (conj :rest))
        missing (if (and (= 1 arity) (= [1] missing)
                         (seq (disj (set (tax/direct-genls tx pred context)) pred)))
                  []
                  missing)]
    (when (seq missing)
      {:predicate pred :arity arity :missing missing})))

(defn- missing-arg-findings
  "Audit every predicate `context` sees declared an arity, one at a time, in print order."
  [kb context remaining]
  (let [tx (reasoning/taxonomy kb)]
    (bounded-findings
     :missing-arg
     (keep (fn [[pred arity]] (missing-positions kb tx pred arity context))
           (sort-by (comp nm/print-key key) (arity-census kb context)))
     remaining)))

(def ^:private passes
  "The passes in run order, `[category audit]`: `audit` takes `kb candidate-terms context
  remaining` and answers `{:status :complete|:truncated :findings …}`.  `:max-results`
  counts findings in this order."
  [[:definition-inconsistencies provers/definition-inconsistencies]
   [:all-specified-violations (fn [kb _ context remaining]
                                (specified-findings kb context remaining))]
   [:genl-arg-widening (fn [kb _ context remaining]
                         (widening-findings kb context remaining))]
   [:not-under-thing not-under-thing-findings]
   [:implicit-genl implicit-genl-findings]
   [:orthogonal-over-separation (fn [kb _ context remaining]
                                  (orthogonal-over-separation-findings kb context remaining))]
   [:twin-genls (fn [kb _ context remaining]
                  (twin-genls-findings kb context remaining))]
   [:derivable-stated-edge (fn [kb _ context remaining]
                             (derivable-stated-edge-findings kb context remaining))]
   [:disjoint-could-be-partition (fn [kb _ context remaining]
                                   (disjoint-could-be-partition-findings kb context remaining))]
   [:missing-arg (fn [kb _ context remaining]
                   (missing-arg-findings kb context remaining))]])

(defn- check-args!
  "Refuse a `candidate-terms` that is not a set of ground terms (`:bad-args`), and a
  `:categories` that is not a set of the categories `passes` names (`:unknown-option`)."
  [candidate-terms categories]
  (when-not (set? candidate-terms)
    (throw (ex-info "kb-integrity candidate-terms must be a finite set"
                    {:type :bad-args :op 'kb-integrity :arg :candidate-terms})))
  (when-let [term (first (remove sx/ground-term? candidate-terms))]
    (throw (ex-info "kb-integrity candidate-terms must all be ground"
                    {:type :bad-args :op 'kb-integrity :arg :candidate-terms :term term})))
  (let [known (mapv first passes)]
    (when-not (or (nil? categories) (and (set? categories) (every? (set known) categories)))
      (throw (ex-info (str "kb-integrity :categories must be a set of "
                           (str/join ", " known) ", got " (pr-str categories))
                      {:type :unknown-option :mismatch :bad-value
                       :option :categories :value categories})))))

(defn- run-passes
  "Run the `passes` that `categories` names (every one when nil) in order, each with what
  is left of `max-results`: nil when every pass completed, `:max-results` when one
  stopped at the cap."
  [kb candidate-terms context max-results categories]
  (loop [[[_ audit] & more] (filter #(or (nil? categories) (categories (first %))) passes)
         remaining          max-results]
    (when audit
      (let [result (audit kb candidate-terms context remaining)]
        (if (= :truncated (:status result))
          :max-results
          (recur more (some-> remaining (- (count (:findings result))))))))))

(defn- report-categories
  "The non-empty categories of a meter's findings, the specified category as a map."
  [found]
  (into {}
        (keep (fn [[k xs]]
                (when (seq xs)
                  [k (if (= :all-specified-violations k) (into {} xs) xs)])))
        found))

(defn kb-integrity
  "Run the bounded integrity sweep in `context` over the finite set of ground
  `candidate-terms`.  Answers `{:status :audited :candidate-count n}` when no pass finds
  anything, `:status :gap` with the non-empty categories otherwise, and `:status
  :truncated` with its `:reason`, `:work`, `:elapsed-ms` and the findings kept before a
  bound in `options` (`integrity-opt-keys`) ran out.  `:categories`, a set of category
  keys, runs those passes alone.  Reads only: a diagnostic raised by
  evaluating a condition goes to a sink local to the call.  See docs/integrity.md."
  ([kb candidate-terms context]
   (kb-integrity kb candidate-terms context nil))
  ([kb candidate-terms context options]
   (budget/check-budget! options integrity-opt-keys "kb-integrity")
   (check-args! candidate-terms (:categories options))
   (let [candidate-count (count candidate-terms)
         m               (budget/meter options)
         reason          (binding [violations/*report-sink* (atom [])]
                           (budget/metered
                            m #(try (run-passes kb candidate-terms context
                                                (:max-results options) (:categories options))
                                    (catch clojure.lang.ExceptionInfo e
                                      (or (budget/exhausted e) (throw e))))))
         found           (report-categories (budget/found m))]
     (cond
       reason      (merge {:status :truncated :reason reason :candidate-count candidate-count}
                          (budget/snapshot m) found)
       (seq found) (merge {:status :gap :candidate-count candidate-count} found)
       :else       {:status :audited :candidate-count candidate-count}))))

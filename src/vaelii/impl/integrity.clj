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
                                  (orthogonal-over-separation-findings kb context remaining))]])

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

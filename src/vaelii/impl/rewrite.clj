;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.rewrite
  "Symbolic (schematic) equational rewriting — the oriented term-rewriting half of
  equality, the gap docs/equality.md leaves open.

  A schematic equation `(equals L R)` with variables — `(equals (fatherOf (fatherOf
  ?x)) (grandfatherOf ?x))` — is not a merge of two symbols (that is the partition,
  docs/equality.md) nor a ground reifiable-NAT compound (that reifies to symbols,
  docs/nat.md).  It is a **rewrite rule over a schema**: oriented into a terminating
  reduction `L → R`, it lets a term be normalized so that a stored `(parentChain
  (fatherOf (fatherOf Tom)))` and a query `(parentChain (grandfatherOf Tom))` meet at
  one normal form.

  ## Orientation and termination

  An equation is oriented by a **reduction order** — the Knuth-Bendix order `kbo>`
  with unit weights — so rewriting strictly decreases every term at each step and
  therefore terminates, whatever the rule set and without any confluence/completion
  argument (`orient`).  The heavier side (by `term-size`) rewrites to the lighter; an
  **equal-weight** pair is oriented by a fixed symbol precedence (root, then
  lexicographically on the arguments), so a shape like `(f (g ?x)) = (g (f ?x))`
  orients where a size-only rule would refuse it.  Both are gated by the variable
  condition (`var-dominates?`), which keeps the order stable under *every*
  substitution.  Only a **permutative** equation — `(rel ?x ?y) = (rel ?y ?x)`, which
  no term order can orient — or one whose variable condition fails both ways is
  refused (`orient` returns nil).

  ## What normalizes, and what does not

  Rewriting applies to **terms in argument position** — the denoting terms a
  schematic equation is about — never to a top-level predication (`normalize-sentence`
  keeps the sentence's functor and rewrites each argument).  `fatherOf` the function
  symbol and `fatherOf` a predicate are the same symbol; protecting the predication is
  what stops a rule about the *term* `fatherOf(fatherOf(x))` from rewriting a *fact*
  that merely happens to share the shape.

  This namespace is **pure**: it takes the oriented rules as data and knows nothing of
  the store, the taxonomy, or belief.  The taxonomy caches the active oriented rules
  (belief-following, like the equality partition), `vaelii.impl.kb` threads
  `normalize-sentence` into `rewrite-term` so migration and query both see one normal
  form, and `vaelii.impl.special` justifies each rewritten twin — the same
  belief-following machinery ground congruence already uses.  Bottom layer: it
  requires only `vaelii.impl.sentex`."
  (:require [vaelii.impl.sentex :as sx]))

;; ---- term structure ------------------------------------------------------

(defn- subterms
  "Every subterm of `term` — each atom and each compound, `term` itself included."
  [term]
  (if (sequential? term)
    (cons term (mapcat subterms term))
    (list term)))

(defn term-size
  "The KBO unit weight of `term`: the count of symbol / variable / number leaves,
  functors included.  `(fatherOf (fatherOf ?x))` is 3, `(grandfatherOf ?x)` is 2."
  [term]
  (if (sequential? term) (reduce + 0 (map term-size term)) 1))

(defn- var-counts
  "A map of each pattern variable in `term` to how many times it occurs."
  [term]
  (frequencies (filter sx/variable? (tree-seq sequential? seq term))))

(defn- var-dominates?
  "Does every variable occur at least as often in `a` as in `b`?  The KBO variable
  condition `#(x,a) ≥ #(x,b)` for every variable x — necessary for `a ≻ b`, or a
  substitution duplicating a variable `b` has more of could make the rewrite grow."
  [a b]
  (let [ca (var-counts a)]
    (every? (fn [[v n]] (>= (get ca v 0) n)) (var-counts b))))

(defn- prec>
  "The symbol precedence: a fixed, **content-derived** total order on function symbols
  (their natural `compare`), so orientation never depends on which equation was
  asserted first.  Arbitrary but deterministic — it decides the *direction* of an
  equal-weight rewrite, not whether one exists.  `(prec> a b)` is `a ≻_F b`."
  [a b]
  (neg? (compare b a)))

;; Genuine in-file cycle: a same-root equal-weight pair is decided by `kbo-lex>` over the
;; arguments, and the first differing position is decided by `kbo>` again.  The recursion
;; is the order's own definition, so no ordering of the two removes it.
(declare kbo>)

(defn- kbo-lex>
  "Lexicographic KBO on two equal-length argument lists (reached only when the roots
  are the same symbol): at the first differing position, the left argument must
  dominate under `kbo>`."
  [ss ts]
  (cond
    (empty? ss)               false
    (= (first ss) (first ts)) (recur (rest ss) (rest ts))
    :else                     (kbo> (first ss) (first ts))))

(defn kbo>
  "The **Knuth-Bendix order** with unit weights: is `s ≻ t`?  A genuine reduction order
  (stable under substitution and context, well-founded), so a rule `l → r` with `l ≻ r`
  terminates whatever the rule set — the termination guarantee for schematic rewriting.

  Decided in order: the variable condition gates it; then the heavier side wins; an
  equal-weight pair is decided by the root symbol precedence, and same-root by a
  lexicographic comparison of the arguments.  With unit weights `term-size` *is* the
  weight, so this refines the old size-only rule — it agrees on unequal sizes and
  additionally orients an equal-size pair like `(f (g ?x))` vs `(g (f ?x))`."
  [s t]
  (and (var-dominates? s t)
       (let [ws (term-size s) wt (term-size t)]
         (cond
           (> ws wt)      true
           (< ws wt)      false
           (sx/variable? s) false          ; a variable is minimal
           (sx/variable? t) false          ; equal weight + t a variable ⇒ not > (var cond already gates)
           :else (let [f (first s) g (first t)]
                   (cond
                     (prec> f g) true
                     (prec> g f) false
                     :else       (kbo-lex> (rest s) (rest t))))))))

(defn orient
  "Orient `(equals l r)` into a terminating rewrite `[big small]`, or nil when no
  terminating orientation exists.  The Knuth-Bendix order (`kbo>`) decides: the heavier
  side rewrites to the lighter, and two **equal-weight** sides are oriented by the
  symbol precedence — so `(f (g ?x)) = (g (f ?x))` now orients, where a size-only rule
  refused it.  nil only when the sides are KBO-**incomparable**: a *permutative*
  equation like `(rel ?x ?y) = (rel ?y ?x)`, which no term order can orient, or one
  whose variable condition fails in both directions."
  [l r]
  (cond
    (kbo> l r) [l r]
    (kbo> r l) [r l]
    :else nil))

;; ---- one-way matching + substitution -------------------------------------

(def ^:private no-match ::no-match)

(defn- match*
  [pattern subject sigma]
  (cond
    (= sigma no-match)  no-match
    (sx/variable? pattern)
    (if (contains? sigma pattern)
      (if (= (get sigma pattern) subject) sigma no-match)
      (assoc sigma pattern subject))
    (and (sequential? pattern) (sequential? subject))
    (if (= (count pattern) (count subject))
      (reduce (fn [sig [p s]] (match* p s sig)) sigma (map vector pattern subject))
      no-match)
    (or (sequential? pattern) (sequential? subject)) no-match
    :else (if (= pattern subject) sigma no-match)))

(defn match
  "One-way match of `pattern` (a rule LHS, whose variables may bind) against
  `subject` (a term, possibly variable-bearing): the substitution σ of the pattern's
  variables with `(subst pattern σ) = subject`, or nil.  Only the pattern's variables
  bind — a variable in the subject is treated as an opaque constant — so a rule never
  captures a query's variables, and since orientation forbids an RHS variable absent
  from the LHS, σ binds every variable the RHS will substitute."
  [pattern subject]
  (let [r (match* pattern subject {})]
    (when (not= r no-match) r)))

(defn- subst
  "`term` with each variable replaced by its binding in `sigma` (an unbound variable
  left as-is), recursively."
  [term sigma]
  (cond
    (sx/variable? term)   (get sigma term term)
    (sequential? term)    (apply list (map #(subst % sigma) term))
    :else                 term))

;; ---- normalization -------------------------------------------------------

(def ^:private normalize-guard
  "A pure safety net.  The reduction order already guarantees termination, so this
  bound is never reached; it exists only so a would-be bug fails safe (return the
  partly-normalized term) rather than hanging.  `unify` remains the arbiter of every
  match, so a partly-normalized form can only *miss*, never match wrongly."
  4096)

(defn- rewrite-root
  "Rewrite `term` at its root with the first applicable rule, or nil when none
  applies.  `rules` is a seq of `{:lhs :rhs}` oriented pairs."
  [rules term]
  (some (fn [{:keys [lhs rhs]}]
          (when-let [sigma (match lhs term)] (subst rhs sigma)))
        rules))

(defn normalize
  "The normal form of `term` under the oriented `rules`: rewrite innermost subterms to
  a fixpoint, then the root, repeating until nothing applies.  Terminates by the
  reduction order (each root rewrite strictly decreases size); the guard is a pure
  safety net."
  [rules term]
  (loop [term term, guard 0]
    (let [term' (if (sequential? term)
                  (apply list (first term) (map #(normalize rules %) (rest term)))
                  term)]
      (if-let [red (and (< guard normalize-guard) (rewrite-root rules term'))]
        (recur red (inc guard))
        term'))))

(defn normalize-sentence
  "Normalize a **sentence** `(pred arg…)`: rewrite each argument as a term, leaving the
  predication's functor and shape untouched.  A schematic equation is about denoting
  terms, which live in argument position; a predication is an assertion, not a term.
  A no-op when `rules` is empty."
  [rules sentence]
  (if (and (seq rules) (sequential? sentence) (seq sentence))
    (apply list (first sentence) (map #(normalize rules %) (rest sentence)))
    sentence))

;; ---- schematic-equation detection ----------------------------------------

(defn- has-variable? [form]
  (boolean (some sx/variable? (tree-seq sequential? seq form))))

(defn schematic-equation?
  "Is `sentence` a schematic equational rule — an `(equals L R)` whose sides carry a
  variable-bearing compound?  This is the shape that becomes a rewrite rule rather
  than a partition merge: `equals` specifically (not `sameAs`, individuals-only, nor
  `rewriteOf`, whose compound form is a NAT declaration), with a compound side and a
  variable, so a ground `(equals (F a) (F b))` — which reifies to symbols — is *not*
  one."
  [sentence]
  (and (sequential? sentence)
       (= 'equals (first sentence))
       (= 3 (count sentence))
       (some sequential? (rest sentence))
       (has-variable? sentence)))

(defn rule-applies?
  "Does the oriented rule `{:lhs …}` rewrite some argument subterm of `sentence`?  The
  test for whether a schematic equation justifies a migrated twin — a rule that
  matches nothing in the sentence contributed nothing to its normal form."
  [{:keys [lhs]} sentence]
  (boolean (some #(some (fn [st] (match lhs st)) (subterms %))
                 (when (sequential? sentence) (rest sentence)))))

;; ---- confluence surfacing: critical pairs between rules ------------------
;; A terminating rewrite system is confluent iff every **critical pair** joins (the
;; critical-pair lemma).  Two rules `l1 → r1` and `l2 → r2` *overlap* when a
;; non-variable subterm of `l1` unifies with `l2`: the overlap term can then be
;; rewritten two ways, and if the results normalize to different forms the rules
;; disagree about a shared term.  This is **detection, not completion** — the engine
;; still gives a deterministic normal form (rules applied in a content-sorted order,
;; `unify` the arbiter), so a match is never wrong; the report warns that a term
;; written one way and a theory-equal term written another may not meet.
;;
;; **Self-overlaps are excluded.**  A single rule's internal non-confluence — `(f (f
;; ?x)) → (g ?x)` reduces `f³` two ways in the abstract — is absorbed by the
;; deterministic normalization (the same syntactic term always normalizes the same
;; way), so it never causes a stored-vs-query miss and is not worth flagging.  What is
;; worth surfacing is two **distinct** equations disagreeing, `f∘f = g` alongside `f∘f
;; = h`.

(defn- occurs? [subst v t]
  (let [t (if (and (sx/variable? t) (contains? subst t)) (get subst t) t)]
    (cond
      (= v t)         true
      (sequential? t) (some #(occurs? subst v %) t)
      :else           false)))

(defn- unify*
  [s t subst]
  (if (nil? subst)
    nil
    (let [s (if (and (sx/variable? s) (contains? subst s)) (get subst s) s)
          t (if (and (sx/variable? t) (contains? subst t)) (get subst t) t)]
      (cond
        (= s t)          subst
        (sx/variable? s) (when-not (occurs? subst s t) (assoc subst s t))
        (sx/variable? t) (when-not (occurs? subst t s) (assoc subst t s))
        (and (sequential? s) (sequential? t) (= (count s) (count t)))
        (reduce (fn [sub [a b]] (unify* a b sub)) subst (map vector s t))
        :else            nil))))

(defn- unify
  "The most general unifier of `s` and `t` as a substitution map, or nil.  Two-way (both
  sides' variables may bind), with an occurs check so a cyclic binding cannot form."
  [s t]
  (unify* s t {}))

(defn- resolve-fully
  "`term` with every variable replaced by its (recursively resolved) binding in
  `subst` — the substitution applied to a fixpoint, safe because `unify`'s occurs check
  forbids a cycle."
  [subst term]
  (cond
    (sx/variable? term)  (if (contains? subst term) (resolve-fully subst (get subst term)) term)
    (sequential? term)   (apply list (map #(resolve-fully subst %) term))
    :else                term))

(defn- rename-rule
  "A rule with its variables renamed `prefix0`, `prefix1`, … by first occurrence, so two
  rules being overlapped share no variable names.  RHS variables are a subset of the
  LHS's (orientation guarantees it), so the LHS numbering covers both."
  [rule prefix]
  (let [vars (distinct (filter sx/variable? (tree-seq sequential? seq (:lhs rule))))
        m    (into {} (map-indexed (fn [i v] [v (symbol (str prefix i))]) vars))]
    {:lhs (subst (:lhs rule) m) :rhs (subst (:rhs rule) m)}))

(defn- positions
  "Every `[path compound-subterm]` of `term` — `path` a vector of child indices, `[]`
  the whole term.  Only compound subterms, since a rule LHS (always a compound) can
  overlap nothing else."
  [term]
  (letfn [(go [t path]
            (when (and (sequential? t) (seq t))
              (cons [path t]
                    (apply concat (map-indexed (fn [i c] (go c (conj path i))) t)))))]
    (go term [])))

(defn- replace-at
  "`term` with the subterm at `path` replaced by `new`."
  [term path new]
  (if (empty? path)
    new
    (let [i (first path)]
      (apply list (map-indexed (fn [j c] (if (= j i) (replace-at c (rest path) new) c)) term)))))

(defn- critical-pairs
  "The critical pairs where a subterm of `r1`'s LHS overlaps `r2`'s LHS: for each such
  overlap, `[rewrite r1 at the root, rewrite that subterm with r2]` under the unifier.
  `r1` and `r2` are renamed to disjoint variables first."
  [r1 r2]
  (let [{l1 :lhs rr1 :rhs} (rename-rule r1 "?a")
        {l2 :lhs rr2 :rhs} (rename-rule r2 "?b")]
    (for [[path sub] (positions l1)
          :let [sigma (unify sub l2)]
          :when sigma]
      [(resolve-fully sigma rr1)
       (resolve-fully sigma (replace-at l1 path rr2))])))

(defn non-joining-pairs
  "The overlaps between `new-rule` and the **other** rules in `all-rules` whose two
  reducts do not normalize to one form — the non-confluent conflicts worth surfacing.
  Each entry is `{:with <other handle> :form-a t :form-b t}`.  Self-overlaps are
  excluded (see the section note).  `all-rules` includes `new-rule`; it is the whole
  active set the reducts are normalized against."
  [new-rule all-rules]
  (let [others   (remove #(= (:handle %) (:handle new-rule)) all-rules)
        rulemaps (map #(select-keys % [:lhs :rhs]) all-rules)]
    (for [o others
          [a b] (distinct (concat (critical-pairs new-rule o) (critical-pairs o new-rule)))
          :let  [na (sx/canon (normalize rulemaps a))
                 nb (sx/canon (normalize rulemaps b))]
          :when (not= na nb)]
      {:with (:handle o) :form-a na :form-b nb})))

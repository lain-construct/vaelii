;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.fluent
  "The per-instant functionality audit for fluent-carried values.

  `functional` (checks / special) enforces at-most-one-value over the **bare** literals of
  a marked predicate: two co-believed `(P a v1)` / `(P a v2)` derive `(equals v1 v2)` and
  merge.  A value carried the event-calculus way never appears in a bare literal — it rides
  inside a fluent NAT under `initiates`, and `holdsAt` derives it at a moment (docs/time.md,
  CxChange).  So the equality closure never sees the pair, and per-instant functionality —
  a function that has at most one value for one subject at any single instant — is enforced
  by nothing at assert.

  Whether two fluents overlap at an instant follows from `initiates`, `terminates` and the
  clipping closure, and is not known when a fluent is asserted.  So this reads it on demand,
  the shape `vaelii.impl.predall/specified-violations` uses for the analogous reason: an
  audit reports, it does not mutate belief.  A merge-eligible clash (two symbol values) is
  reported as `:merge` and a non-mergeable one (two numbers or strings) as `:contradiction`,
  mirroring `functional`'s own split, and the caller decides what to do with the report.

  Reached from outside through `vaelii.core/functional-at-instant-violations` and
  `vaelii.core/all-functional-at-instant-violations`.  This namespace sits **above**
  `vaelii.core`, so it may `ask`; the delegation runs back down through
  `vaelii.impl.wiring`, the same arrangement `predall` uses."
  (:require [vaelii.core :as v]
            [vaelii.impl.nat :as nat]))

(def ^:private holds-at-depth
  "The backward search bound for one `(holdsAt fluent instant)` question.  `holdsAt` is a
  rule over `initiates` and the transitive `instantBefore` closure, negated on `clipped`;
  four levels reach the fixture's chain of moments with margin over the three the
  event-calculus tests answer at.  A bound is required rather than optional: `holdsAt` is
  backward-only and unbounded search over a long instant chain does not terminate cheaply."
  4)

(defn- fluent-fillers
  "Every `[subject value fluent]` a binary fluent function `f` carries, gathered from the
  `initiates` and `initially` facts believed in `context` — the candidates the audit tests
  at each moment.  A `reifiable_function` application is stored as a reified constant, so the
  `(f subject value)` shape is read from its `nat-expression` rather than off the constant;
  a fluent whose expression is not `(f a v)` is skipped.  The returned fluent is the term as
  stored, the form `holdsAt` is asked of.  `ask` follows belief, so a filler under a
  disbelieved `initiates` fact is not gathered."
  [kb f context]
  (let [from (fn [fl] (let [expr (if (nat/reified-nat-symbol? fl) (nat/nat-expression kb fl) fl)]
                        (when (and (seq? expr) (= f (first expr)) (= 3 (count expr)))
                          [(second expr) (nth expr 2) fl])))]
    (into #{}
          (comp (map from) (remove nil?))
          (concat (for [b (v/ask kb (list 'initiates '?e '?fluent '?t) context)]
                    (get b '?fluent))
                  (for [b (v/ask kb (list 'initially '?fluent) context)]
                    (get b '?fluent))))))

(defn functional-at-instant-violations
  "The per-instant clashes of one `(functional_at_instant f)` declaration in `context`, as a
  set of maps `{:function f :subject s :instant t :values #{v …} :kind k}` — one per
  moment `t` at which more than one distinct value of `f` holds for one subject `s`.  `:kind`
  is `:merge` when every clashing value is a symbol (the pair `functional` would merge) and
  `:contradiction` otherwise (two numbers or strings `functional` refuses outright).

  Every believed `time_point` is a candidate moment, and `holdsAt` is asked of each filler
  at each — so a value holding at a different instant from another is not a clash, which is
  what the event-calculus representation buys over a bare `functional` mark.  The read
  follows belief and is scoped to `context`, so two fillers in contexts that cannot see each
  other do not clash, and a filler whose initiating event is disbelieved is not a value."
  [kb f context]
  (let [fillers  (fluent-fillers kb f context)
        subjects (into #{} (map first) fillers)
        moments  (into #{} (map #(get % '?t)) (v/ask kb '(time_point ?t) context))]
    (into #{}
          (for [t moments
                s subjects
                :let [vals (into #{}
                                 (comp (filter (fn [[cs _ _]] (= s cs)))
                                       (filter (fn [[_ _ fl]]
                                                 (v/query? kb (list 'holdsAt fl t) context
                                                           {:max-depth holds-at-depth})))
                                       (map second))
                                 fillers)]
                :when (> (count vals) 1)]
            {:function f :subject s :instant t :values vals
             :kind (if (every? symbol? vals) :merge :contradiction)}))))

(defn all-functional-at-instant-violations
  "Every `(functional_at_instant f)` declaration visible in `context`, audited, as
  `{f #{violation …} …}` — declarations that clash nowhere are omitted, so a clean sweep is
  an empty map.  The one call an integrity sweep makes; `functional-at-instant-violations`
  is the per-declaration reader it is built from."
  [kb context]
  (into {}
        (for [b     (v/ask kb '(functional_at_instant ?f) context)
              :let  [f  (get b '?f)
                     vs (functional-at-instant-violations kb f context)]
              :when (seq vs)]
          [f vs])))

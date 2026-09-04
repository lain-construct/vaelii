;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.predall
  "The *Specified* half of the predAll / predExists / predInstance / predSpecified matrix
  (docs/predall.md, resources/kb/CxCore.txt).

  Reached from outside through `vaelii.core/specified-violations` and
  `vaelii.core/all-specified-violations`.  This namespace sits **above** `vaelii.core`,
  because auditing is asking and the audit asks through the public read path, so the
  delegation runs back down through `vaelii.impl.wiring`.

  Where the *Instance* relations stamp real inference and the *Exists* relations are
  inert records beside a sanctioned placeholder functor, `predAllSpecified` / `predSpecifiedAll` are an **integrity
  audit**: given a declaration that every instance of a collection ought to have a
  *determinate* filler, the reader here returns the instances that do not.  It is not a
  stored rule and concludes nothing — it reads the declaration and the beliefs and hands
  back the violations, the way a solve-time report does.

  **Indeterminate = the `indeterminate_term` category.**  A filler counts as determinate
  unless it is a member of the extensible `indeterminate_term` collection (CxCore.txt).
  Skolem constants are its built-in first member — a reified NAT whose expression is a
  `SkolemFn` application (docs/skolem.md), detected structurally because a skolem's
  membership is never a stored fact — and a further kind is added with
  `(genl NewKind indeterminate_term)`.  Whether a non-skolem NAT is determinate by default
  is punted (Pace): a plain individual, a literal and an *Exists* placeholder alike are
  all treated as determinate here, which is what makes `predAllSpecified` the exact
  antagonist of `predAllExists`."
  (:require [vaelii.core :as v]
            [vaelii.impl.provers :as provers]))

(defn indeterminate-term?
  "Is `term` an **indeterminate** filler in `ctx` — a member of the extensible
  `indeterminate_term` category (CxCore.txt)?  A skolem constant is the built-in first
  member, read off its `SkolemFn` minting expression because a skolem's membership is
  never a stored fact; a further kind added with `(genl NewKind indeterminate_term)` is
  picked up through ordinary collection membership.

  `vaelii.impl.provers/indeterminate-term?` **is** the implementation, so the audit and
  the `different` prover's UNA identity exemption cannot disagree about a term.  This
  namespace sits above the prover registry, which is what makes the call possible; two
  copies agreeing by inspection did diverge, on a membership one reader derived and the
  other read as stored.

  A non-skolem NAT that is not declared an `indeterminate_term`, a bare individual and a
  literal are all determinate; the blanket non-skolem-NAT determinacy question is punted
  (Pace)."
  [kb term ctx]
  (provers/indeterminate-term? kb term ctx))

(defn- slot-typings
  "The visible slot-`n` typing constraints of `pred` in `ctx`, as
  `[{:check :membership|:subtype :type t} …]` — one entry per believed
  `(arg pred n t)` (a membership constraint) and `(genlArg pred n t)` (a subtype
  constraint), plus the implicit subtype-of-`thing` constraint a
  `type_relation_predicate` membership states of every position.  That last arm is
  what CxCore's own note beside `genl` describes — its argument 2 is deliberately
  free of a `genlArg` declaration the root would fail, and \"the position is not
  thereby unconstrained: genl is a type_relation_predicate, which says of every one
  of its positions what genlArg says of one.\"  Read through `ask`, so
  `provers/MetaConstraintProver` composes the constraints inherited up the genl
  closure exactly as the assert-time checker's own reader walks them — the audit and
  the checker cannot disagree about what the predicate's contract says."
  [kb pred n ctx]
  (vec
   (concat
    (for [b (v/ask kb (list 'arg pred n '?t) ctx)
          :let [t (get b '?t)]
          :when (some? t)]
      {:check :membership :type t})
    (for [b (v/ask kb (list 'genlArg pred n '?t) ctx)
          :let [t (get b '?t)]
          :when (some? t)]
      {:check :subtype :type t})
    (when (v/ask? kb (list 'type_relation_predicate pred) ctx)
      [{:check :subtype :type 'thing}]))))

(defn- satisfies-typing?
  "Does filler `y` satisfy one derived slot constraint in `ctx`?  A membership
  constraint asks `(t y)`; a subtype constraint asks `(genl y t)`, with the type
  itself passing reflexively — a slot whose contract arrives through
  `type_relation_predicate` must not convict the filler `thing`, whose `genl`
  self-edge is nowhere stored.

  Both questions are the KB's OWN reading, deliberately.  For an `arg`-typed slot
  that means argument-type inference usually answers the membership off the very
  declaration the constraint was derived from, so a stored filler passes unless its
  membership is actively refuted — the conformance bite for instance-positions lives
  at the assert-time checker, which refuses a filler it can convict, and an audit
  stricter than the contract it derives from would be the second type system the
  binary form removes.  The subtype arm keeps real teeth: nothing derives a `genl`
  edge for a filler, so a kind with no visible path to the constraint type violates."
  [kb y {:keys [check type]} ctx]
  (case check
    :membership (v/ask? kb (list type y) ctx)
    :subtype    (or (= y type) (v/ask? kb (list 'genl y type) ctx))))

(defn- determinate-filler?
  "Does at least one determinate filler `y`, believed at position `arg-pos` of
  `(pred … x …)` in `ctx`, satisfy every derived slot constraint in `typings`?

  A binding that carries no `?y` is not a filler: the registry answers a goal with `[{}]`
  where a prover proves it without binding anything, and a typing question about nil is
  not a membership question."
  [kb pred x typings arg-pos ctx]
  (let [goal    (case arg-pos
                  :second (list pred x '?y)
                  :first  (list pred '?y x))
        answers (v/ask kb goal ctx)]
    (boolean
     (some (fn [b]
             (let [y (get b '?y)]
               (and (some? y)
                    (not (indeterminate-term? kb y ctx))
                    (every? #(satisfies-typing? kb y % ctx) typings))))
           answers))))

(defn specified-violations
  "Audit one binary `(predAllSpecified pred indep)` declaration in `ctx` and return a
  result map — `{:violations #{x …}}` where the audit ran (empty set = the requirement
  holds), or `{:gap :missing-slot-typing :pred pred :position n}` where `pred` carries
  no visible slot typing at the audited position, which is a declaration-contract gap
  reported explicitly rather than silently audited unconstrained.

  The required filler type is **derived from `pred`'s own argument contract**, never
  restated in the declaration: every visible `(arg pred n t)` requires the filler to be
  a member of `t`, every visible `(genlArg pred n t)` requires it to be a subtype of
  `t`, and multiple constraints compose conjunctively, as the assert-time checker
  composes them.

  `arg-pos` selects the twin: `:second` for `predAllSpecified` (the audited filler sits
  at `pred`'s second position), `:first` for `predSpecifiedAll` (the filler sits first
  and the quantified instance second).  Defaults to `:second`.

  A filler is indeterminate exactly when it is an `indeterminate_term` — a skolem (the
  built-in first member) or an extension declared with `(genl NewKind indeterminate_term)`
  — so an *Exists* placeholder passes and a skolemised witness does not, which is what
  makes this the antagonist of the *Exists* class."
  ([kb pred indep ctx] (specified-violations kb pred indep ctx :second))
  ([kb pred indep ctx arg-pos]
   (let [n       (case arg-pos :second 2 :first 1)
         typings (slot-typings kb pred n ctx)]
     (if (empty? typings)
       {:gap :missing-slot-typing :pred pred :position n}
       {:violations
        (into #{}
              (comp (map #(get % '?x))
                    (remove #(determinate-filler? kb pred % typings arg-pos ctx)))
              (v/ask kb (list indep '?x) ctx))}))))

(defn- declaration-args
  "Read the stored binary `(functor pred indep)` declarations in `ctx` as
  `[pred indep]` tuples."
  [kb functor ctx]
  (for [b (v/ask kb (list functor '?pred '?indep) ctx)]
    [(get b '?pred) (get b '?indep)]))

(defn all-specified-violations
  "Audit every `predAllSpecified` and `predSpecifiedAll` declaration visible in `ctx`
  and return `{[functor pred indep] result …}` — each result a
  `{:violations #{…}}` or a `{:gap …}` as `specified-violations` returns them.
  Declarations that hold are omitted; a declaration-contract gap never is, so a clean
  sweep is an empty map and a gap cannot pass as one.  The one call an integrity sweep
  makes; `specified-violations` is the per-declaration reader it is built from."
  [kb ctx]
  (into {}
        (for [[functor arg-pos] [['predAllSpecified :second]
                                 ['predSpecifiedAll :first]]
              [pred indep] (declaration-args kb functor ctx)
              :let [r (specified-violations kb pred indep ctx arg-pos)]
              :when (or (:gap r) (seq (:violations r)))]
          [[functor pred indep] r])))

;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.quasiquote
  "Quasiquotation — the metalinguistic constructor (mention-opacity: docs/argtypes.md).

  `(Quasiquote T)` builds the syntactic term `T` with each `(Unquote v)` hole replaced by
  `v`, and names the result *as syntax* — a mention.  `(Quasiquote (isa (Unquote ?x) Dog))`
  fired with `?x`=Fido constructs the term for `(isa Fido Dog)`.

  The model is **skolemization**, not the `evaluate` prover: a `Quasiquote` is a
  term-constructor sitting in argument position (`(believes Tom (Quasiquote …))`), built
  deterministically from a firing's bindings and reified before placement.  Reduction of a
  ground `(Quasiquote T)` strips its `Unquote` holes to the expression `E`, then reifies
  `(Quote E)` — `Quote` being a reifiable **quoting** function, so `E` reifies to an opaque
  `nat/` constant that mention-opacity holds apart from its referents' merges.  Determinism
  is content-addressed for free: `E` *is* the content, so `nat/reify-or-mint-nat` dedups two
  firings on one binding to one constant (no rule digest / frontier is needed, unlike a
  skolem witness, which is anonymous).

  `Quasiquote` is an `unreifiableFunction`, so an *open* template — the one that lives in a
  rule consequent until the antecedent binds its `Unquote` holes — stays structural and is
  never minted; range restriction (`rules/check-range-restricted`) already refuses a hole no
  antecedent binds, so an open template never reaches storage.  It is a `quotingFunction`
  too, so while it waits in the rule its `Unquote`-marked spellings are held opaque to an
  identity merge exactly as a `Quote` payload is.

  Turned on by declaration, like `reifiableFunction` turns the reify pass on: a KB that has
  not declared `(quotingFunction Quasiquote)` pays one taxonomy-prop read per firing/assert
  and the reducer is a no-op.  And like reification, it is **declared before use**: opacity is
  applied when a mention is reified and again in the equality congruence, each gated on the
  mark being present then, so `ensure-quasiquote-functions` (or the four marks) must precede
  the constructions it governs and any identity merge over the referents inside them.  A reify
  or merge processed while the mark is absent — before it is declared, or after it is retracted
  — is not held opaque and folds the mention onto its referent's class."
  (:require [vaelii.impl.nat :as nat]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.wiring :as wiring]))

(def quasiquote-function
  "The reserved template-constructor functor, keyed on by name like `skolem/SkolemFn`."
  'Quasiquote)

(def unquote-marker
  "The reserved hole marker: `(Unquote v)` inside a template splices `v` into the
  constructed expression.  Meaningful only inside a `Quasiquote` body."
  'Unquote)

(def quote-function
  "The reifiable quoting function a reduced template mentions its result through."
  'Quote)

(defn any-quasiquote?
  "Gate: is quasiquotation enabled — `(quotingFunction Quasiquote)` declared?  False ⇒ the
  reducer short-circuits, one prop read.  Mirrors `nat/any-reifiable-functions?`."
  [kb]
  (tax/quoting-function? (:taxonomy kb) quasiquote-function))

(defn ensure-quasiquote-functions
  "Enable quasiquotation as a unit — declare the four marks it needs, each only if absent:
  `Quote` reifiable + quoting (the constructed expression reifies to a mention constant) and
  `Quasiquote` unreifiable + quoting (an open template stays structural and is a mention).
  The last of them, `(quotingFunction Quasiquote)`, is the gate `any-quasiquote?` reads, so
  this call is what turns the reducer on.  Idempotent, asserted without chaining or settling
  since it is pure metadata — the shape `skolem/ensure-skolem-function` uses."
  [kb]
  (let [tax (:taxonomy kb)]
    (doseq [s (cond-> []
                (not (nat/reifiable-function? kb quote-function))
                (conj (list 'reifiableFunction quote-function))
                (not (tax/quoting-function? tax quote-function))
                (conj (list 'quotingFunction quote-function))
                (not (tax/has-prop? tax :unreifiable quasiquote-function))
                (conj (list 'unreifiableFunction quasiquote-function))
                (not (tax/quoting-function? tax quasiquote-function))
                (conj (list 'quotingFunction quasiquote-function)))]
      (wiring/assert-sentence kb s nat/universal-context {:strength :monotonic :chain? false}))))

(defn- unquote-form? [x]
  (and (seq? x) (= unquote-marker (first x)) (= 2 (count x))))

(defn quasiquote-form? [x]
  (and (seq? x) (= quasiquote-function (first x)) (= 2 (count x))))

(defn- ground? [form]
  (not-any? sx/variable? (tree-seq sequential? seq form)))

(defn- strip-unquotes
  "The template body `t` with each `(Unquote v)` replaced by `v` — the constructed
  expression.  A `Quasiquote` nested inside is its own mention level and is left **whole**,
  its `Unquote`s untouched, so it stays literal syntax in the constructed expression (and
  `reduce-term` holds it opaque there too — the two must agree, or a construction stored one
  way is queried another)."
  [t]
  (cond
    (unquote-form? t)    (second t)
    (quasiquote-form? t) t
    (vector? t)          (mapv strip-unquotes t)
    (seq? t)             (apply list (map strip-unquotes t))
    :else                t))

(defn- reduce-term
  "Every **ground** `(Quasiquote T)` subterm of `term` replaced by `(reify-fn (Quote E))`,
  `E` its constructed expression.  An open template (a hole still unbound) is left
  untouched — in a rule consequent it reduces at firing, once substitution grounds it; a
  direct open assert is a non-ground fact `wff` already refuses."
  [kb term reify-fn]
  (cond
    (and (quasiquote-form? term) (ground? term))
    (reify-fn (list quote-function (strip-unquotes (second term))))
    ;; a mention is opaque — a `quotingFunction` application (`Quote`, or an open/nested
    ;; `Quasiquote`) or a quoting-predicate payload (`termOfUnit` / `rewriteOf`, the reified
    ;; NAT's own bookkeeping): a `Quasiquote` nested inside is literal syntax, not reduced
    ;; here.  Without this the `(termOfUnit K E)` re-assert `mint-nat!` makes would re-run
    ;; over `E` and reduce a nested construction the write already fixed, leaving it stored
    ;; one way and queried (top level only) another.
    (and (seq? term)
         (or (contains? nat/nat-quoting-predicates (first term))
             (tax/quoting-function? (:taxonomy kb) (first term))))
    term
    (vector? term) (mapv #(reduce-term kb % reify-fn) term)
    (seq? term)    (apply list (map #(reduce-term kb % reify-fn) term))
    :else          term))

(defn maybe-reduce
  "Strip ground `Quasiquote`s to their `(Quote E)` mention form on the write and read
  paths, and stop — the reify pass beside it (`maybe-reify-nats` on write, mints;
  `maybe-reify-for-read` on read, dedups) reifies `(Quote E)`, so the two spellings of one
  construction meet at one constant.  Structural: mints nothing itself.  Gated — a no-op
  unless quasiquotation is declared."
  [kb sentence]
  (if (any-quasiquote? kb)
    (reduce-term kb sentence identity)
    sentence))

(defn reduce-in-conclusion
  "Reduce ground `Quasiquote`s in a fired conclusion, minting `(Quote E)` to its constant
  — the chain path (`chain/derive-conclusion`) places its conclusion directly and does not
  run the write reify pass, so it reifies here, beside skolemization.  The mints run under
  `*defer-settle?*` like a skolem's, so a mid-fixpoint construction does not settle belief.
  Gated."
  [kb raw]
  (if (any-quasiquote? kb)
    (binding [wiring/*defer-settle?* true]
      (reduce-term kb raw #(nat/reify-or-mint-nat kb %)))
    raw))

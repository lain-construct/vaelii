;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.skolem
  "Head existentials: the deterministic constant a rule head `(exists ?y C)` fires to.

  A rule head `(exists ?y C)` (docs/skolem.md) leaves `?y` unbound after the antecedent
  substitution.  Forward firing replaces it with a *deterministic* skolem constant so the
  semi-naive fixpoint terminates: the same `(rule, antecedent-binding)` must produce the
  same constant, or a re-derivation would mint a new one each round and never converge.
  The constant is a NAT `(SkolemFn <rule-digest> <exist-index> <frontier-values…>)` routed
  through the ordinary reify path — `nat/reify-or-mint-nat` dedups it against
  `termOfUnit`, so re-firing on the same binding resolves to the one constant.  A single
  skolem function reified per-argument (rather than a per-rule function name) means one
  lazy `reifiableFunction` declaration turns the whole mechanism on, and the frontier
  values in the arguments key determinism.

  A namespace of its own because it has **two callers on two layers** and belongs to
  neither.  The write path asks `has-existential-head?` when a rule is asserted, and
  declares the reifiable function then, so a rule that fires during its own assert already
  finds it; the forward chainer (`vaelii.impl.chain`) calls `skolemize-conclusion` at each
  firing.  Its own vocabulary is rules and firings — rule handles, frontier variables, a
  substituted conclusion — so it is not part of `vaelii.impl.nat`, which knows about
  reified terms and nothing about rules; minting is only *how* it makes the constant.

  The mint itself is a full assert, one layer above this one, reached through
  `vaelii.impl.wiring` — which is where the reason it cannot be a require is written down."
  (:require [vaelii.impl.nat :as nat]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.wiring :as wiring]))

(def skolem-function
  "The one reifiable function every skolem constant is an application of.  A NAT
  `(SkolemFn <rule-digest> <exist-index> <frontier-values…>)` reifies to a stable `nat/`
  constant; the rule's content digest and the frontier values in the arguments are what
  make it a function of the `(rule, binding)`, so no per-rule function name is needed."
  'SkolemFn)

(defn ensure-skolem-function
  "Declare `SkolemFn` a `reifiableFunction` if it is not already — so skolem NATs reify to
  `nat/` constants and the NAT orphan-cleanup gate (`nat/any-reifiable-functions?`) is on
  for retraction.  Idempotent, and asserted without chaining or settling since it is pure
  metadata."
  [kb]
  (when-not (nat/reifiable-function? kb skolem-function)
    (wiring/assert-sentence kb (list 'reifiableFunction skolem-function)
                            nat/universal-context
                            {:strength :monotonic :chain? false})))

(defn has-existential-head?
  "Does `sentence` assert a rule whose consequent is a head existential `(exists ?y C)`?
  Read past any `set/*Rule` / `exceptWhen` wrapper."
  [sentence]
  (and (sequential? sentence)
       (let [inner (rules/inner-rule sentence)]
         (and (rules/rule-sentence? inner)
              (sx/head-exists? (rules/consequent inner))))))

(defn- frontier-vars
  "A rule's consequent variables that its antecedents bind — the universal parameters an
  existential witness depends on, in a deterministic (sorted) order so the skolem's
  argument list is stable across firings and across the conjuncts of one head.

  **A post-join literal's output is not one of them.**  An aggregate is an antecedent and
  its `?n` may well appear in the consequent, but `?n` is computed per *placement*, after
  the witness is minted — so the bindings here do not hold it, and it would substitute to
  itself and put a variable in the skolem NAT's argument list.  `chain`'s
  `free-consequent-vars` subtracts the same set at the same moment, for the same reason;
  an ordinary rule carries no post-join literals and this is a no-op for it."
  [rule]
  (let [vars  #(filter sx/variable? (tree-seq sequential? seq %))
        post  (into #{} (mapcat sx/deferred-output-vars) (:post-join rule))
        avars (into #{} (mapcat vars) (:antecedents rule))
        cvars (distinct (vars (:consequent rule)))]
    (vec (sort (remove post (filter avars cvars))))))

(defn- rule-digest
  "The content key a skolem constant carries: the hex SHA-1 of the rule's canonical
  antecedents, consequent and context.  A witness is a function of the *rule*, and the
  rule's identity is its content — so the same rule re-asserted after a retraction, or
  asserted into a KB built in another order, mints the same witness NAT, and a fact
  stated about a witness keeps referring to it.  Anything store-assigned here (a
  handle) would put assertion order into stored `termOfUnit` content, which order
  independence rules out; the chase literature keys skolem terms the same way, on the
  rule and its existential position, never on a store id."
  [rule]
  ;; print vars bound off: the digest lands in stored `termOfUnit` content, and an
  ;; ambient *print-length*/*print-level* (a REPL's, typically) would elide the rule
  ;; out of its own identity — two rules digesting alike merge their witnesses
  (let [s (binding [*print-length* nil *print-level* nil *print-meta* false]
            (pr-str [(:antecedents rule) (:consequent rule) (:context rule)]))
        d (.digest (java.security.MessageDigest/getInstance "SHA-1")
                   (.getBytes ^String s "UTF-8"))]
    (apply str (map #(format "%02x" %) d))))

(defn skolemize-conclusion
  "Replace each still-unbound (existential) variable `free` in a rule's substituted
  conclusion `raw` with its deterministic skolem constant, and return the ground
  conclusion.

  The skolem for the i-th existential variable (existentials sorted, so `i` is stable) is
  the NAT `(SkolemFn <rule-digest> i <frontier-values…>)` reified to a `nat/` constant.
  Because the arguments are a function of the rule's content and this firing's frontier
  values, two firings on the same antecedent binding reify to the *same* constant
  (`reify-or-mint-nat` dedups via `termOfUnit`) — which is what lets the fixpoint
  converge — and the conjuncts of one head share it, since one rule head is one
  digest and one existential index."
  [kb rule raw bindings free]
  (ensure-skolem-function kb)
  (let [rh       (rule-digest rule)
        args     (mapv #(res/substitute % bindings) (frontier-vars rule))
        ;; One binding around the whole fold rather than one per mint: `into` is eager, so
        ;; every mint runs inside it, and the flag says the same thing for all of them.
        subs     (binding [wiring/*defer-settle?* true]
                   (into {}
                         (map-indexed
                          (fn [idx e]
                            [e (nat/reify-or-mint-nat kb (list* skolem-function rh idx args))]))
                         (sort free)))]
    (res/substitute raw subs)))

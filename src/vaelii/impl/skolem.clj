;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.skolem
  "Head existentials: the deterministic `SkolemFn` witness a rule head `(exists ?y C)`
  fires to, reified through `vaelii.impl.nat`.  Called from two layers: the assert path
  declares `SkolemFn` when it stores such a rule, and the forward chainer mints at each
  firing.  See docs/skolem.md."
  (:require [vaelii.impl.nat :as nat]
            [vaelii.impl.nat-read :as nat-read]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.wiring :as wiring]))

(def skolem-function
  "The reifiable function every skolem constant is an application of."
  'SkolemFn)

(defn ensure-skolem-function
  "Declare `SkolemFn` a `reifiable_function` if it is not already, which also turns on
  the NAT orphan-cleanup presence check (`nat-read/any-reifiable-functions?`).  Idempotent; asserted
  without chaining."
  [kb]
  (when-not (nat-read/reifiable-function? kb skolem-function)
    (wiring/assert-sentence kb (list 'reifiable_function skolem-function)
                            nat-read/universal-context
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
  "A rule's consequent variables that its antecedents bind, sorted so the skolem's
  argument list is stable.  A post-join literal's output is excluded: it is computed per
  placement, after the mint, so it would substitute to itself and put a variable in the
  NAT (`chain/derive-conclusion` subtracts the same set)."
  [rule]
  (let [vars  sx/form-vars
        post  (into #{} (mapcat sx/deferred-output-vars) (:post-join rule))
        avars (into #{} (mapcat vars) (:antecedents rule))
        cvars (distinct (vars (:consequent rule)))]
    (vec (sort (remove post (filter avars cvars))))))

(defn- rule-digest
  "The hex SHA-1 of the rule's canonical antecedents, consequent and context: the
  content key a skolem constant carries in place of a handle, which would put assertion
  order into stored `natFormula` content."
  [rule]
  ;; print vars bound off: the digest lands in stored `natFormula` content, and an
  ;; ambient *print-length*/*print-level* (a REPL's, typically) would elide the rule
  ;; out of its own identity — two rules digesting alike merge their witnesses
  (let [s (binding [*print-length* nil *print-level* nil *print-meta* false]
            (pr-str [(:antecedents rule) (:consequent rule) (:context rule)]))
        d (.digest (java.security.MessageDigest/getInstance "SHA-1")
                   (.getBytes ^String s "UTF-8"))]
    (apply str (map #(format "%02x" %) d))))

(defn witnesses
  "`[[var expr]…]`, `free` sorted: the NAT `(SkolemFn <rule-digest> i <frontier-values…>)`
  the i-th still-unbound (existential) variable of a rule's conclusion names under
  `bindings`, before anything is minted."
  [rule bindings free]
  (let [rh   (rule-digest rule)
        args (mapv #(res/substitute % bindings) (frontier-vars rule))]
    (into [] (map-indexed (fn [idx e] [e (list* skolem-function rh idx args)])) (sort free))))

(defn skolemize-conclusion
  "Mint the skolem constant of each of `witnesses` (`witnesses` above) and return the
  rule's substituted conclusion `raw` with each variable replaced by its constant."
  [kb raw witnesses]
  (ensure-skolem-function kb)
  ;; One binding around the whole fold rather than one per mint: `into` is eager, so
  ;; every mint runs inside it.
  (let [subs (binding [wiring/*defer-settle?* true]
               (into {} (map (fn [[v e]] [v (nat/reify-or-mint-nat kb e)])) witnesses))]
    (res/substitute raw subs)))

;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.llm.correct
  "Type-level corrections: a proposal that says the right thing in the wrong shape.

  Every model asked about a *type* writes facts **about the type symbol** —
  `(eats penguin fish)`, `(mortal penguin)` — where the KB's idiom quantifies over the
  type's instances.  Measured across eight models on the shipped schema this is the
  dominant remaining error class, and nothing else catches it: `naming/problems` passes
  it (the names are all well-formed), `wff` passes it, the argIsa constraints pass it
  (open-world — a type symbol carries no type membership, and an untyped argument cannot
  violate), and it stores.  The claim is *usually right*; only its shape is wrong.

  So this rewrites rather than rejects.  Each correction carries the sentence it came
  from, the one to store instead, the **alternatives** where more than one shape is
  defensible, and why — because for the most common case the choice between shapes is a
  semantic judgement no engine can make for the author:

  | claim | shape | inference | exception possible? |
  |---|---|---|---|
  | definitional — what a penguin *is* | `(genl penguin mortal)` | free, off the cached closure | no |
  | defeasible — what a penguin *usually does* | `(set/defaultRule (implies (penguin ?x) (mortal ?x)))` | forward chaining | yes, via `exceptWhen` |

  **The defeasible shape is the default, on asymmetric risk.**  A defeasible claim that
  should have been definitional costs only the chaining it did not need.  A definitional
  claim that should have been defeasible cannot take an `exceptWhen` at all — a `genl`
  edge admits no exception — so the only repair is retracting it and rebuilding the
  closure.  Guessing wrong in that direction is the expensive one, so it is not guessed.

  Nothing here mutates: a correction is a proposal about a proposal.  What to do with it
  — show both shapes, show only the rewrite, let the author edit it — is the caller's."
  (:require [clojure.string :as str]
            [vaelii.core :as v]
            [vaelii.impl.llm.inventory :as inv]
            [vaelii.impl.sentex :as sx]))

;; ---- what the sentence is about -------------------------------------------

(defn- type-arg?
  "Is `a` a symbol the KB treats as a **type** — something whose instances a claim
  could be about?  Asked of the KB (`inventory/term-kind`) and never of the spelling: a
  bare lowercase word satisfies the predicate and the type convention alike, so `dog`
  and `flies` are decided by their genl edges and argIsa constraints, not by their
  letters."
  [kb a]
  (and (symbol? a)
       (not (sx/variable? a))
       (= :type (inv/term-kind kb a))))

(defn- instance-position?
  "Does position `n` of `pred` want an *instance* rather than a type?  True when an
  `argIsa` constrains it: `(argIsa eats 1 animal)` asks for an animal, and a type is not
  an animal — `genl penguin animal` holds while `isa? penguin animal` does not, which is
  exactly the distinction the constraint is about.  A position with no constraint is left
  alone, since an unconstrained argument may legitimately be a type (`(comment penguin
  \"…\")`, `(disjoint penguin fish)`)."
  [kb pred n]
  (boolean (seq (v/sentexes-matching kb (list 'argIsa pred n '?t) '?ctx))))

(defn- arg-type
  "The type `argIsa` constrains position `n` of `pred` to, or nil when unconstrained."
  [kb pred n]
  (some-> (first (v/sentexes-matching kb (list 'argIsa pred n '?t) '?ctx)) :sentence (nth 3)))

(defn- structural?
  "Is this a predicate whose arguments are *supposed* to be types?  `genl`, `disjoint`,
  `argIsa`, `comment` and the rest of the vocabulary head talk about types by design, so
  a type in their arguments is correct and not a mistake to rewrite."
  [pred]
  (inv/structural-functor? pred))

;; ---- the corrections -----------------------------------------------------

(defn- defeasible-rule
  "`(set/defaultRule (implies (T ?x) <head>))` — the defeasible reading of a one-place
  claim about a type's instances, `head` being what is said of `?x`: `(P ?x)`, or its
  negation.  Written with `?x` rather than the canonical `?var0`: the author reads this,
  and the engine renumbers on store."
  [t head]
  (list 'set/defaultRule (list 'implies (list t '?x) head)))

(defn- unary-on-type
  "`(P T)` — and `(not (P T))` — where T is a type and P is one-place: \"every T is P\",
  written as a fact about the type symbol.  Two defensible shapes; the defeasible one
  leads.

  The negated form matters as much as the plain one, because it is how the shipped schema
  states its own worked example: `(implies (penguin ?x) (not (flies ?x)))`.  A model
  writing `(not (flies penguin))` has the right claim in the wrong shape, exactly like
  `(mortal penguin)`, so it is corrected the same way rather than passed through."
  [kb sentence]
  (let [negated? (and (= 2 (count sentence)) (= 'not (first sentence))
                      (seq? (second sentence)))
        body     (if negated? (second sentence) sentence)]
    (when (= 2 (count body))
      (let [[p t] body]
        (when (and (symbol? p)
                   (not (structural? p))
                   (type-arg? kb t))
          (let [head (if negated? (list 'not (list p '?x)) (list p '?x))]
            {:from sentence
             :to (defeasible-rule t head)
             ;; a *negative* claim has no genl reading — genl says what a thing is, and
             ;; there is no edge meaning "no penguin flies" — so the alternative is
             ;; offered only for the positive form
             :alternatives (when-not negated? [(list 'genl t p)])
             :rule :unary-on-type
             :confidence :high
             :why (str (pr-str sentence) " states " p " of the type symbol " t
                       " rather than of its instances. As a defeasible default, every"
                       " instance of " t (if negated? " does not satisfy " " satisfies ")
                       p (when-not negated?
                           (str "; as a definitional claim it is the genl edge (" t
                                " is a kind of " p "), which admits no exception")) ".")}))))))

(defn- type-lift-name
  "The type-level spelling of a relation — `eats` ⇒ `eatsType`.  A relation between
  *types* is a different relation from the one between individuals, so it gets its own
  name rather than overloading the instance-level one."
  [pred]
  (symbol (str (name pred) "Type")))

(defn- relation-on-types
  "`(R T1 T2)` where R's argIsa wants instances and an argument is a type — \"every T1
  Rs a T2\".  The lift `(RTypeName T1 T2)` leads because it keeps the claim in one
  ground sentence; the quantified rule is the alternative that spells the meaning out.

  The lift is **inert on its own**: nothing connects `(eatsType penguin fish)` to
  `(eats Pingu SomeFish)` until a rule says how, and which rule depends on the reading
  (every penguin eats *some* fish, or *every* fish).  That is stated in `:why` rather
  than decided here."
  [kb sentence]
  (let [[r & args] sentence
        n (count args)]
    (when (and (>= n 2)
               (symbol? r)
               (not (structural? r))
               (some (fn [[i a]] (and (type-arg? kb a) (instance-position? kb r i)))
                     (map-indexed (fn [i a] [(inc i) a]) args)))
      (let [[t1 t2] args
            lift    (type-lift-name r)
            types   (filter #(type-arg? kb %) args)
            inverse (v/inverse-of kb r)
            ;; The direction is ambiguous exactly when both positions want the same
            ;; type: `partOf : physical_object x physical_object` gives no signal about
            ;; which argument is the whole, and `(partOf penguin beak)` reads as "a
            ;; penguin is part of a beak" — backwards.  Swapping the arguments of the
            ;; lift says what the author meant without coining a second name, so it is
            ;; offered rather than assumed.  (`hasPartType penguin beak` is that same
            ;; claim read the other way; declaring `(inverse partOf hasPart)` is what
            ;; would let the lift be named in that direction instead.)
            same-type? (and (= 2 n) (= (arg-type kb r 1) (arg-type kb r 2)))]
        {:from sentence
         :to (apply list lift args)
         :alternatives (vec (concat
                             (when same-type? [(apply list lift (reverse args))])
                             (when inverse [(apply list (type-lift-name inverse)
                                                   (reverse args))])
                             (when (= 2 n)
                               [(list 'implies (list t1 '?x)
                                      (list 'exists '(?y) (list 'and (list t2 '?y)
                                                                (list r '?x '?y))))])))
         :rule :relation-on-types
         :confidence (if same-type? :low :medium)
         :why (str r " relates individuals (its argIsa constrains an argument to a"
                   " type's instances), but "
                   (str/join ", " types) (if (= 1 (count types)) " names a type. "
                                             " name types. ") lift
                   " is the type-level relation."
                   " It stores as one ground sentence but infers nothing on its own:"
                   " connecting it to " r " needs a rule, and which rule depends on"
                   " whether every " t1 " " r " *some* " (or t2 "…") " or *every* one."
                   (when same-type?
                     (str " Both positions of " r " want the same type, so the argument"
                          " order carries no constraint and may be reversed — check the"
                          " direction.")))}))))

(defn- arity-surplus
  "A sentence with more arguments than the predicate declares.  Only auto-fixable when
  the surplus is an exact **duplicate** — `(partOf penguin beak beak)` is a stutter, and
  dropping the repeat is the one repair that needs no guess about intent.  Otherwise it
  is reported with no `:to`, since choosing which argument to drop is choosing what the
  author meant."
  [kb sentence]
  (let [[p & args] sentence
        declared (get (inv/declared-arities kb) p)]
    (when (and declared (symbol? p) (> (count args) declared))
      (let [deduped (vec (distinct args))]
        (cond-> {:from sentence
                 :rule :arity-surplus
                 :confidence (if (= declared (count deduped)) :high :low)
                 :why (str p " is declared with " declared " argument"
                           (when (not= 1 declared) "s") " but has " (count args)
                           (if (= declared (count deduped))
                             " — the surplus is a repeated argument."
                             " — which argument is surplus is not inferable."))}
          (= declared (count deduped)) (assoc :to (apply list p deduped)))))))

(def ^:private passes
  "Ordered: each pass sees what the ones before it left.  Arity is checked before the
  type-level rewrites, since rewriting a malformed sentence would carry the malformation
  into the rewrite — and a stutter repaired into a well-formed sentence *about type
  symbols* is still the error this namespace exists for, so the repair is handed on
  rather than returned."
  [arity-surplus unary-on-type relation-on-types])

(def ^:private confidence-order {:low 0 :medium 1 :high 2})

(defn- weakest [a b]
  (if (and a b) (if (< (confidence-order a 0) (confidence-order b 0)) a b) (or a b)))

(defn correction
  "The correction for one sentence, or nil when nothing here applies.

  Passes **compose**: one that yields a `:to` hands it to the passes after it, so a
  sentence that is malformed *and* states a relation of type symbols is repaired in
  both respects instead of only the first.  The result keeps the original `:from`,
  joins every `:why`, names the chain in `:rules`, and carries the **weakest**
  confidence in it — a chain is no surer than its least sure link.

  A pass that claims a sentence without a `:to` ends the chain and drops the repair
  accumulated so far: a partial fix whose result the engine would still refuse is
  worse than no fix, and the joined `:why` still says everything found."
  [kb sentence]
  (when (and (seq? sentence) (seq sentence))
    (loop [[f & more] passes
           acc        nil
           cur        sentence]
      (if (nil? f)
        acc
        (if-let [c (f kb cur)]
          (let [c (assoc c
                         :from       sentence
                         :why        (str/join " " (remove str/blank? [(:why acc) (:why c)]))
                         :rules      (conj (:rules acc []) (:rule c))
                         :confidence (weakest (:confidence acc) (:confidence c)))]
            (if (:to c) (recur more c (:to c)) c))
          (recur more acc cur))))))

(defn corrections
  "Corrections for a batch of `[sentence context]` entries — `{:corrections [...]
  :unchanged [...]}`, each correction carrying `:index` and `:context` so a caller can
  point at the line it came from.

  Read-only: nothing is stored, and a corrected sentence is *not* re-checked here, so a
  caller that intends to store one should still run it through `v/check`."
  [kb entries]
  (reduce
   (fn [acc [i [sentence context]]]
     (if-let [c (correction kb sentence)]
       (update acc :corrections conj (assoc c :index i :context context))
       (update acc :unchanged conj {:index i :sentence sentence :context context})))
   {:corrections [] :unchanged []}
   (map-indexed vector entries)))

(defn apply-correction
  "The `[sentence context]` entry a correction becomes — its `:to`, or the `:alternatives`
  entry at `alt`.  Returns nil for a correction with no `:to` (one that only reports),
  so a caller cannot silently store the sentence it was warning about."
  ([c] (apply-correction c nil))
  ([c alt]
   (when-let [s (if alt (nth (:alternatives c) alt nil) (:to c))]
     [s (:context c)])))

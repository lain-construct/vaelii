;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.llm.correct
  "Type-level corrections: a proposal that says the right thing in the wrong shape.

  Every model asked about a *type* writes facts **about the type symbol** —
  `(eats penguin fish)`, `(mortal penguin)` — where the KB's idiom quantifies over the
  type's instances.  Measured across eight models on the shipped schema this is the
  dominant remaining error class, and nothing else catches it: `naming/problems` passes
  it (the names are all well-formed), `wff` passes it, the arg constraints pass it
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
  and `flies` are decided by their genl edges and arg constraints, not by their
  letters."
  [kb a]
  (and (symbol? a)
       (not (sx/variable? a))
       (= :type (inv/term-kind kb a))))

(defn- instance-position?
  "Does position `n` of `pred` want an *instance* rather than a type?  True when an
  `arg` constrains it to something **narrower than the root**: `(arg eats 1 animal)`
  asks for an animal, and a type is not an animal — `genl penguin animal` holds while
  `isa? penguin animal` does not, which is exactly the distinction the constraint is about.

  A position with no constraint is left alone, since an unconstrained argument may
  legitimately be a type.  So is one constrained to `thing`, and for the same reason: the
  root is what every term reaches, so a constraint on it separates no term from any other
  and is evidence of nothing.  `comment` is the case that needs this — its first argument
  is any term at all, an individual or a type or a predicate, and `thing` is the honest
  declaration for it, so a type there is correct and rewriting `(comment penguin \"…\")`
  would be the bug.

  A position holding a **kind** is a different matter and is not this test's business:
  it is declared with `genlArg`, which this never reads.  That is why `(arg eats 1
  animal)` passes — `animal` sits at `arg`'s third position, declared `(genlArg arg
  3 thing)` — rather than because the root is being ignored there."
  [kb pred n]
  (boolean (seq (for [sx (v/sentexes-matching kb (list 'arg pred n '?t) '?ctx)
                      :when (not= 'thing (nth (:sentence sx) 3))]
                  sx))))

(defn- arg-type
  "The type `arg` constrains position `n` of `pred` to — the **narrowest** one, or nil
  when unconstrained.

  Two contexts each declaring one position is the usual shape, and `sentexes-matching`
  promises the set and not an order, so which declaration answers has to be a content
  choice: `same-type?` reads this to decide whether the reversed argument order is offered
  at all and whether the card reads `:low` or `:medium`, and neither may turn on the order
  the index happened to hand back.  `inventory/specificity` is that choice — most specific
  first, the type name breaking a tie — and it is the ranking the vocabulary card's own
  signatures use, so a position reads the same in both places.  Narrowest is also the
  honest reading of two constraints: a term must satisfy both to stand there."
  [kb pred n]
  (first (sort-by (partial inv/specificity kb)
                  (for [{:keys [sentence]} (v/sentexes-matching kb (list 'arg pred n '?t) '?ctx)]
                    (nth sentence 3)))))

(defn- structural?
  "Is this **frame** rather than vocabulary — a connective or meta-form the engine
  interprets (`implies`, `and`, `not`, `ist`, …)?  `inventory/structural-functors` is the
  roster, and it holds the connectives only.

  The vocabulary head is *not* on it and does not need to be.  `genl` and `disjoint` take
  types by declaration — they are `typeRelationPredicate`s constrained with `genlArg`,
  which `instance-position?` never reads — and `comment` takes anything, which is what its
  `thing` constraint says.  Each is left alone by the declaration it carries rather than by
  being named here, so there is one place to look when one of them is rewritten in error."
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
  "`(R T1 T2)` where R's arg wants instances and an argument is a type — \"every T1
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
         :why (str r " relates individuals (its arg constrains an argument to a"
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

(ns vaelii-bridge.utils
  "Thin wrappers over vaelii.core for the Lacuna integration layer.
   Promotes to vaelii proper when stable."
  (:require [vaelii.core :as v]))

(defn first-if-singleton
  "Returns the first element if coll has exactly one item, otherwise nil."
  [coll]
  (let [s (seq coll)]
    (when (and s (nil? (next s)))
      (first s))))

(defn sentex-matching
  "Returns the unique sentex matching sentence in context, or nil.
   Nil when zero or more than one match — ambiguity is not a match."
  [kb sentence context]
  (first-if-singleton (v/sentexes-matching kb sentence context)))

(defn- replace-arg-isa!
  "Retract (argIsa pred position old-type) and assert (argIsa pred position new-type).
   Throws if the expected old axiom is absent — fail loud if the starter drifts."
  [kb pred position old-type new-type context]
  (let [sentence (list 'argIsa pred position old-type)
        h (v/handle-of kb sentence context)]
    (when-not h
      (throw (ex-info (str "Bridge migration precondition failed: expected "
                           (pr-str sentence) " in " context " but not found. "
                           "Starter ontology may have changed.")
                      {:type :bridge-precondition-failed
                       :expected sentence
                       :context context})))
    (v/retract! kb h)
    (v/assert kb (list 'argIsa pred position new-type) context)))

(defn- retract-exact!
  "Retract the exact sentex. Throws if not found — fail loud on starter drift."
  [kb sentence context]
  (let [h (v/handle-of kb sentence context)]
    (when-not h
      (throw (ex-info (str "Bridge migration precondition failed: expected "
                           (pr-str sentence) " in " context)
                      {:type :bridge-precondition-failed
                       :expected sentence :context context})))
    (v/retract! kb h)))

(defn fix-starter-ontology!
  "Corrections to the shipped starter ontology for the Lacuna bridge.
   Call after loading the starter KB.

   1. Retract marriedTo decontextualization (existing).
   2. Migrate biological 'person' to 'human': retract the mammal chain,
      introduce 'human' as the biological type, broaden 'person' to include
      constructs. Social preds' argIsa person auto-widen."
  [kb]
  ;; 1. retract marriedTo decontextualization
  (when-let [h (v/handle-of kb '(decontextualizedPredicate marriedTo) 'CxSociety)]
    (v/retract! kb h))

  ;; 2. migrate person → human for biological chain
  ;; retract the biological definition (conditional — upstream v0.11.0+ already did this)
  (when-let [h (v/handle-of kb '(genl person mammal) 'CxOrganism)]
    (v/retract! kb h))
  (when-let [h (v/handle-of kb '(comment person "A human being — a mammal that is also a social and rational agent.") 'CxOrganism)]
    (v/retract! kb h))

  ;; establish human as the biological type
  (v/assert kb '(unaryPredicate human) 'CxCore)
  (v/assert kb '(genl human mammal) 'CxOrganism)
  (v/assert kb '(comment human "A human being — a mammal that is also a social and rational agent.") 'CxOrganism)

  ;; broaden person to include constructs (idempotent)
  (v/assert kb '(comment person "An entity with social agency.") 'CxOrganism)
  (v/assert kb '(genl human person) 'CxUniverse)
  (v/assert kb '(genl construct person) 'CxUniverse)
  (v/assert kb '(disjoint human construct) 'CxUniverse)

  ;; widen siblingOf from animal to person — CxLife ships (arg siblingOf 1 animal)
  ;; which rejects constructs; the bridge uses siblingOf for chosen kinship too
  (when-let [h (v/handle-of kb '(arg siblingOf 1 animal) 'CxLife)]
    (v/retract! kb h))
  (when-let [h (v/handle-of kb '(arg siblingOf 2 animal) 'CxLife)]
    (v/retract! kb h))
  (v/assert kb '(arg siblingOf 1 person) 'CxSociety)
  (v/assert kb '(arg siblingOf 2 person) 'CxSociety)

  ;; social preds (knows, friendOf, marriedTo, etc.) keep arg person — auto-widened
  ;; parentOf keeps arg animal — unchanged
  )

(defn- check-arg-types
  "Assertive-mode argIsa check: reject if arg has a type disjoint with the
   required type. Vaelii's disjoint is closed under genl, so one ask suffices
   per arg type — no manual genl walking needed."
  [kb pred args context]
  (vec
    (for [[i arg] (map-indexed #(vector (inc %1) %2) args)
          :let [constraints (v/query kb (list 'argIsa pred i '?type) context
                                     {:max-depth 0})]
          :when (seq constraints)
          :let [required-type (get (first constraints) '?type)]
          :when (not (v/ask? kb (list required-type arg) context))
          :let [arg-types (map #(get % '?type)
                               (v/query kb (list '?type arg) context
                                        {:max-depth 0}))]
          :when (some #(v/ask? kb (list 'disjoint % required-type) context)
                      arg-types)]
      {:type :arg-type-bridge
       :message (str "arg " i " of (" pred " ...) — " arg " has a type disjoint with "
                     required-type ".")
       :predicate pred :position i :arg arg :required-type required-type
       :sentence (cons pred args)})))

(defn check-guarded
  "Extended check: runs v/check plus bridge-specific guards.
   Returns a vector of problem maps — empty when the sentence is admissible.
   Stores nothing.

   Bridge guards (beyond what v/check catches):
   - :undeclared-predicate — predicate not declared via (predicate ?p)
   - :not-assertible-bridge — predicate marked (notAssertible ?pred)
   - :arg-type-bridge — argIsa violation (vaelii entails instead of rejecting)"
  [kb sentence context & [opts]]
  (let [pred (when (sequential? sentence) (first sentence))
        args (when (sequential? sentence) (rest sentence))
        bridge-problems
        (cond-> []
          (and pred (not (v/ask? kb (list 'predicate pred) 'CxCore)))
          (conj {:type :undeclared-predicate
                 :message (str pred " is not a declared predicate.")
                 :predicate pred
                 :sentence sentence})

          (and pred (v/ask? kb (list 'notAssertible pred) 'CxCore))
          (conj {:type :not-assertible-bridge
                 :message (str pred " is notAssertible — derived-only.")
                 :predicate pred
                 :sentence sentence}))
        arg-problems (when (and pred (empty? bridge-problems) (seq args))
                       (check-arg-types kb pred args context))]
    (if (seq bridge-problems)
      bridge-problems
      (into (vec (v/check kb sentence context opts))
            arg-problems))))

(defn assert-guarded
  "Like v/assert, but runs check-guarded first and throws on any problem.
   Stores nothing until all checks pass."
  [kb sentence context & [opts]]
  (let [problems (check-guarded kb sentence context opts)]
    (when (seq problems)
      (let [p (first problems)]
        (throw (ex-info (str "assert-guarded rejected: " (:message p))
                        (assoc p :problems problems))))))
  (if opts
    (v/assert kb sentence context opts)
    (v/assert kb sentence context)))

;; ── defining-assertions ─────────────────────────────────────────────────────

(defn- arity-of
  "Return the declared or deduced arity of pred, or nil if unknown.
   Checks predicateTypeByArity declarations first (unaryPredicate → 1,
   binaryPredicate → 2, ternaryPredicate → 3), then falls back to
   explicit (arity pred ?n)."
  [kb pred context]
  (cond
    (v/ask? kb (list 'unaryPredicate pred) context) 1
    (v/ask? kb (list 'binaryPredicate pred) context) 2
    (v/ask? kb (list 'ternaryPredicate pred) context) 3
    :else
    (let [results (v/query kb (list 'arity pred '?n) context {:max-depth 0})]
      (when (seq results)
        (get (first results) '?n)))))

(defn- is-predicate?
  "True if sym is known to be a predicate (any arity type or explicit)."
  [kb sym context]
  (or (v/ask? kb (list 'predicate sym) context)
      (v/ask? kb (list 'unaryPredicate sym) context)
      (v/ask? kb (list 'binaryPredicate sym) context)
      (v/ask? kb (list 'ternaryPredicate sym) context)))

(defn defining-assertions
  "Check whether sym has all its required defining assertions in context.
   Returns a map:
     :sym        — the symbol checked
     :kind       — :predicate, :collection, or :unknown
     :present    — set of keywords for assertions found
     :missing    — set of keywords for assertions expected but absent
     :arity      — the deduced arity (predicates only, nil if missing)
     :details    — map of keyword → found value(s) for present assertions

   Defining assertions for all terms:
     :genl       — at least one (genl sym ?parent)
     :comment    — at least one (comment sym ?text)

   Additional for predicates:
     :arity      — deducible from type declaration or explicit
     :argIsa     — (argIsa sym pos ?type) for each arg position
     :argGenl    — (argGenl sym pos ?type) for each arg position (optional)

   argIsa and argGenl are checked per-position. A position with neither
   argIsa nor argGenl is flagged as missing :argIsa-N."
  [kb sym context]
  (let [pred?    (is-predicate? kb sym context)
        kind     (if pred? :predicate :collection)

        ;; common assertions (filter out reflexive genl — genl is reflexive in v0.7.0+)
        genls    (remove #(= sym (get % '?parent))
                         (v/query kb (list 'genl sym '?parent) context {:max-depth 0}))
        comments (v/query kb (list 'comment sym '?text) context {:max-depth 0})

        present  (cond-> #{}
                   (seq genls)    (conj :genl)
                   (seq comments) (conj :comment))
        missing  (cond-> #{}
                   (empty? genls)    (conj :genl)
                   (empty? comments) (conj :comment))
        details  (cond-> {}
                   (seq genls)    (assoc :genl (mapv #(get % '?parent) genls))
                   (seq comments) (assoc :comment (mapv #(get % '?text) comments)))

        ;; predicate-specific
        arity    (when pred? (arity-of kb sym context))
        [present missing details]
        (if-not pred?
          [present missing details]
          (let [present (if arity (conj present :arity) present)
                missing (if (nil? arity) (conj missing :arity) missing)
                details (if arity (assoc details :arity arity) details)

                ;; check argIsa/argGenl for each position
                positions (range 1 (inc (or arity 0)))]
            (reduce
              (fn [[p m d] pos]
                (let [arg-isas  (v/query kb (list 'argIsa sym pos '?type) context
                                         {:max-depth 0})
                      arg-genls (v/query kb (list 'argGenl sym pos '?type) context
                                         {:max-depth 0})
                      pos-key   (keyword (str "argIsa-" pos))]
                  (if (or (seq arg-isas) (seq arg-genls))
                    [(conj p pos-key)
                     m
                     (cond-> d
                       (seq arg-isas)  (assoc pos-key
                                              (mapv #(get % '?type) arg-isas))
                       (seq arg-genls) (assoc (keyword (str "argGenl-" pos))
                                              (mapv #(get % '?type) arg-genls)))]
                    [p (conj m pos-key) d])))
              [present missing details]
              positions)))]
    {:sym     sym
     :kind    kind
     :present present
     :missing missing
     :arity   arity
     :details details}))

(defn check-defining-assertions
  "Convenience: returns the :missing set from defining-assertions.
   Empty set means the term is fully defined."
  [kb sym context]
  (:missing (defining-assertions kb sym context)))

(defn assert-well-defined?
  "True if sym has no missing defining assertions."
  [kb sym context]
  (empty? (check-defining-assertions kb sym context)))

(ns vaelii.impl.llm.inventory
  "The KB's own vocabulary, put in front of the model — and the flag for when the model
  invents vocabulary anyway.

  **Measured failure mode.**  Asked to write type-level common sense about a term, every
  local model that writes usable s-expressions at all encodes structure into the
  *predicate name* rather than into arguments:

      (implies (penguin ?x) (lives_in_antarctica ?x))
      (implies (penguin ?x) (capable_of_swimming ?x))
      (implies (penguin ?x) (thermoregulates_via_blubber_and_feathers ?x))

  Each is admissible, novel, and useless: a one-off unary predicate joins no rule and
  matches no other sentence.  `(livesIn ?x Antarctica)` is the same claim in vocabulary
  the KB can reason with.  Swapping models does not fix it — the strongest model
  produces the *most* of it, because it produces the most output.

  **The check chain cannot catch it.**  A unary snake_case functor is a well-formed type
  name by the naming invariants, so `(has_black_and_white_feathers ?x)` passes naming,
  groundness, well-formedness, argIsa, disjointness and functionality alike — and it
  should, since coining a type is a legitimate thing to do.  So there are exactly two
  guards, and they are both here:

  1. **Prevention** — `inventory` / `render` put the *relevant available* vocabulary in
     the prompt with each predicate's arity and argument types, and the prompt tells the
     model to reuse it.  A model that can see `livesIn` with `args 1:animal 2:place`
     writes `(livesIn ?x Antarctica)`.
  2. **Detection** — `coined` reports every functor in a proposal the KB has never seen,
     with its arity and naming role, plus a reuse-versus-coin count over the proposal's
     literals.  It **reports, never rejects**: a reviewer decides, because a genuinely
     new type is how an ontology grows.

  **Selection is by relevance, bounded by tokens.**  Nothing enumerates the KB: the
  inventory is seeded from the page's term, walks its `genl` neighbourhood (supertypes
  nearest first, subtypes, siblings), and takes the predicates that neighbourhood
  *licenses* — the `argIsa`-declared ones whose argument types the term satisfies, plus
  the ones already used in facts with those terms.  Every read is pinned by a term
  (a cached closure lookup, an `argIsa` query on a fixed argument, a bounded argument-root
  walk), so the cost tracks the neighbourhood rather than the knowledge base."
  (:require [clojure.string :as str]
            [vaelii.core :as v]
            [vaelii.impl.core-context :as core-context]
            [vaelii.impl.llm.selection :as selection]))

;; ---- what counts as coined vocabulary -----------------------------------

(def structural-functors
  "The functors that are **frame, not vocabulary**: the connectives that canonicalize
  into the sentex record and the meta-forms the engine interprets.  A proposal using
  `implies` is not coining a predicate, so these are never reported — and they are named
  here rather than read from the KB so the flag works on a KB with no vocabulary loaded
  at all.  A namespaced functor (`set/defaultRule`, `do/labeling`) is excluded the same
  way, by its namespace."
  '#{implies and or not exceptWhen ist unknown thereExists sentexHandle})

(defn structural-functor?
  "Is `f` frame rather than vocabulary?"
  [f]
  (or (not (symbol? f))
      (some? (namespace f))
      (contains? structural-functors f)))

(defn literals
  "Every literal in a sentence as `[{:functor f :arity n} …]`, at any nesting depth and
  in reading order, with the structural frame dropped.

  A rule contributes its antecedents and its consequent; a nested compound argument
  contributes itself, since a functor in argument position is vocabulary too.  Duplicates
  are kept — the count of literals is what a reuse-versus-coin ratio is taken over."
  [sentence]
  (let [acc (volatile! [])
        walk (fn walk [form]
               (when (sequential? form)
                 (let [f (first form)]
                   (when-not (structural-functor? f)
                     (vswap! acc conj {:functor f :arity (dec (count form))})))
                 (run! walk (rest form))))]
    (walk sentence)
    @acc))

(defn- rooted?
  "Is `term` reachable from one of the index's O(1) secondary roots — used as a fact's
  functor, or standing in one of the first three argument positions?  The cheap half of
  `known-term?`: a predicate that is *declared* and never used still sits at argument 1
  of its own `(argIsa P …)` / `(arity P …)` / `(binaryPredicate P)` sentexes, and a type
  sits at either end of a `genl` edge, so this answers yes for almost everything the KB
  knows without touching the term roster."
  [kb term]
  (or (pos? (v/count-with-functor kb term))
      (some #(pos? (v/count-with-arg kb % term)) [1 2 3])))

(defn unknown-terms
  "The `candidates` the KB has **never seen** — no fact, no rule, no declaration, at any
  nesting depth.

  The O(1) roots answer first; only what they cannot resolve falls through to the term
  roster (`vaelii.core/terms`), which is the exact answer and is read **once** for the
  whole candidate set.  So a proposal that reuses vocabulary throughout costs a handful
  of set-size reads, and the roster pass is paid only when something really is new —
  which is the case worth paying for."
  [kb candidates]
  (let [maybe (remove #(rooted? kb %) (distinct candidates))]
    (if (empty? maybe)
      #{}
      (let [vocab (set (v/terms kb))]
        (into #{} (remove vocab) maybe)))))

(defn coined
  "The vocabulary an `edit` batch introduces, as
  `{:coined [{:predicate :arity :role :in :index} …] :vocabulary {…}}`.

  One entry per *literal* whose functor the KB has never seen, in batch order:

    :predicate  the functor
    :arity      how many arguments the literal gave it — the reviewer's first question,
                since `(capable_of_swimming ?x)` and `(capableOf ?x Swimming)` differ in
                exactly that
    :role       `:type` (snake_case, a one-place property) or `:predicate` (camelCase),
                by the naming invariants — a coined *type* and a coined *relation* are
                different judgements
    :in :index  where in the batch it came from, so a caller can point at the entry

  `:vocabulary` counts the whole proposal:
  `{:literals :reused :coined :coined-types :coined-relations}` — which says at a glance
  whether the proposal is conservative (all reuse) or inventive (mostly new names), the
  one number a reviewer wants before reading anything.

  Nothing here rejects.  `:remove` entries are ignored: retracting cannot coin."
  [kb batch]
  (let [found (vec (for [[i entry] (map-indexed vector (:add batch))
                         :let [[sentence] (when (sequential? entry) entry)]
                         lit (literals sentence)]
                     (assoc lit :in :add :index i)))
        new?  (unknown-terms kb (map :functor found))
        cs    (vec (for [{:keys [functor arity in index]} found
                         :when (contains? new? functor)]
                     {:predicate functor
                      :arity arity
                      :role (v/term-role functor)
                      :in in
                      :index index}))]
    {:coined cs
     :vocabulary {:literals (count found)
                  :reused (- (count found) (count cs))
                  :coined (count cs)
                  :coined-types (count (filter #(= 1 (:arity %)) cs))
                  :coined-relations (count (remove #(= 1 (:arity %)) cs))}}))

;; ---- the neighbourhood the inventory is drawn from -----------------------

(defn specificity
  "How specific a type is, as the size of its own `genl` up-closure: `penguin` (5) sits
  under `bird` (4) under `animal` (3).  Sorting **descending** puts the nearest, most
  specific type first — the order relevance runs in — and the name breaks ties, so the
  order is a function of the taxonomy and never of arrival.

  Public because `vaelii.impl.llm.text` builds a card from a document's resolved terms
  rather than from one page term, and a second copy of this ordering would drift."
  [kb t]
  [(- (count (v/genls kb t))) (str t)])

(def predicate-type-arities
  "The predicate meta-ontology's arity declarations: the type a predicate is a member of,
  and the arity that membership states."
  {'unaryPredicate 1 'binaryPredicate 2 'ternaryPredicate 3})

(defn declared-arities
  "`{predicate -> arity}` for every predicate the KB **declares** — its `(arity P N)`
  sentexes and its `unaryPredicate` / `binaryPredicate` / `ternaryPredicate` memberships,
  which derive each other, so either spelling is enough.

  **Arity is never inferred from `argIsa`.**  `argIsa` constrains an argument to a *type*
  and is deliberately partial: a second argument may be unconstrained by design (you may
  `likes` anything) or not a type at all (a year, an integer).  Measured on the shipped
  schema, the highest `argIsa` position disagrees with the declared arity for 8 of the 42
  constrained relations — `likes`, `birthYearOf` and `arity` all read as unary — so an
  inventory built that way would print `likes/1` and *cause* the arity errors it exists to
  prevent.  A predicate the KB never declared gets no arity rather than a guessed one.

  Cost is the size of the **vocabulary**: four extent reads, none of them over facts."
  [kb]
  (merge (into {} (for [[pred n] predicate-type-arities
                        {:keys [sentence]} (v/sentexes-matching kb (list pred '?p) '?ctx)]
                    [(nth sentence 1) n]))
         (into {} (for [{:keys [sentence]} (v/sentexes-matching kb '(arity ?p ?n) '?ctx)
                        :when (number? (nth sentence 2))]
                    [(nth sentence 1) (nth sentence 2)]))))

(defn- observed-arity
  "The arity of a stored fact with this functor, or nil.  Ground truth rather than
  inference — it is a sentence the KB holds — and the one fallback for a predicate used
  without ever being declared.  The extent is walked lazily, so this is one record fetch."
  [kb p]
  (when-let [sx (first (v/sentexes-with-functor kb p))]
    (let [s (v/readable-sentence sx)]
      (when (and (sequential? s) (= p (first s))) (dec (count s))))))

(defn term-kind
  "How a page about `term` should treat it — `:type`, `:predicate`, `:individual`,
  `:context`, or nil.

  The naming invariants leave one genuine ambiguity, and say so: a single lowercase word
  (`dog`, `flies`) satisfies both the predicate and the type spelling, and role is decided
  by position and arity rather than by the symbol.  So the **KB** decides — a term with
  `genl` edges is a type, one with `argIsa` constraints is a relation, and a bare unary is
  a type.  Which way it goes decides what the inventory is drawn from, so guessing off the
  spelling alone would give a page about `dog` the vocabulary of a relation."
  [kb term]
  (let [role (v/term-role term)]
    (if-not (#{:predicate :type} role)
      role
      (cond
        (or (> (count (v/genls kb term)) 1) (> (count (v/specs kb term)) 1)) :type
        (seq (v/sentexes-matching kb (list 'argIsa term '?n '?t) '?ctx)) :predicate
        (seq (v/sentexes-matching kb (list 'unaryPredicate term) '?ctx)) :type
        :else :predicate))))

(defn seed-types
  "The types the inventory is drawn around, most specific first, for a page about
  `term` — read off the term's own role:

    a type        the type itself, its supertypes, its subtypes, and its siblings
                  (the other subtypes of its nearest supertype)
    an individual the types it is asserted to have, and their supertypes
    a predicate   the types its `argIsa` constraints name, so what it can be said *of*
                  is on the card

  `opts`: `:max-genls` (8), `:max-specs` (12), `:max-siblings` (12).  Each closure is a
  cached taxonomy read, so the whole walk is a handful of set lookups."
  ([kb term] (seed-types kb term {}))
  ([kb term {:keys [max-genls max-specs max-siblings]
             :or {max-genls 8 max-specs 12 max-siblings 12}}]
   (let [order #(sort-by (partial specificity kb) %)
         role  (term-kind kb term)]
     (case role
       :type
       (let [up      (order (disj (set (v/genls kb term)) term))
             down    (order (disj (set (v/specs kb term)) term))
             parent  (first up)
             sibs    (when parent
                       (order (remove (set (v/specs kb term))
                                      (disj (set (v/specs kb parent)) parent))))]
         {:term term :role role
          :genls (vec (take max-genls up))
          :specs (vec (take max-specs down))
          :siblings (vec (take max-siblings sibs))})

       :individual
       (let [ts (order (v/types-of kb term))
             up (order (disj (set (mapcat #(v/genls kb %) ts)) term))]
         {:term term :role role
          :types (vec (take max-specs ts))
          :genls (vec (take max-genls (remove (set ts) up)))})

       :predicate
       (let [args (vec (for [{:keys [sentence]} (v/sentexes-matching kb (list 'argIsa term '?n '?t) '?ctx)]
                         (nth sentence 3)))
             up   (order (disj (set (v/genls kb term)) term))
             down (order (disj (set (v/specs kb term)) term))]
         {:term term :role role
          :arg-types (vec (distinct args))
          :genls (vec (take max-genls up))
          :specs (vec (take max-specs down))})

       {:term term :role role}))))

(defn neighbourhood-types
  "The seed's types as one relevance-ordered vector — the term first, then supertypes,
  its own subtypes, its siblings.  This is the order predicates inherit their relevance
  from, so a predicate licensed by the term itself outranks one licensed by `thing`."
  [seed]
  (let [{:keys [term role]} seed]
    (vec (distinct (concat (when (= :type role) [term])
                           (:types seed)
                           (:arg-types seed)
                           (:genls seed)
                           (:specs seed)
                           (:siblings seed))))))

;; ---- structural vocabulary vs domain vocabulary -------------------------

(def head-context
  "The spindle head — the context the engine's own vocabulary is documented in.  A term the
  head documents is **structural**: it is part of how you say a thing, not part of what
  there is to say."
  'CoreContext)

(def structural-predicates
  "The structural predicates a type-level claim actually needs, and the only ones offered —
  **in the order they matter**, so a token cap cuts the least useful first.

  The head documents far more than this — the evaluables, the quantity apparatus
  (`conversionFactor`, `quantityGreaterThanOrEqual`, `termOfUnit`), the context plumbing.
  Handing a model asked about penguins the whole vocabulary head is irrelevant at best and an
  invitation to misuse something it half-recognizes at worst, so the structural block is an
  allowlist rather than a dump.  The connectives (`implies`, `and`, `not`, `exceptWhen`) are
  not here because they are *frame*: the prompt states the sentence shapes directly."
  '[genl disjoint comment argIsa])

(defn structural-terms
  "Every term the vocabulary head documents, from its `comment` sentexes in that context —
  one pinned read, and the exact answer, since a term's documentation is stored where the
  term is defined."
  [kb]
  (into #{} (for [{:keys [sentence]} (v/sentexes-matching kb '(comment ?t ?text) head-context)]
              (nth sentence 1))))

;; ---- the predicates that neighbourhood licenses -------------------------

(defn- argisa-predicates
  "The predicates an `argIsa` declares to take a `t` somewhere — `(argIsa P n t)` read as
  inference rather than as constraint.  The query pins `argIsa` and the *type*, so it is
  one narrow index read whatever the KB's size."
  [kb t]
  (distinct (for [{:keys [sentence]} (v/sentexes-matching kb (list 'argIsa '?p '?n t) '?ctx)]
              (nth sentence 1))))

(defn- used-with
  "The functors of stored facts holding `t` in one of the first three argument positions
  — the predicates the KB has actually said something with about this term, including the
  ones no `argIsa` constrains.  Walked lazily and capped, so a term sitting in a million
  facts costs `max-scan` record reads, not a million."
  [kb t max-scan]
  (distinct (for [pos [1 2 3]
                  sx (take max-scan (v/sentexes-with-arg kb pos t))
                  :let [f (first (v/readable-sentence sx))]
                  :when (and (symbol? f) (not (structural-functor? f)))]
              f)))

(defn- props-of
  "The algebraic metadata a predicate carries, as keyword names — what makes reusing it
  worth more than coining a synonym, since a `transitive` predicate reasons on its own."
  [kb p]
  (vec (for [k [:transitive :symmetric :reflexive :functional :decontextualized]
             :when (v/has-prop? kb k p)]
         (name k))))

(defn predicate-shape
  "One predicate's inventory entry:
  `{:predicate :arity :args [[position type] …] :props […] :inverse :doc}`.

  `:args` is every `argIsa` constraint on it, sorted by position, and `:arity` comes from
  the KB's declarations — never from the constraints.  Together they are the part that stops
  the model folding an argument into the predicate's name: seeing
  `locatedIn/2 : physical_object × physical_object` makes reuse the obvious move, where a
  bare `locatedIn` leaves the model guessing whether there is anywhere to put `Antarctica`."
  [kb p arity]
  {:predicate p
   :arity (or arity (observed-arity kb p))
   :args (vec (sort-by first
                       (for [{:keys [sentence]} (v/sentexes-matching kb (list 'argIsa p '?n '?t) '?ctx)]
                         [(nth sentence 2) (nth sentence 3)])))
   :props (props-of kb p)
   :inverse (v/inverse-of kb p)
   :doc (first (core-context/comment-of kb p))})

(defn inventory
  "The vocabulary a page about `term` should be written in, as data:

      {:term       the page's term
       :seed       what `seed-types` found — the genl neighbourhood
       :types      [{:type :parent :doc} …]                    the type names to reuse
       :relations  [{:predicate :arity :args :props :inverse :doc :tier} …]  domain vocabulary
       :structural [{:predicate :arity :args :doc} …]           how to state a type-level claim
       :dropped    {:relations n :types n}}

  **Two blocks, because they are two different things.**  The domain relations are what the
  reader's knowledge is *made of*; the structural handful is how a claim about a kind is
  *stated* (`genl`, `disjoint`, `comment`, `argIsa`).  A term the vocabulary head documents
  is structural and is left out of the domain block unless the page is about that band.

  **The source is the KB's declarations, not its facts.**  Types come from `vaelii.core/types`
  and relations from the `unaryPredicate` / `binaryPredicate` / `ternaryPredicate`
  memberships, because a schema-only KB has no facts: enumerating functors that actually
  appear in fact position on the shipped schema yields 20 names, every one of them an engine
  meta-predicate and not one of them a domain relation.  `argIsa` then supplies argument
  *types* for the 42 relations that declare them.

  Ordering is by **relevance tier** — predicates already used in facts with the page's term,
  then those an `argIsa` licenses for the term itself, then for each supertype in turn
  (nearest first), then subtypes and siblings, then everything else declared, alphabetically.
  On a vocabulary the size of the shipped schema everything fits and the order is cosmetic;
  ordering is what makes the *cut* meaningful when it does not.

  `opts`: `:max-relations` (120), `:max-types` (80), `:max-scan` (200 facts per argument
  position), plus `seed-types`' bounds.  The reads are all vocabulary-sized — four extent
  reads for the arities, the taxonomy's own node set, one pinned `comment` read — plus a
  per-rendered-predicate `argIsa` query, so the cost tracks the vocabulary and never the
  number of facts."
  ([kb term] (inventory kb term {}))
  ([kb term {:keys [max-relations max-types max-scan]
             :or {max-relations 120 max-types 80 max-scan 200}
             :as opts}]
   (let [seed       (seed-types kb term opts)
         nb         (neighbourhood-types seed)
         nb-set     (set nb)
         arities    (declared-arities kb)
         all-types  (set (v/types kb))
         structural (structural-terms kb)
         head-only? #(and (structural %) (not (nb-set %)))
         domain?    #(and (not (all-types %)) (not (head-only? %)) (not (structural-functor? %)))
         declared   (set (filter domain? (keys arities)))
         ranked     (concat (map vector (repeat 0) (filter domain? (used-with kb term max-scan)))
                            (mapcat (fn [i t]
                                      (map vector (repeat (inc i))
                                           (filter domain? (argisa-predicates kb t))))
                                    (range) nb)
                            (map vector (repeat Long/MAX_VALUE) (sort declared)))
         best       (reduce (fn [acc [tier p]] (if (contains? acc p) acc (assoc acc p tier)))
                            {} ranked)
         ordered    (map first (sort-by (fn [[p tier]] [tier (str p)]) best))
         kept       (take max-relations ordered)
         types      (->> (concat (filter all-types nb) (sort (remove nb-set all-types)))
                         (remove head-only?)
                         distinct)
         shown      (take max-types types)]
     {:term term
      :seed seed
      :types (vec (for [t shown]
                    {:type t
                     :parent (first (sort-by (partial specificity kb) (disj (set (v/genls kb t)) t)))
                     :doc (first (core-context/comment-of kb t))}))
      :relations (vec (for [p kept] (assoc (predicate-shape kb p (arities p)) :tier (best p))))
      :structural (vec (for [p structural-predicates
                             :when (or (arities p) (seq (core-context/comment-of kb p)))]
                         (predicate-shape kb p (arities p))))
      :dropped {:relations (max 0 (- (count ordered) (count kept)))
                :types (max 0 (- (count types) (count shown)))}})))

;; ---- rendering it, bounded by tokens ------------------------------------

(defn signature
  "A predicate's shape as a signature — `2 : `animal` × `food``, with `?` for a position the
  KB constrains to no type, the bare arity when it constrains none of them, and nothing at
  all when it never declared the arity.  Reading
  `locatedIn/2 : physical_object × physical_object` is what makes reuse the obvious move."
  [{:keys [arity args]}]
  (let [by-pos (into {} args)
        n      (or arity (when (seq args) (apply max (map first args))))]
    (cond
      (nil? n)       nil
      (empty? args)  (str n)
      :else          (str n " : " (str/join " × " (for [i (range 1 (inc n))]
                                                    (if-let [t (by-pos i)] (selection/tick t) "?")))))))

(defn predicate-line
  "One predicate as a card line — its signature, its algebraic metadata, its inverse, and
  its own documentation:

      - `eats`/2 : `animal` × `food` — (eats ?animal ?food) means that ?animal takes …
      - `locatedIn`/2 : `physical_object` × `physical_object` [transitive] — …"
  [{:keys [predicate props inverse doc] :as shape} max-doc-chars]
  (let [tags (cond-> (vec props) inverse (conj (str "inverse of " (selection/tick inverse))))]
    (str "- " (selection/tick predicate)
         (when-let [s (signature shape)] (str "/" s))
         (when (seq tags) (str " [" (str/join ", " tags) "]"))
         (when-let [d (selection/clip doc max-doc-chars)] (str " — " d)))))

(defn type-line
  "One type as a card line: its nearest supertype, and what it means.  Every type in the
  block carries its parent, so the block *is* the hierarchy — no separate subtype list is
  needed to read it."
  [{:keys [type parent doc]} max-doc-chars]
  (str "- " (selection/tick type)
       (when parent (str " < " (selection/tick parent)))
       (when-let [d (selection/clip doc max-doc-chars)] (str " — " d))))

(defn- fit
  "Take entries while their running token estimate stays under `max-tokens`, and say how
  many were left out.  The inventory is the one section that can be trimmed without losing
  knowledge — a predicate not listed is a predicate the model will not reuse, which is a
  worse answer, never a wrong one — so this trims where `vaelii.impl.llm.selection` refuses."
  [lines max-tokens]
  (loop [kept [] spent 0 [l & more] lines]
    (if (nil? l)
      [kept 0]
      (let [cost (selection/estimate-tokens l)]
        (if (and max-tokens (> (+ spent cost) max-tokens))
          [kept (inc (count more))]
          (recur (conj kept l) (long (+ spent cost)) more))))))

(defn- block
  [heading lead lines cut noun]
  (when (seq lines)
    (str "### " heading "\n\n"
         (when lead (str lead "\n\n"))
         (str/join "\n" lines)
         (when (pos? cut) (str "\n\n_… and " cut " further " noun ", not listed here._")))))

(defn render
  "The inventory as the prompt's vocabulary section, in markdown — **three blocks**: the
  domain relations to reuse, the type names to reuse, and the small structural set a claim
  about a kind is stated with.

  The relation block is headed by the instruction that makes it load-bearing, since a card
  the model reads as background buys nothing.  `opts`: `:max-tokens` (nil = no cap),
  `:max-doc-chars` (140).  Where a cap or a count bound cut a block, the number left out is
  stated rather than hidden."
  ([inv] (render inv {}))
  ([{:keys [relations types structural dropped]} {:keys [max-tokens max-doc-chars]
                                                  :or {max-doc-chars 140}}]
   (let [share (fn [f] (when max-tokens (long (* f max-tokens))))
         [rlines rcut] (fit (map #(predicate-line % max-doc-chars) relations) (share 0.55))
         [tlines tcut] (fit (map #(type-line % max-doc-chars) types) (share 0.3))
         [slines scut] (fit (map #(predicate-line % max-doc-chars) structural) (share 0.15))]
     (str/join
      "\n\n"
      (remove str/blank?
              [(block "Relations already in this knowledge base — reuse these"
                      (str "`name/arity : argument types`. Say what you mean with one of these "
                           "and its arguments rather than inventing a predicate name that "
                           "spells the argument out.")
                      rlines (+ (or (:relations dropped) 0) rcut) "relations")
               (block "Type names already in this knowledge base"
                      "`subtype < supertype`. Reuse a type name rather than coining a synonym."
                      tlines (+ (or (:types dropped) 0) tcut) "types")
               (block "Stating a claim about a kind"
                      nil slines scut "structural predicates")])))))

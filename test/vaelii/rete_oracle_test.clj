(ns vaelii.rete-oracle-test
  "The correctness gate for the incremental matcher (`vaelii.impl.rete`).

  The engine keeps the semi-naive `vaelii.impl.chain` as the **reference**
  implementation and holds the incremental network to it, exactly as the taxonomy
  keeps `closures` / `equality-partition` as reference impls the incremental versions
  are oracle-tested against.  Two layers of oracle:

    * matcher-level — `rete/rete-match-pattern` must return the *same set* as
      `res/match-pattern` for every probe pattern over a populated KB.  This is the
      one place the network can differ, so it is pinned directly.

    * end-to-end — the same randomized sequence of rule/fact asserts and retracts,
      run once through the reference chain and once through the incremental matcher,
      must leave **identical derived content**: the same stored sentexes and the same
      justifications (compared by content, since handles are allocated per run).  The two
      KBs live on the two database pairs the suite reserves (scratch + isolated) so
      they can be stepped in lock-step and compared after *every* operation, which
      localizes any divergence to the op that caused it.

  The random ontology exercises every invariant the network must preserve: multi-
  antecedent joins with a leading-variable non-trigger antecedent (the case the
  network exists to speed up), recursion + the depth guard, unary subtype fan-out, a
  symmetric predicate matched as a non-trigger antecedent (the mirror probe), a
  deferred `lessThan` antecedent, `exceptWhen` blocking, a `functional` predicate that
  derives an equality twin, sibling-context firings with no common placement, and
  retraction with re-derivation."
  (:require [clojure.set :as set]
            [clojure.test :refer [deftest is]]
            [vaelii.core :as v]
            [vaelii.impl.chain :as chain]
            [vaelii.impl.core-context :as core-context]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rete :as rete]
            [vaelii.test-util :as tu]))

;; ---- the shared ontology (identical on both KBs) ------------------------

(defn build-ontology!
  "CoreContext vocabulary + a compact ontology whose rules cover every invariant.  A
  rule set, contexts, a type lattice, disjointness, and metadata — no contingent
  facts (those are the random sequence)."
  [kb]
  (core-context/load-into kb)
  ;; context spindle: Base sees Core; Left and Right are incomparable specs of Base,
  ;; so a rule in Base firing over a Left fact and a Right fact has no common
  ;; placement context (the sibling no-placement case)
  (v/assert kb '(genlContext BaseContext CoreContext) 'CoreContext {:strength :monotonic})
  (v/assert kb '(genlContext LeftContext BaseContext) 'CoreContext {:strength :monotonic})
  (v/assert kb '(genlContext RightContext BaseContext) 'CoreContext {:strength :monotonic})
  ;; type lattice
  (doseq [e '[(genl animal thing) (genl dog animal) (genl poodle dog)
              (genl cat animal) (genl bird animal) (genl penguin bird)]]
    (v/assert kb e 'BaseContext {:strength :monotonic}))
  (v/assert kb '(disjoint dog cat) 'BaseContext {:strength :monotonic})
  ;; metadata
  (v/assert kb '(symmetric siblingOf) 'BaseContext {:strength :monotonic})
  (v/assert kb '(transitive ancestorOf) 'BaseContext {:strength :monotonic})
  (v/assert kb '(functional bestFriendOf) 'BaseContext {:strength :monotonic})
  ;; rules (all in Base, so they see facts in Left / Right / Base)
  (let [R (fn [ante conseq]
            (v/assert kb (list 'implies ante conseq) 'BaseContext))]
    ;; the leading-variable join the network exists to accelerate
    (R '(and (parentOf ?x ?y) (parentOf ?y ?z)) '(grandparentOf ?x ?z))
    ;; recursion + depth guard: right-recursive ancestor
    (R '(parentOf ?x ?y) '(ancestorOf ?x ?y))
    (R '(and (parentOf ?x ?y) (ancestorOf ?y ?z)) '(ancestorOf ?x ?z))
    ;; unary subtype fan-out (a poodle is a dog)
    (R '(dog ?x) '(hasFur ?x))
    ;; type antecedent joined with a relation
    (R '(and (owns ?p ?a) (animal ?a)) '(petOwner ?p))
    ;; a symmetric predicate as a NON-trigger antecedent — exercises the mirror probe
    ;; inside the matcher (triggered by parentOf, siblingOf joined second)
    (R '(and (parentOf ?x ?y) (siblingOf ?y ?z)) '(uncleAuntOf ?x ?z))
    ;; a deferred antecedent in a forward join (computed, not matched)
    (R '(and (ageOf ?x ?a) (ageOf ?y ?b) (lessThan ?a ?b)) '(youngerThan ?x ?y)))
  ;; exceptWhen default: birds fly unless penguins
  (v/assert kb '(exceptWhen (penguin ?b) (set/defaultRule (implies (bird ?b) (flies ?b))))
            'BaseContext)
  kb)

;; ---- content snapshots, by content not by handle ------------------------

(defn- sx-content [kb id]
  (when-let [s (p/get-sentex (:records kb) id)]
    [(:sentence s) (:context s) (:truth s)]))

(defn stored-content [kb]
  (into #{} (keep #(sx-content kb %)) (p/sentex-ids (:records kb))))

(defn believed-content [kb]
  (into #{} (comp (filter #(v/in? kb %)) (keep #(sx-content kb %)))
        (p/sentex-ids (:records kb))))

(defn justification-content [kb]
  (into #{}
        (keep (fn [id]
                (when-let [d (p/get-justification (:records kb) id)]
                  [(sx-content kb (:informant d))
                   (into #{} (map #(sx-content kb %)) (:antecedents d))
                   (sx-content kb (:consequence d))
                   (:strength d)])))
        (p/justification-ids (:records kb))))

(defn snapshot [kb]
  {:stored   (stored-content kb)
   :believed (believed-content kb)
   :deduced  (justification-content kb)})

(defn diff-report [ref-snap rete-snap]
  (into {}
        (for [k [:stored :believed :deduced]
              :let [only-ref  (set/difference (get ref-snap k) (get rete-snap k))
                    only-rete (set/difference (get rete-snap k) (get ref-snap k))]
              :when (or (seq only-ref) (seq only-rete))]
          [k {:only-reference (vec (take 6 only-ref))
              :only-rete      (vec (take 6 only-rete))}])))

;; ---- running an op on the reference vs the incremental path -------------

(defmacro with-rete [_rete-kb & body]
  `(binding [chain/*matcher* rete/rete-match-pattern] ~@body))

(defn apply-op!
  "Apply `op` to both KBs — the reference one plainly, the incremental one under the
  rete matcher — and return their post-op snapshots.  `op` is `[:assert sentence ctx opts]`
  or `[:retract sentence ctx]`."
  [ref-kb rete-kb op]
  (case (first op)
    :assert
    (let [[_ sentence ctx opts] op]
      (try (v/assert ref-kb sentence ctx opts) (catch Throwable _))
      (with-rete rete-kb (try (v/assert rete-kb sentence ctx opts) (catch Throwable _))))
    :retract
    (let [[_ sentence ctx] op
          hr (v/handle-of ref-kb sentence ctx)
          he (v/handle-of rete-kb sentence ctx)]
      ;; only retract when both hold it as-is, so the two stay in lock-step
      (when (and hr he)
        (v/retract! ref-kb hr)
        (with-rete rete-kb (v/retract! rete-kb he)))))
  [(snapshot ref-kb) (snapshot rete-kb)])

;; ---- the random op stream -----------------------------------------------

(def ^:private inds (mapv #(symbol (str "I" %)) (range 8)))
(def ^:private ctxs '[LeftContext RightContext BaseContext])

(defn- rand-fact [^java.util.Random rng]
  (let [ind #(nth inds (.nextInt rng (count inds)))
        ctx #(nth ctxs (.nextInt rng (count ctxs)))]
    (case (.nextInt rng 9)
      0 [:assert (list 'parentOf (ind) (ind)) (ctx) {:strength :monotonic}]
      1 [:assert (list 'siblingOf (ind) (ind)) (ctx) {:strength :monotonic}]
      2 [:assert (list 'owns (ind) (ind)) (ctx) {:strength :monotonic}]
      3 [:assert (list (nth '[dog poodle cat bird penguin] (.nextInt rng 5)) (ind))
         (ctx) {:strength :monotonic}]
      4 [:assert (list 'ageOf (ind) (.nextInt rng 5)) (ctx) {:strength :monotonic}]
      5 [:assert (list 'bestFriendOf (ind) (ind)) (ctx) {:strength :monotonic}]
      6 [:assert (list 'parentOf (ind) (ind)) (ctx) {}]        ; a :default premise
      7 [:assert (list 'bird (ind)) (ctx) {:strength :monotonic}]
      8 [:retract (list 'parentOf (ind) (ind)) (ctx)])))

;; ---- oracle 1: the matcher returns the reference set --------------------

(defn- proj [triples] (into #{} (map #(vec (take 2 %))) triples))

(deftest matcher-returns-the-reference-set
  (let [rete-kb (doto (tu/isolated-fresh) build-ontology!)]
    (try
      (rete/track! rete-kb)
      ;; populate with facts of varied shapes across contexts
      (with-rete rete-kb
        (doseq [f '[(parentOf I0 I1) (parentOf I1 I2) (parentOf I2 I3)
                    (siblingOf I1 I4) (siblingOf I5 I1)
                    (owns I0 I1) (dog I1) (poodle I2) (cat I3) (bird I4) (penguin I5)
                    (ageOf I0 3) (ageOf I1 4) (bestFriendOf I6 I7)]]
          (v/assert rete-kb f 'BaseContext {:strength :monotonic}))
        ;; every probe pattern must give the same [handle bindings] set both ways
        (doseq [pat '[(parentOf ?x ?y)      ; fully open
                      (parentOf I1 ?z)       ; leading value (trie-selective)
                      (parentOf ?x I2)       ; leading variable (the network's case)
                      (parentOf I0 I1)       ; ground (a test)
                      (parentOf I9 ?z)       ; no matches
                      (siblingOf ?x I1)      ; symmetric, needs the mirror
                      (siblingOf I1 ?y)      ; symmetric, other order
                      (animal ?a)            ; unary subtype fan-out
                      (dog ?a)               ; subtype (poodle satisfies)
                      (bird ?b)
                      (owns ?p ?a)
                      (ageOf ?x ?a)
                      (grandparentOf ?x ?z)]]
          (is (= (proj (res/match-pattern rete-kb pat '?ctx))
                 (proj (rete/rete-match-pattern rete-kb pat '?ctx)))
              (str "matcher diverged on " (pr-str pat)))))
      (finally (tu/clear-kb! rete-kb) (rete/disengage!)))))

;; ---- oracle 2: end-to-end derived-content equivalence -------------------

(deftest ^:slow end-to-end-agrees-with-the-reference-chain
  (dotimes [trial 6]
    (let [ref-kb  (doto (tu/fresh)          build-ontology!)
          rete-kb (doto (tu/isolated-fresh) build-ontology!)]
      (try
        (rete/track! rete-kb)
        ;; the ontologies alone must already agree (rules + metadata derive some things)
        (is (= (snapshot ref-kb) (snapshot rete-kb))
            (str "trial " trial ": ontologies diverged before any fact\n"
                 (pr-str (diff-report (snapshot ref-kb) (snapshot rete-kb)))))
        (let [rng (java.util.Random. (+ 1000 trial))]
          (dotimes [step 60]
            (let [op (rand-fact rng)
                  [rs es] (apply-op! ref-kb rete-kb op)]
              (is (= rs es)
                  (str "trial " trial " step " step " diverged after " (pr-str op) "\n"
                       (pr-str (diff-report rs es)))))))
        (finally
          (tu/clear-kb! ref-kb)
          (tu/clear-kb! rete-kb)
          (rete/disengage!))))))

;; ---- targeted scenarios (deterministic, for localization) ---------------

(defn- run-both [ops]
  (let [ref-kb  (doto (tu/fresh)          build-ontology!)
        rete-kb (doto (tu/isolated-fresh) build-ontology!)]
    (rete/track! rete-kb)
    (let [snaps (mapv #(apply-op! ref-kb rete-kb %) ops)
          ok    (every? (fn [[r e]] (= r e)) snaps)
          bad   (first (keep-indexed (fn [i [r e]] (when (not= r e) [i (diff-report r e)])) snaps))]
      (tu/clear-kb! ref-kb) (tu/clear-kb! rete-kb) (rete/disengage!)
      [ok bad])))

(deftest scenario-grandparent-leading-variable-join
  (let [[ok bad] (run-both '[[:assert (parentOf I0 I1) BaseContext {:strength :monotonic}]
                             [:assert (parentOf I1 I2) BaseContext {:strength :monotonic}]
                             [:assert (parentOf I2 I3) BaseContext {:strength :monotonic}]])]
    (is ok (str "diverged: " (pr-str bad)))))

(deftest scenario-recursion-and-depth
  (let [ops (mapv (fn [i] [:assert (list 'parentOf (nth inds i) (nth inds (inc i)))
                           'BaseContext {:strength :monotonic}])
                  (range 6))
        [ok bad] (run-both ops)]
    (is ok (str "diverged: " (pr-str bad)))))

(deftest scenario-exceptwhen-blocking
  (let [[ok bad] (run-both '[[:assert (bird I0) BaseContext {:strength :monotonic}]
                             [:assert (penguin I1) BaseContext {:strength :monotonic}]
                             ;; I1 is a bird (penguin<bird) but excepted; I0 flies
                             [:assert (bird I1) BaseContext {:strength :monotonic}]
                             [:retract (penguin I1) BaseContext]])]  ; releases the exception
    (is ok (str "diverged: " (pr-str bad)))))

(deftest scenario-symmetric-non-trigger-antecedent
  (let [[ok bad] (run-both '[[:assert (siblingOf I2 I3) BaseContext {:strength :monotonic}]
                             [:assert (parentOf I0 I2) BaseContext {:strength :monotonic}]])]
    ;; uncleAuntOf I0 I3 via (parentOf I0 I2)+(siblingOf I2 I3); siblingOf stored sorted
    (is ok (str "diverged: " (pr-str bad)))))

(deftest scenario-functional-twin-derivation
  (let [[ok bad] (run-both '[[:assert (bestFriendOf I0 I1) BaseContext {:strength :monotonic}]
                             [:assert (bestFriendOf I0 I2) BaseContext {:strength :monotonic}]])]
    ;; two values for a functional predicate derive (equals I1 I2)
    (is ok (str "diverged: " (pr-str bad)))))

(deftest scenario-sibling-context-no-placement
  (let [[ok bad] (run-both '[[:assert (parentOf I0 I1) LeftContext {:strength :monotonic}]
                             [:assert (parentOf I1 I2) RightContext {:strength :monotonic}]])]
    ;; grandparent join across Left and Right: no common descendant, no placement
    (is ok (str "diverged: " (pr-str bad)))))

(deftest scenario-deferred-antecedent
  (let [[ok bad] (run-both '[[:assert (ageOf I0 2) BaseContext {:strength :monotonic}]
                             [:assert (ageOf I1 4) BaseContext {:strength :monotonic}]
                             [:assert (ageOf I2 3) BaseContext {:strength :monotonic}]])]
    (is ok (str "diverged: " (pr-str bad)))))

(deftest scenario-retraction-and-rederivation
  (let [[ok bad] (run-both '[[:assert (parentOf I0 I1) BaseContext {:strength :monotonic}]
                             [:assert (parentOf I1 I2) BaseContext {:strength :monotonic}]
                             [:retract (parentOf I1 I2) BaseContext]
                             [:assert (parentOf I1 I2) BaseContext {:strength :monotonic}]])]
    (is ok (str "diverged: " (pr-str bad)))))

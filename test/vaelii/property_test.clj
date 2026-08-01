(ns vaelii.property-test
  "Property-based tests for the engine's crown-jewel invariant: **the same
  knowledge, given in any order, yields the same beliefs.**

  `order_independence_test` pins this down on a handful of hand-built scenarios and
  enumerates *every* permutation of each.  That is exhaustive but shallow — it only
  ever sees the shapes someone thought to write down.  Here test.check generates the
  scenarios instead: a random sub-multiset of a fixed, well-formed operation pool and
  a random reordering of it, thousands of shapes across a run, each shrunk to a
  minimal counterexample when it fails.  A generated ordering that reads differently
  from another ordering of the same operations is exactly the order-dependence this
  file exists to catch.

  The operation pool is deliberately the interaction-dense corner of the engine —
  a defeasible default, its exception, direct type facts, a monotonic premise that
  defeats the default, and a bare rule that propagates the default's conclusion — so
  a generated subset routinely exercises defeat, revival, and propagation together.
  Every pool operation is well-formed and asserting any sub-multiset in any order
  never throws, so a failing property is a real order-dependence, not a bad input.

  KNOWN GAP — a `genl` edge is *not* in the pool.  Asserting `(genl penguin bird)`
  *after* a `bird ⇒ flies` rule and a `penguin` fact does not re-fire the rule over
  the now-subtype-matching fact, so the derived `(flies …)` materializes only when
  the edge precedes the rule: `query`-visible belief becomes order-dependent (the
  on-demand `ask` answer stays order-independent).  Until that forward-materialization
  bug is fixed, a reorderable `genl` edge would make this property fail for a real
  reason unrelated to what it is guarding, so it is held out and tracked separately."
  (:require [clojure.test :refer [use-fixtures]]
            [clojure.test.check.clojure-test :refer [defspec]]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

;; Flush the scratch pair after this namespace's generated runs, so the KB content
;; the last generated ordering left behind does not leak into a later namespace.
(use-fixtures :once (fn [f] (f) (tu/clear-kb! (tu/test-kb))))

(defn- default-rule [antes conseq]
  (list 'set/defaultRule (list 'implies (cons 'and antes) conseq)))

;; Each entry is a [label op] pair; `op` applies one assertion to a KB.  Labelled so
;; a shrunk counterexample prints the operations, not opaque closures.
(def ^:private op-pool
  [[:default-birds-fly
    #(v/assert % (default-rule '[(bird ?x)] '(flies ?x)) 'UniverseContext)]
   [:penguins-dont-fly
    #(v/assert-rule % '[(penguin ?x)] '(not (flies ?x)) 'UniverseContext)]
   [:tweety-is-a-penguin
    #(v/assert % '(penguin Tweety) 'UniverseContext {:strength :monotonic})]
   [:tweety-is-a-bird
    #(v/assert % '(bird Tweety) 'UniverseContext)]
   [:robin-is-a-bird
    #(v/assert % '(bird Robin) 'UniverseContext)]
   [:flight-enables-travel
    #(v/assert-rule % '[(flies ?x)] '(canTravel ?x) 'UniverseContext)]])

(defn- believed? [kb sentence]
  (boolean (seq (v/sentexes-matching kb sentence 'UniverseContext))))

(defn- observe
  "A whole-KB reading, compared as one value across orderings.  Beliefs plus the
  defeat-class of each flight literal plus the dilemma/conflict counts — the same
  breadth `order_independence_test` settled on, so an order-dependent defeat, a
  double-counted contradiction, or a flipped class all surface as a diff."
  [kb]
  (let [tw (v/handle-of kb '(flies Tweety) 'UniverseContext)
        rb (v/handle-of kb '(flies Robin) 'UniverseContext)]
    {:tweety-flies       (believed? kb '(flies Tweety))
     :tweety-grounded    (believed? kb '(not (flies Tweety)))
     :tweety-travels     (believed? kb '(canTravel Tweety))
     :robin-flies        (believed? kb '(flies Robin))
     :robin-travels      (believed? kb '(canTravel Robin))
     :tweety-isa-bird    (v/isa? kb 'Tweety 'bird 'UniverseContext)
     :flies-classes      [(v/defeat-class kb tw) (v/defeat-class kb rb)]
     :contradictions     (count (v/contradictions kb))
     :conflicts          (count (v/conflicts kb))}))

(defn- run-ops
  "Apply `ops` (op fns) to a freshly cleared KB and return `observe`'s reading."
  [ops]
  (let [kb (tu/fresh)]
    (doseq [op ops] (op kb))
    (observe kb)))

(defn- gen-permutation
  "A generator of a uniformly random permutation of `coll` (version-independent — it
  does not lean on a particular test.check `shuffle` combinator)."
  [coll]
  (if (empty? coll)
    (gen/return [])
    (gen/let [i    (gen/choose 0 (dec (count coll)))
              rest (gen-permutation (into (subvec (vec coll) 0 i)
                                          (subvec (vec coll) (inc i))))]
      (into [(nth coll i)] rest))))

(def ^:private gen-scenario
  "A non-empty sub-multiset of the operation pool paired with one reordering of it."
  (gen/let [picks (gen/not-empty (gen/vector (gen/elements op-pool) 1 (count op-pool)))
            perm  (gen-permutation picks)]
    {:picks picks :perm perm}))

(defspec ^:slow order-independence-holds-over-generated-scenarios 300
  (prop/for-all [{:keys [picks perm]} gen-scenario]
                (= (run-ops (map second picks))
                   (run-ops (map second perm)))))

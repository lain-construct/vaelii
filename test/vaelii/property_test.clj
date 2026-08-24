;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.property-test
  "Property-based tests for the engine's crown-jewel invariant: **the same
  knowledge, given in any order, yields the same beliefs.**

  `order_independence_test` pins this down on a handful of hand-built scenarios and
  enumerates *every* permutation of each.  That is exhaustive but shallow — it only
  ever sees the shapes someone thought to write down.  Here test.check generates the
  scenarios instead: a random sub-multiset of a fixed, well-formed pool and two random
  orderings of it, thousands of shapes across a run, each shrunk to a minimal
  counterexample when it fails.  A generated ordering that reads differently from
  another ordering of the same operations is exactly the order-dependence this file
  exists to catch.

  The pool holds **chains**, not bare operations, and that is what lets a `retract!`
  into it: a retraction names the handle its own assertion allocated, so it may not be
  shuffled ahead of it, and a flat permutation has no way to say so.  A chain keeps its
  own order and interleaves freely with the others (`gen-linearization`).  Removals earn
  their place by asking what adds alone cannot: an operation whose net effect on the
  knowledge is nothing must leave the reading it found, whichever operations ran between
  the two halves.

  The pool is deliberately the interaction-dense corner of the engine — a defeasible
  default, its exception, direct type facts, a monotonic premise that defeats the
  default, a bare rule that propagates the default's conclusion, a `genl` edge that
  reaches the default's antecedent through the type hierarchy, and two chains that end
  where they began — so a generated subset routinely exercises defeat, revival,
  subsumption and a sweep together.  Every chain is well-formed and any sub-multiset of
  them runs in any *linear extension* without throwing, so a failing property is a real
  order-dependence and not a bad input.

  The `genl` edge is the operation this file was once written without.  An edge arriving
  *after* the rule and the fact it connects has to re-fire that rule over facts already
  stored, which is not the same work as firing the rules keyed on `genl` — the seeding
  `vaelii.impl.special/subsumption-seeds` does, and the claim
  `order_independence_test/a-firing-that-subsumes-is-order-independent` pins on four
  hand-written sentences.  Here it is one draw among the rest, so the seeding is asked
  about against defeat, revival and a removal at once rather than on its own."
  (:require [clojure.test :refer [use-fixtures]]
            [clojure.test.check.clojure-test :refer [defspec]]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

;; Flush the scratch space after this namespace's generated runs, so the KB content
;; the last generated ordering left behind does not leak into a later namespace.
(use-fixtures :once (fn [f] (f) (tu/clear-kb! (tu/test-kb))))

(defn- default-rule [antes conseq]
  (list 'set/defaultRule (list 'implies (cons 'and antes) conseq)))

;; Each entry is a **chain**: [label op] pairs that must run in the order written, `op`
;; applying one operation to a KB.  Most chains are one op long and constrain nothing.
;; Labelled so a shrunk counterexample prints the operations, not opaque closures.
(def ^:private chain-pool
  [[[:default-birds-fly
     #(v/assert % (default-rule '[(bird ?x)] '(flies ?x)) 'CxUniverse)]]
   [[:penguins-dont-fly
     #(v/assert-rule % '[(penguin ?x)] '(not (flies ?x)) 'CxUniverse)]]
   [[:tweety-is-a-penguin
     #(v/assert % '(penguin Tweety) 'CxUniverse {:strength :monotonic})]]
   [[:tweety-is-a-bird
     #(v/assert % '(bird Tweety) 'CxUniverse)]]
   [[:robin-is-a-bird
     #(v/assert % '(bird Robin) 'CxUniverse)]]
   [[:flight-enables-travel
     #(v/assert-rule % '[(flies ?x)] '(canTravel ?x) 'CxUniverse)]]
   ;; The edge that makes the penguin a bird by inheritance rather than by assertion,
   ;; so `default-birds-fly` reaches Tweety through the type hierarchy and
   ;; `penguins-dont-fly` meets it there.  Drawn in any position, including after both
   ;; the rule and the fact it connects.
   [[:penguins-are-birds
     #(v/assert % '(genl penguin bird) 'CxUniverse)]]
   ;; ---- the chains that end where they began ----
   ;; A fact learned and forgotten.  While it stands it feeds the default and whatever
   ;; the default feeds, so the retraction has a cascade to sweep; afterwards the KB
   ;; must read as though Sparrow was never mentioned, wherever the other operations
   ;; landed between the two halves.
   [[:sparrow-is-a-bird
     #(v/assert % '(bird Sparrow) 'CxUniverse)]
    [:forget-the-sparrow
     #(v/retract! % (v/handle-of % '(bird Sparrow) 'CxUniverse))]]
   ;; A doubt raised and withdrawn.  This one defeats rather than adds: while it stands
   ;; Robin's flight is OUT, and lifting it has to bring the conclusion back — by
   ;; relabelling if the conclusion is still stored, by re-deriving if the operations
   ;; that landed in between mean it never was.
   [[:doubt-robins-flight
     #(v/assert % '(not (flies Robin)) 'CxUniverse {:strength :monotonic})]
    [:withdraw-the-doubt
     #(v/retract! % (v/handle-of % '(not (flies Robin)) 'CxUniverse))]]])

(defn- believed? [kb sentence]
  (boolean (seq (v/sentexes-matching kb sentence 'CxUniverse))))

(defn- observe
  "A whole-KB reading, compared as one value across orderings.  Beliefs plus the
  defeat-class of each flight literal plus the dilemma/conflict counts — the same
  breadth `order_independence_test` settled on, so an order-dependent defeat, a
  double-counted contradiction, or a flipped class all surface as a diff."
  [kb]
  (let [tw (v/handle-of kb '(flies Tweety) 'CxUniverse)
        rb (v/handle-of kb '(flies Robin) 'CxUniverse)]
    {:tweety-flies       (believed? kb '(flies Tweety))
     :tweety-grounded    (believed? kb '(not (flies Tweety)))
     :tweety-travels     (believed? kb '(canTravel Tweety))
     :robin-flies        (believed? kb '(flies Robin))
     :robin-travels      (believed? kb '(canTravel Robin))
     :sparrow-flies      (believed? kb '(flies Sparrow))
     :sparrow-travels    (believed? kb '(canTravel Sparrow))
     :tweety-isa-bird    (v/isa? kb 'Tweety 'bird 'CxUniverse)
     :flies-classes      [(v/defeat-class kb tw) (v/defeat-class kb rb)]
     :contradictions     (count (v/contradictions kb))
     :conflicts          (count (v/conflicts kb))
     ;; The two content sets are here for the removals.  A chain that ends where it began
     ;; contributes nothing to any belief named above, so a sweep that stopped short —
     ;; a conclusion left believed on a support that is gone, a premise mark left on a
     ;; handle the retraction was supposed to give back — needs a reading that does not
     ;; depend on the test having named the sentence in advance.
     ;;
     ;; **Content, and belief, and nothing else.**  Which sentexes are *stored* is not
     ;; order-independent and is not claimed to be: a conclusion drawn and then defeated
     ;; leaves a record that is OUT, where an ordering that defeated its antecedent first
     ;; never drew it at all, and the two read the same belief off different record sets:
     ;; a stored sentex is not a believed one (README.md, "Belief filtering").  So this
     ;; counts neither records nor handles — it is the sentences believed, and asserted.
     :believed-set       (into #{} (comp (filter #(v/in? kb %))
                                         (map #(:sentence (v/sentex kb %))))
                               (tu/sentex-ids kb))
     :premise-set        (into #{} (map #(:sentence (v/sentex kb %)))
                               (tu/premise-ids kb))}))

(defn- run-ops
  "Apply `ops` (op fns) to a freshly cleared KB and return `observe`'s reading."
  [ops]
  (let [kb (tu/fresh)]
    (doseq [op ops] (op kb))
    (observe kb)))

(defn- gen-linearization
  "A generator of one random linear extension of `chains`: at each step pick a chain that
  still has operations left and take its head, so every chain keeps its own order while
  the chains interleave freely.  The generative counterpart of `order_independence_test`'s
  exhaustive `interleavings`, and the reason a chain in the pool may contain a
  `retract!` — a permutation generator would put the retraction before its own assert.

  Written out rather than taken from a test.check `shuffle` combinator, for the reason
  the permutation generator it replaces was: this stays fixed across versions of the
  library."
  [chains]
  (let [chains (into [] (remove empty?) chains)]
    (if (empty? chains)
      (gen/return [])
      (gen/let [i    (gen/choose 0 (dec (count chains)))
                tail (gen-linearization (update chains i rest))]
        (into [(first (nth chains i))] tail)))))

(def ^:private gen-scenario
  "A non-empty sub-multiset of the chain pool and two independent orderings of it.

  Two generated orderings rather than the chains as written against one reordering: with
  chains the written order is just one linear extension among many and has no claim to be
  the reference, and drawing both makes the property symmetric in what it compares."
  (gen/let [picks (gen/not-empty (gen/vector (gen/elements chain-pool) 1 (count chain-pool)))
            a     (gen-linearization picks)
            b     (gen-linearization picks)]
    {:picks picks :a a :b b}))

(defspec ^:slow order-independence-holds-over-generated-scenarios 300
  (prop/for-all [{:keys [a b]} gen-scenario]
                (= (run-ops (map second a))
                   (run-ops (map second b)))))

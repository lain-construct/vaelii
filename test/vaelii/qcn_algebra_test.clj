;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.qcn-algebra-test
  "The relation-algebra laws, held over every shipped algebra.

  `qcn_mask_test` checks that the compiled bitmask tables agree with the algebra's own
  set-valued `:compose` and `:converse`.  This asks the prior question: whether that
  algebra is a relation algebra at all.  A composition table is transcribed or computed
  by hand, and a wrong cell is a wrong *entailment* reported with as much confidence as a
  right one — never a crash — so the tables that have no independent derivation need a
  check that is not simply reading them again.

  Two of the three transcribed tables are re-derived from first principles by their own
  tests: `interval_test` enumerates every ordering of six endpoints, `point_test` every
  ordering of three instants.  **RCC-8's 8×8 has no such derivation** — regions have no
  coordinates to lay out — so these laws are what stands over it, and they are not weak:
  every single-cell mutation of `space/rcc8-composition` but three fails one of them, and
  the three are one shape, dropping a symmetric relation from its own square, where both
  sides of every law move together.

  The laws, and what each one would catch:

  * **converse is a total involution on the universe** — a converse naming a relation the
    algebra does not have, or a pair that does not pair off.
  * **composition is closed and never empty** — a cell naming a foreign relation, and a
    cell emptied by a typo, which would make a satisfiable network report inconsistent.
  * **the identity is a singleton, self-converse, and two-sided** — the diagonal reading
    `qcn/constraint` gives every pair `(i i)` without consulting the network.
  * **converse reverses composition**, `(a∘b)⌣ = b⌣∘a⌣` — the transposed cell of every
    entry, which is what makes a single mistyped cell visible from the other direction.
  * **the cycle law**, `c ∈ a∘b ⟺ a⌣∘c meets b` — Peirce's law, the one that ties all
    three operations together and the strongest single check on a transcribed table.

  **Associativity is deliberately not among them**, and the reason is a real difference
  between the algebras rather than an omission.  Five of the six compose associatively;
  `vaelii.impl.distance` does not, because its composition is exact per *pair* of classes
  and a set of classes loses the correlation between the two legs — the standard reading
  of a weak composition, and it costs path consistency nothing, which needs only that
  composition over-approximate the truth.

  The vocabulary is checked here too: a denotation naming a relation outside the universe
  encodes to nothing (`compile-algebra` masks against the universe by construction), so
  the goal it claims would be answered off a denotation the algebra never saw."
  (:require [clojure.set :as set]
            [clojure.test :refer [deftest is testing]]
            [vaelii.impl.distance :as dist]
            [vaelii.impl.interval :as iv]
            [vaelii.impl.orientation :as dir]
            [vaelii.impl.point :as pt]
            [vaelii.impl.relative :as rel]
            [vaelii.impl.space :as space]))

(def algebras
  "Every shipped algebra, by name."
  {:rcc8     space/rcc8-algebra
   :allen    iv/allen-algebra
   :cardinal dir/direction-algebra
   :relative rel/relative-algebra
   :distance dist/distance-algebra
   :point    pt/point-algebra})

(def calculi
  "Every shipped calculus, by name — the algebra plus the vocabulary over it."
  {:rcc8     space/rcc8
   :allen    iv/allen
   :cardinal dir/cardinal
   :relative rel/relative
   :distance dist/qualitative-distance
   :point    pt/instants})

(defn- offenders
  "The members of `xs` that fail `ok?`, at most five of them — a law is asserted once per
  algebra with its witnesses in the message, rather than once per pair or triple, so a
  failure names what broke it without the passing case costing thousands of assertions."
  [ok? xs]
  (into [] (comp (remove ok?) (take 5)) xs))

(defn- base-pairs [universe]
  (for [a universe b universe] [a b]))

(defn- base-triples [universe]
  (for [a universe b universe c universe] [a b c]))

;; ---- the laws ------------------------------------------------------------

(deftest converse-is-a-total-involution-on-the-universe
  (doseq [[nm {:keys [universe converse]}] algebras]
    (testing (name nm)
      (is (= [] (offenders #(set/subset? (converse #{%}) universe) universe))
          "every relation's converse is a relation of the algebra")
      (is (= [] (offenders #(= 1 (count (converse #{%}))) universe))
          "a base relation's converse is a base relation, not a disjunction")
      (is (= [] (offenders #(= #{%} (converse (converse #{%}))) universe))
          "converse is its own inverse")
      (is (= universe (converse universe))
          "so the universe is its own converse"))))

(deftest composition-is-closed-and-never-empty
  (doseq [[nm {:keys [universe compose]}] algebras]
    (testing (name nm)
      (is (= [] (offenders (fn [[a b]] (set/subset? (compose #{a} #{b}) universe))
                           (base-pairs universe)))
          "no cell names a relation outside the algebra")
      ;; jointly exhaustive: some relation always holds of the outer pair, so a cell that
      ;; composed to nothing would report a satisfiable network inconsistent
      (is (= [] (offenders (fn [[a b]] (seq (compose #{a} #{b})))
                           (base-pairs universe)))
          "no cell is empty"))))

(deftest the-identity-is-a-singleton-self-converse-and-two-sided
  (doseq [[nm {:keys [universe identity compose converse]}] algebras]
    (testing (name nm)
      (is (= 1 (count identity)) "the diagonal constraint is one relation")
      (is (set/subset? identity universe) "and one the algebra has")
      (is (= identity (converse identity)) "a thing stands to itself the same way round")
      (is (= [] (offenders #(and (= #{%} (compose identity #{%}))
                                 (= #{%} (compose #{%} identity)))
                           universe))
          "composing with the identity on either side changes nothing"))))

(deftest converse-reverses-composition
  (doseq [[nm {:keys [universe compose converse]}] algebras]
    (testing (name nm)
      (is (= [] (offenders (fn [[a b]]
                             (= (converse (compose #{a} #{b}))
                                (compose (converse #{b}) (converse #{a}))))
                           (base-pairs universe)))
          "(a∘b)⌣ = b⌣∘a⌣ over every pair of base relations"))))

(deftest the-cycle-law-ties-the-three-operations-together
  ;; Peirce's law: c is possible between x and z given a(x,y) and b(y,z) exactly when b is
  ;; possible between y and z given a⌣(y,x) and c(x,z).  It reads every cell of the table
  ;; against a transposed one, which is what makes a single mistyped entry visible.
  (doseq [[nm {:keys [universe compose converse]}] algebras]
    (testing (name nm)
      (is (= [] (offenders (fn [[a b c]]
                             (= (contains? (compose #{a} #{b}) c)
                                (boolean (seq (set/intersection
                                               (compose (converse #{a}) #{c}) #{b})))))
                           (base-triples universe)))
          "c ∈ a∘b ⟺ a⌣∘c meets b"))))

(deftest composition-and-converse-distribute-over-union
  ;; What the bitmask compilation's dynamic programming assumes (`qcn_mask_test` checks
  ;; the tables it builds; this checks the algebra it builds them from).  Held over the
  ;; universe and the identity rather than over 2^k sets, since the recurrence needs only
  ;; that a set's answer is the union of its members'.
  (doseq [[nm {:keys [universe identity compose converse]}] algebras]
    (testing (name nm)
      (let [union-of  (fn [f s] (into #{} (mapcat f) s))
            some-sets [universe identity (set/difference universe identity)]]
        (is (= [] (offenders #(= (converse %) (union-of (fn [r] (converse #{r})) %))
                             some-sets))
            "the converse of a set is the union of its members' converses")
        (is (= [] (offenders (fn [[s1 s2]]
                               (= (compose s1 s2)
                                  (union-of (fn [a] (union-of #(compose #{a} #{%}) s2)) s1)))
                             (for [s1 some-sets s2 some-sets] [s1 s2])))
            "and a composition of sets the union of the pairwise compositions")))))

;; ---- the vocabulary over the algebra -------------------------------------

(deftest every-denotation-is-a-subset-of-the-universe
  ;; A denotation naming a relation the algebra does not have encodes to nothing — the
  ;; mask is built against the universe — so the predicate would be entailed by a
  ;; constraint set nobody wrote.
  (doseq [[nm calc] calculi]
    (testing (name nm)
      (let [universe (:universe (:algebra calc))]
        (is (= [] (offenders #(set/subset? ((:denotation calc) %) universe)
                             (:predicates calc)))
            "no predicate denotes a relation outside the algebra")
        (is (= [] (offenders #(seq ((:denotation calc) %)) (:predicates calc)))
            "and none denotes nothing at all")))))

(deftest the-base-predicates-are-the-singletons-and-cover-the-universe
  (doseq [[nm calc] calculi]
    (testing (name nm)
      (let [universe   (:universe (:algebra calc))
            denotation (:denotation calc)
            singletons (filter #(= 1 (count (denotation %))) (:predicates calc))]
        (is (= universe (into #{} (mapcat denotation) singletons))
            "every base relation has a predicate of its own")
        (is (= (count universe) (count singletons))
            "and no two predicates name the same one")))))

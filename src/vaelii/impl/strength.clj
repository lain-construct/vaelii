(ns vaelii.impl.strength
  "Assumption strengths on beliefs, and the derived *defeat-class* that resolves
  soft contradictions.

  There are exactly two classes, and a user asserts content at either:

    :monotonic  known-true; indefeasible; never sent to a solver.
    :default    defeasible; the common case — most of a common-sense KB.

  They form a total order  monotonic > default.  In a contradiction the member of
  *least* class is defeated; :monotonic ('known true') content is never sent to a
  solver.

  Derivation adds no class of its own.  A justification confers `min(its own
  strength, the weakest of its antecedents' classes)`, and a rule's own strength is
  read off its defeasibility: a **bare rule** confers :monotonic — it adds no
  defeasibility, so its conclusion is capped by whatever it rests on — and a
  **`set/defaultRule`** confers :default, because it introduces defeasibility.  So a
  bare rule over :monotonic facts concludes :monotonic (it *is* monotonically
  entailed), and the same rule over a :default premise concludes :default.

  There are exactly two classes; do not add a third.  Undercutting a defeasible
  generality is done with `exceptWhen` (docs/exceptions.md) — the excepted rule states
  its own exception and simply does not fire — so no intermediate class is needed to
  out-rank one belief with another."
  (:refer-clojure :exclude [min max]))

(def assertable
  "The strengths a caller may put on an assertion."
  #{:monotonic :default})

(def ^:private rank    {:default 1 :monotonic 2})
(def ^:private by-rank {1 :default 2 :monotonic})

(defn rank-of "Numeric rank of a class (0 for unknown)." [class] (get rank class 0))
(defn class-of-rank [r] (get by-rank r :default))

(defn max "The stronger of two classes." [a b] (if (>= (rank-of a) (rank-of b)) a b))
(defn min "The weaker of two classes."   [a b] (if (<= (rank-of a) (rank-of b)) a b))

(defn defeasible? "Is this class a plain default (the only solver-eligible class)?"
  [class] (= class :default))
(defn known-true? "Is this class strong enough to never be sent to a solver?"
  [class] (= class :monotonic))
(defn assertable? [s] (contains? assertable s))

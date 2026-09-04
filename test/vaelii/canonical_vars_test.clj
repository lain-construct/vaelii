;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.canonical-vars-test
  "Canonical variable namespaces, and the two ways a form moves between them.

  A **renaming** is a permutation and a **substitution** is a chain to a term.  They are
  both maps from variables, they look alike, and applying one with the other's function
  is either wrong or non-terminating — which is the whole reason `sentex/rename-vars`
  exists beside `res/substitute`."
  (:require [clojure.set :as set]
            [clojure.test :refer [deftest is testing]]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]))

;; ---- renaming is one pass, because a permutation has cycles ---------------

(deftest a-renaming-is-applied-in-one-pass
  (testing "a swap is the smallest map that tells a renaming from a substitution"
    (is (= '(P ?var1 ?var0)
           (sx/rename-vars '(P ?var0 ?var1) '{?var0 ?var1, ?var1 ?var0}))))
  (testing "and a longer cycle is no different"
    (is (= '(P ?var1 ?var2 ?var0)
           (sx/rename-vars '(P ?var0 ?var1 ?var2)
                           '{?var0 ?var1, ?var1 ?var2, ?var2 ?var0}))))
  (testing "shape is preserved — a conjunction is a vector, a literal a list"
    (is (= '[(P ?var1 (F ?var0)) (Q ?var0)]
           (sx/rename-vars '[(P ?var0 (F ?var1)) (Q ?var1)]
                           '{?var0 ?var1, ?var1 ?var0}))))
  (testing "an unmapped variable is left alone"
    (is (= '(P ?var1 ?other) (sx/rename-vars '(P ?var0 ?other) '{?var0 ?var1}))))
  (testing "the chasing substitution cannot do this, and must not be asked to"
    ;; `substitute` follows ?var0 -> ?var1 -> ?var0 forever.  It is right for a
    ;; unifier, whose bindings the occurs check keeps acyclic, and wrong for a
    ;; permutation.  Two maps that look alike and need two functions.
    (is (thrown? StackOverflowError
                 (doall (res/substitute '(P ?var0 ?var1) '{?var0 ?var1, ?var1 ?var0}))))))

;; ---- canonicalizing a conjunction ----------------------------------------

(deftest alpha-variant-conjunctions-canonicalize-to-one-value
  ;; The identity a node engine needs: two conjunctions differing only in what their
  ;; variables are called are one question, and must be recognized as one.
  (let [[a _] (sx/canonical-conjunction '[(edgeOf ?x ?y) (anc ?y ?z)])
        [b _] (sx/canonical-conjunction '[(edgeOf ?p ?q) (anc ?q ?r)])]
    (is (= a b '[(edgeOf ?var0 ?var1) (anc ?var1 ?var2)]))
    (testing "one numbering across the whole conjunction, so a shared variable still joins"
      ;; the shared variable is argument 2 of the first literal and argument 1 of
      ;; the second — one name, so the join survives canonicalization
      (is (= '?var1 (nth (first a) 2) (nth (second a) 1))))
    (testing "and a differently-joined conjunction stays a different value"
      (is (not= a (first (sx/canonical-conjunction '[(edgeOf ?x ?y) (anc ?z ?w)])))))))

(deftest the-varmap-carries-a-solution-back-to-the-names-the-caller-used
  (let [[canon vm] (sx/canonical-conjunction '[(anc ?who ?whom)])]
    (is (= '[(anc ?var0 ?var1)] canon))
    (is (= '{?var0 ?who, ?var1 ?whom} vm))
    (testing "round-tripping the conjunction returns what went in"
      (is (= '[(anc ?who ?whom)] (sx/rename-vars canon vm))))
    (testing "and a canonical-space answer renames onto the caller's keys"
      (is (= '{?who Tom, ?whom Rex}
             (into {} (map (fn [[k v]] [(get vm k k) v])) '{?var0 Tom, ?var1 Rex}))))))

(deftest a-caller-writing-the-canonical-names-produces-a-permutation
  ;; The case that makes one-pass renaming required rather than fastidious: a query
  ;; spelled with the engine's own canonical names, crossed over.
  (let [[canon vm] (sx/canonical-conjunction '[(anc ?var1 ?var0)])]
    (is (= '[(anc ?var0 ?var1)] canon))
    (is (= '{?var0 ?var1, ?var1 ?var0} vm) "the varmap here is a swap")
    (is (= '[(anc ?var1 ?var0)] (sx/rename-vars canon vm)))))

(deftest numbering-from-an-offset-makes-two-namespaces-disjoint
  ;; How a stored rule (spelled ?var0 ?var1 …) is renamed clear of a conjunction spelled
  ;; the same way: number it past the end instead of decorating its names.
  (let [[canon vm] (sx/canonical-conjunction '[(anc ?var0 ?var1) (edgeOf ?var0 ?var1)] 3)]
    (is (= '[(anc ?var3 ?var4) (edgeOf ?var3 ?var4)] canon))
    (is (= '{?var3 ?var0, ?var4 ?var1} vm))
    (testing "so nothing it mentions collides with ?var0 ?var1 ?var2"
      (is (empty? (set/intersection
                   (res/form-variables canon) '#{?var0 ?var1 ?var2}))))))

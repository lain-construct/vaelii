;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.literal-cache-test
  "The cache key's canonicalizer (`literal-cache/canonicalize`) and the translation back
  (`rename-bindings`).  Two spellings of one question must converge to one key, and a
  literal that repeats a variable must **not** converge with one that does not — the
  distinction `res/goal-key` deliberately does not draw."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.impl.literal-cache :as lc]
            [vaelii.impl.resolution :as res]))

(defn- canon [form] (first (lc/canonicalize form)))
(defn- back  [form] (second (lc/canonicalize form)))

(deftest spellings-of-one-question-converge
  (testing "variable names do not survive canonicalization"
    (is (= (canon '(parentOf Tom ?y)) (canon '(parentOf Tom ?z))))
    (is (= '(parentOf Tom ?0) (canon '(parentOf Tom ?y)))))
  (testing "first occurrence, not sorted — position drives the numbering"
    (is (= '(between ?0 ?1 ?0) (canon '(between ?a ?b ?a))))
    (is (= '(between ?0 ?1 ?0) (canon '(between ?q ?p ?q)))))
  (testing "a ground literal is unchanged and needs no rename"
    (is (= '(parentOf Tom Bob) (canon '(parentOf Tom Bob))))
    (is (= {} (back '(parentOf Tom Bob))))))

(deftest repetition-is-preserved
  (testing "a repeated variable does not share a key with two distinct ones"
    (is (not= (canon '(P ?x ?x)) (canon '(P ?x ?y))))
    (is (= '(P ?0 ?0) (canon '(P ?x ?x))))
    (is (= '(P ?0 ?1) (canon '(P ?x ?y)))))
  (testing "goal-key collapses exactly the distinction this must keep"
    ;; the trap the canonicalizer exists to avoid: goal-key is a sound loop guard and
    ;; an unsound cache key, because (P ?x ?y)'s answers include pairs (P ?x ?x) excludes
    (is (= (res/goal-key '(P ?x ?x)) (res/goal-key '(P ?x ?y))))))

(deftest anonymous-variables-are-ordinary-variables
  ;; `unify` binds `_` and chases it — (P _ _) fails against (P A B) — so the cache key
  ;; must share it, unlike the index key (`sentex/alpha-rename`) which makes each fresh
  (testing "unify treats a repeated _ as one variable"
    (is (nil? (res/unify '(P _ _) '(P A B))))
    (is (some? (res/unify '(P _ _) '(P A A)))))
  (testing "so the canonical form repeats it, and matches the ?x ?x spelling"
    (is (= '(P ?0 ?0) (canon '(P _ _))))
    (is (= (canon '(P ?x ?x)) (canon '(P _ _))))
    (is (not= (canon '(P _ _)) (canon '(P _ ?y))))))

(deftest shape-and-nesting-survive
  (testing "a nested compound argument is renamed in place"
    (is (= '(holdsIn ?0 (parentOf ?1 Tom)) (canon '(holdsIn ?c (parentOf ?x Tom))))))
  (testing "a vector stays a vector, a list stays a list"
    (is (vector? (canon '[(P ?x) (Q ?x)])))
    (is (seq? (canon '(P ?x)))))
  (testing "a conjunction numbers jointly, so the shared variable stays shared"
    (is (= '[(P ?0) (Q ?0 ?1)] (canon '[(P ?x) (Q ?x ?y)])))))

(deftest rename-back-restores-the-callers-names
  (let [[c r] (lc/canonicalize '(parentOf ?parent ?child))]
    (is (= '(parentOf ?0 ?1) c))
    (testing "keys come back"
      (is (= '{?parent Tom ?child Bob}
             (lc/rename-bindings r '{?0 Tom ?1 Bob}))))
    (testing "values come back too — a goal variable bound to another goal variable"
      (is (= '{?parent ?child} (lc/rename-bindings r '{?0 ?1}))))
    (testing "a canonical name inside a compound value comes back"
      (is (= '{?parent (f ?child)} (lc/rename-bindings r '{?0 (f ?1)})))))
  (testing "an empty rename is identity"
    (is (= '{?x Tom} (lc/rename-bindings {} '{?x Tom}))))
  (testing "a rule's own ?varN names are not canonical names and pass through"
    (let [[_ r] (lc/canonicalize '(P ?x))]
      (is (= '{?x ?var0} (lc/rename-bindings r '{?0 ?var0}))))))

(deftest a-caller-spelling-its-own-goal-?0-is-not-rewritten-twice
  ;; ?0 is a legal variable name for a caller to use; canonicalization renumbers it like
  ;; any other, and rename-back must not then chase its own output
  (let [[c r] (lc/canonicalize '(P ?x ?0))]
    (is (= '(P ?0 ?1) c))
    (is (= '{?0 ?x, ?1 ?0} r))
    (is (= '{?x Tom, ?0 Bob} (lc/rename-bindings r '{?0 Tom ?1 Bob})))
    (testing "a value carrying both canonical names lands on the caller's two names"
      (is (= '{?x (pair ?x ?0)} (lc/rename-bindings r '{?0 (pair ?0 ?1)}))))))

(deftest round-trip-under-substitution
  ;; the property the cache rests on: solving the canonical literal and renaming back
  ;; gives what solving the caller's literal would have given
  (let [goal '(parentOf ?p ?c)
        [c r] (lc/canonicalize goal)
        sols  (map #(res/unify c % {}) ['(parentOf Tom Bob) '(parentOf Ann Sue)])]
    (is (= '[{?p Tom ?c Bob} {?p Ann ?c Sue}]
           (mapv #(lc/rename-bindings r %) sols)))
    (is (= (mapv #(res/unify goal % {}) ['(parentOf Tom Bob) '(parentOf Ann Sue)])
           (mapv #(lc/rename-bindings r %) sols)))))

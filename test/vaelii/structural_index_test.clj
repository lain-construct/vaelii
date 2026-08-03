;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.structural-index-test
  "Oracle for structural (paren-marked) subterm indexing (docs/indexing.md).

  A positive fact's nested compound arguments linearize into the trie path, so a deep
  position — `QuantityFn`, `Kilogram` inside `(mass ?o (QuantityFn ?n Kilogram))` — is
  its own matchable, selective trie level instead of one opaque token.  The claim, as
  with `arg_root_retrieval_test`, is that this changes only *how* candidates are
  fetched, never *which* sentexes match: `res/*structural-index*` ON narrows on the
  deep positions, OFF falls back to the functor extent, and the existing `unify`
  filters both to the identical set.

  So the gate: `match-pattern` / `matches-visible` / `ask` with the flag OFF must
  return exactly what they return with it ON, over a corpus mixing flat facts,
  top-level-variable queries, deep-leaf-variable queries `(p (F ?x) b)`,
  whole-subterm-variable queries `(p ?y b)`, and nested compounds `(p (F (G ?x)) b)`.
  Plus: the structural retrieval is genuinely *selective* (fewer candidates than the
  functor extent), a reindex regenerates the index in the new shape, and dedup over compound
  arguments is unaffected."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.core-context :as core-context]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.plan :as plan]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.test-util :as tu]))

;; a corpus with nested compound arguments (the structural case) alongside flat facts
(defn- load-corpus [kb]
  (core-context/load-into kb)
  (doseq [s '[(mass Obj1 (QuantityFn 5 Kilogram))
              (mass Obj2 (QuantityFn 9 Meter))
              (mass Obj3 (QuantityFn 5 Meter))
              (mass Obj4 (QuantityFn 12 Kilogram))
              (mass Obj5 (QuantityFn 5 Second))
              (length Rod1 (QuantityFn 3 Meter))
              (length Rod2 (QuantityFn 3 Kilogram))
              (holds Alice (BeliefFn (loves Bob Carol)))
              (holds Dave  (BeliefFn (loves Bob Ann)))
              (p (F (G a)) b)
              (p (F (G c)) b)
              (p (F (H a)) b)
              (p (K a) b)
              (rel X (Fn p) (Gn q) Z)
              (rel X (Fn p) (Gn r) Z)
              (parentOf Tom Bob)
              (parentOf Tom Ann)
              (bornIn Tom 1970)]]
    (v/assert kb s 'MantleContext {:strength :monotonic}))
  kb)

(use-fixtures :once (tu/loaded load-corpus))
(use-fixtures :each (tu/neutral))

(defn- proj [triples] (into #{} (map #(vec (take 2 %))) triples))

(defn- both-ways
  "The [handle bindings] set `f` yields with `*structural-index*` off and on — the
  pair the oracle demands be equal."
  [f]
  [(binding [res/*structural-index* false] (proj (f)))
   (binding [res/*structural-index* true]  (proj (f)))])

;; the query corpus: every shape the encoding must handle
(def ^:private patterns
  '[;; fully ground (a test)
    (mass Obj1 (QuantityFn 5 Kilogram))
    ;; deep-leaf variables — selective on the surrounding deep atoms
    (mass ?o (QuantityFn ?n Kilogram))
    (mass ?o (QuantityFn 5 ?u))
    (mass ?o (QuantityFn ?n ?u))
    (length ?o (QuantityFn 3 ?u))
    ;; top-level / whole-subterm variables — the skip
    (mass ?o ?whole)
    (mass Obj1 ?whole)
    (p ?y b)
    (p ?y ?z)
    ;; nested compounds
    (p (F (G ?x)) b)
    (p (F (H ?x)) b)
    (p (F ?mid) b)
    (holds ?who (BeliefFn (loves Bob ?whom)))
    (holds ?who (BeliefFn ?prop))
    ;; multi-compound argument
    (rel ?x (Fn p) (Gn ?g) Z)
    (rel ?x ?f ?g Z)
    ;; flat facts (must be byte-for-byte unchanged)
    (parentOf Tom ?y)
    (parentOf ?x Bob)
    (bornIn ?p 1970)
    ;; non-matching probes
    (mass ?o (QuantityFn 5 Furlong))
    (p (F (G ?x)) zzz)
    (nope ?x ?y)])

(deftest match-pattern-structural-equals-functor-extent
  (tu/with-kb [kb]
    (doseq [pat patterns]
      (let [[off on] (both-ways #(res/match-pattern kb pat '?ctx))]
        (is (= off on)
            (str "match-pattern diverged (structural off vs on) on " (pr-str pat)
                 "\n  off: " (pr-str off) "\n  on:  " (pr-str on)))))))

(deftest matches-visible-structural-equals-functor-extent
  (tu/with-kb [kb]
    (doseq [ctx '[MantleContext UniverseContext]
            pat patterns]
      (let [[off on] (both-ways #(res/matches-visible kb pat ctx))]
        (is (= off on) (str "matches-visible diverged on " (pr-str pat) " @ " ctx))))))

(deftest ask-structural-equals-functor-extent
  (tu/with-kb [kb]
    (doseq [pat patterns]
      (let [off (binding [res/*structural-index* false] (set (v/ask kb pat '?ctx)))
            on  (binding [res/*structural-index* true]  (set (v/ask kb pat '?ctx)))]
        (is (= off on) (str "ask diverged on " (pr-str pat)
                            "\n  off: " (pr-str off) "\n  on: " (pr-str on)))))))

;; ---- correctness: the actual matches, not just on==off -------------------

(deftest deep-positions-match-the-right-facts
  (tu/with-kb [kb]
    (testing "deep-leaf variable is selective on the surrounding deep atoms"
      (is (= #{'Obj1 'Obj4} (into #{} (map '?o) (v/ask kb '(mass ?o (QuantityFn ?n Kilogram)) '?ctx))))
      (is (= #{'Obj1} (into #{} (map '?o) (v/ask kb '(mass ?o (QuantityFn 5 Kilogram)) '?ctx))))
      (is (= #{'Obj1 'Obj2 'Obj3 'Obj4 'Obj5}
             (into #{} (map '?o) (v/ask kb '(mass ?o (QuantityFn ?n ?u)) '?ctx)))))
    (testing "whole-subterm variable binds the entire compound"
      (is (= #{'(QuantityFn 5 Kilogram)}
             (into #{} (map '?whole) (v/ask kb '(mass Obj1 ?whole) '?ctx)))))
    (testing "whole-subterm variable skips compounds of mixed depth"
      ;; (p ?y b) advances past (F (G a)) [depth 2] and (K a) [depth 1] alike
      (is (= #{'(F (G a)) '(F (G c)) '(F (H a)) '(K a)}
             (into #{} (map '?y) (v/ask kb '(p ?y b) '?ctx)))))
    (testing "nested depth: (p (F (G ?x)) b) matches (G a)/(G c) but not (H a)"
      (is (= #{'a 'c} (into #{} (map '?x) (v/ask kb '(p (F (G ?x)) b) '?ctx))))
      (is (= #{'a}    (into #{} (map '?x) (v/ask kb '(p (F (H ?x)) b) '?ctx)))))))

(deftest query-matches-partial-compounds
  ;; `query` uses `p/lookup` directly (always structural), so it is correct with no
  ;; toggle: a partial compound argument narrows rather than missing entirely
  (tu/with-kb [kb]
    (is (= 2 (count (v/sentexes-matching kb '(mass ?o (QuantityFn ?n Kilogram)) '?ctx))))
    (is (= 1 (count (v/sentexes-matching kb '(mass Obj1 (QuantityFn ?n Kilogram)) '?ctx))))
    (is (= 5 (count (v/sentexes-matching kb '(mass ?o ?whole) '?ctx))))))

;; ---- selectivity: the structural trie beats the functor extent -----------

(deftest structural-retrieval-is-selective
  (tu/with-kb [kb]
    (let [ix  (:index kb)
          _pat (kb/find-sentex-handle kb '(mass ?o (QuantityFn ?n Kilogram)) '?ctx) ; realize the path
          sxp (sx/path (res/kb-sentex kb '(mass ?o (QuantityFn ?n Kilogram)) '?ctx))
          structural (count (p/lookup ix sxp))              ; the ON candidate set
          extent     (count (p/sentexes-with-functor ix 'mass))]  ; the OFF baseline
      (testing "structural lookup returns the true match count, not the functor extent"
        (is (= 2 structural) "only the two Kilogram masses")
        (is (= 5 extent)     "the whole mass extent")
        (is (< structural extent) "structural narrowing is a strict win here")))))

;; ---- planner: deep-prefix selectivity ------------------------------------

(deftest planner-costs-a-deep-prefix-selectively
  (tu/with-kb [kb]
    (tu/with-terms [weighs Thing kg]
      ;; Thing has three weighings; two share the deep prefix (Qt 5 …)
      (v/assert kb (list weighs Thing (list 'Qt 5 kg))     'MantleContext {:strength :monotonic})
      (v/assert kb (list weighs Thing (list 'Qt 9 kg))     'MantleContext {:strength :monotonic})
      (v/assert kb (list weighs Thing (list 'Qt 5 'Gram))  'MantleContext {:strength :monotonic})
      (testing "a known prefix into a compound is costed by the deep trie level"
        ;; [weighs Thing <marker> Qt 5] narrows to 2; the old planner stopped at
        ;; [weighs Thing] and would have costed the whole extent, 3
        (is (= 3 (count (v/sentexes-matching kb (list weighs Thing '?w) '?ctx))) "the extent")
        (is (= 2 (:est-matches (first (plan/explain kb [(list weighs Thing (list 'Qt 5 '?u))]
                                                    'MantleContext)))))))))

;; ---- dedup + reindex -----------------------------------------------------

(deftest compound-argument-dedup-is-unaffected
  (tu/with-kb [kb]
    (tu/with-terms [weighs Thing kg]
      (let [h1 (v/assert kb (list weighs Thing (list 'QFn 7 kg)) 'MantleContext {:strength :monotonic})
            h2 (v/assert kb (list weighs Thing (list 'QFn 7 kg)) 'MantleContext {:strength :monotonic})]
        (is (= h1 h2) "re-asserting a compound-argument fact dedups to one handle")))))

(deftest a-rule-with-a-compound-antecedent-dedups
  ;; invariant #5, the rule side: a rule keeps its literals whole, so two spellings
  ;; that canonicalize alike (α-equivalent variables) still key to one handle
  (tu/with-kb [kb]
    (tu/with-terms [heavy weighs kg]
      (let [h1 (v/assert kb (list 'implies (list weighs '?x (list 'QFn '?n kg)) (list heavy '?x))
                         'MantleContext)
            h2 (v/assert kb (list 'implies (list weighs '?thing (list 'QFn '?amt kg)) (list heavy '?thing))
                         'MantleContext)]
        (is (= h1 h2) "α-equivalent rules with a compound antecedent dedup to one handle")))))

(deftest ragged-arity-with-markers-is-safe
  ;; invariant #2: a compound fact whose path is a proper prefix situation must not let
  ;; a whole-subterm skip cross into an unrelated node or read a marker as a handle
  (tu/with-kb [kb]
    (tu/with-terms [q F]
      (v/assert kb (list q (list F 'a))    'MantleContext {:strength :monotonic})   ; arity 1
      (v/assert kb (list q (list F 'a) 'b) 'MantleContext {:strength :monotonic})   ; arity 2, same F a
      (testing "a whole-subterm variable binds only same-arity facts"
        (is (= #{(list F 'a)}
               (into #{} (map '?y) (v/ask kb (list q '?y) '?ctx)))
            "(q ?y) matches only the arity-1 fact, binding the whole (F a)")
        (is (= #{(list F 'a)}
               (into #{} (map '?y) (v/ask kb (list q '?y 'b) '?ctx)))
            "(q ?y b) matches only the arity-2 fact"))
      (testing "the ground compound is retrievable at each arity"
        (is (= 1 (count (v/sentexes-matching kb (list q (list F 'a)) '?ctx))))
        (is (= 1 (count (v/sentexes-matching kb (list q (list F 'a) 'b) '?ctx))))))))

(deftest reindex-regenerates-the-structural-shape
  (tu/with-kb [kb]
    ;; the acceptance test: assert a corpus, reindex, and *every* pattern in the corpus
    ;; returns the identical result set — proving the index regenerates in the structural shape
    (let [results (fn [] (into {} (for [pat patterns]
                                    [pat (into #{} (map second)
                                               (res/match-pattern kb pat '?ctx))])))
          before (results)]
      (v/reindex kb)
      (is (= before (results)) "every corpus query is identical after a full index rebuild")
      (is (= 2 (count (v/sentexes-matching kb '(mass ?o (QuantityFn ?n Kilogram)) '?ctx)))))))

;; ---- toggle-off parity for flat patterns ---------------------------------

(deftest flat-patterns-are-untouched-by-the-toggle
  (tu/with-kb [kb]
    (doseq [pat '[(parentOf Tom ?y) (parentOf ?x Bob) (bornIn ?p 1970) (parentOf Tom Bob)]]
      (let [[off on] (both-ways #(res/match-pattern kb pat '?ctx))]
        (is (= off on) (str "flat pattern moved with the toggle: " (pr-str pat)))))))

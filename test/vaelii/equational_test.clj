;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.equational-test
  "Symbolic (schematic) equational reasoning — the gap docs/equality.md names.

  Two pieces, on top of ground congruence (which is already free — a `(equals a b)`
  over symbols rewrites every sentex mentioning `a`, at any nesting, via the inverted
  term index; see `ground-congruence-is-free` below):

  * **Part A — compound equality over reifiable NATs.**  `(equals (MotherOf Alice)
    (MotherOf Bob))` — *Alice and Bob have the same mother, so they are siblings* —
    is accepted when `MotherOf` is a `reifiableFunction`.  It reduces to ordinary
    individual equality: each side reifies to its constant *before* wff runs
    (docs/nat.md), so `(equals K1 K2)` merges in the partition and a fact about one
    holds of the other.  A compound equality that does **not** reduce — a structural NAT
    measure like `(QuantityFn 5 Kilogram)` — stays refused.

  * **Part B — schematic equational rules.**  `(equals (fatherOf (fatherOf ?x))
    (grandfatherOf ?x))` is an oriented rewrite `fatherOf∘fatherOf → grandfatherOf`.
    A stored `(parentChain (fatherOf (fatherOf Tom)))` normalizes to `(parentChain
    (grandfatherOf Tom))`, so a query on the `grandfatherOf` normal form matches.
    Oriented by a reduction order (strict size decrease + the variable condition), so
    rewriting terminates.

  Both are belief-following: every rewrite is a JTMS-justified twin, so retracting
  the equation collects the rewrites and revives the originals — exactly the
  discipline ground migration already has.

  House rules: gensym'd temporaries via `tu/with-terms`; engine vocabulary
  (`equals`, `reifiableFunction`, `QuantityFn`, `Kilogram`, contexts) literal; the
  neutral fixture asserts the KB is restored.  CxCore is loaded because the NAT
  bookkeeping (`termOfUnit`, `resultIsa`) rides real vocabulary."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.core-context :as core-context]
            [vaelii.impl.nat :as nat]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh #(doto (tu/fresh) (core-context/load-into))))

;; ---- baseline: ground congruence is already free ------------------------

(tu/deftest-kb ground-congruence-is-free
  ;; `(equals a b)` over two symbols rewrites every sentex naming `a` to `b` at any
  ;; nesting — no congruence algorithm, just the term index + migration.
  (tu/with-terms [bornIn Obama BarackObama Honolulu]
    (v/assert kb (list bornIn Obama Honolulu) 'CxUniverse)
    (v/assert kb (list 'equals Obama BarackObama) 'CxUniverse)
    (is (= [{'?c Honolulu}] (v/ask kb (list bornIn BarackObama '?c) '?ctx))
        "a fact about Obama holds of the merged BarackObama")))

;; ---- Part A: compound equality over reifiable NATs ----------------------

(tu/deftest-kb reifiable-compound-equality-merges-the-reified-nats
  ;; (equals (MotherOf Alice) (MotherOf Bob)): Alice and Bob share a mother.  Each
  ;; side reifies to a reified NAT constant before wff, so this is ordinary individual
  ;; equality — the two reified NATs merge and a fact about one holds of the other.
  (tu/with-terms [MotherOf Alice Bob livesIn NYC]
    (v/assert kb (list 'reifiableFunction MotherOf) 'CxUniverse)
    (v/assert kb (list livesIn (list MotherOf Alice) NYC) 'CxUniverse)
    (testing "before the merge, nothing is known about Bob's mother"
      (is (empty? (v/ask kb (list livesIn (list MotherOf Bob) '?c) '?ctx))))
    (let [h (v/assert kb (list 'equals (list MotherOf Alice) (list MotherOf Bob))
                      'CxUniverse)]
      (testing "the assertion is accepted, its sides reified to symbols"
        (is (some? h))
        (is (every? nat/reified-nat-symbol? (rest (:sentence (v/sentex kb h))))))
      (testing "the reified NATs merge — a fact about Alice's mother holds of Bob's"
        (is (= [{'?c NYC}] (v/ask kb (list livesIn (list MotherOf Bob) '?c) '?ctx))))
      (testing "and they resolve to one class"
        (is (v/same-class? kb
                           (nat/dedup-constant kb (list MotherOf Alice))
                           (nat/dedup-constant kb (list MotherOf Bob)))))
      (testing "retracting the equation is belief-following: Bob's mother separates,"
        (v/retract! kb h)
        (is (empty? (v/ask kb (list livesIn (list MotherOf Bob) '?c) '?ctx))))
      (testing "and Alice's own fact survives"
        (is (= [{'?c NYC}] (v/ask kb (list livesIn (list MotherOf Alice) '?c) '?ctx)))))))

(tu/deftest-kb structural-nat-compound-equality-is-refused
  ;; A structural NAT measure stays structural (never reified), so `(equals (QuantityFn …)
  ;; (QuantityFn …))` does not reduce to symbol equality and wff refuses the compound
  ;; — measure sameness is `sameQuantity`, a computed comparison, not the closure.
  (testing "equals over two ground QuantityFn measures is refused as not-well-formed"
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo #"compound"
         (v/assert kb '(equals (QuantityFn 5 Kilogram) (QuantityFn 5000 Gram))
                   'CxUniverse)))))

;; ---- Part B: schematic equational rules ---------------------------------

(defn- nest [f base n] (reduce (fn [t _] (list f t)) base (range n)))

(tu/deftest-kb schematic-rewrite-normalizes-store-and-query
  ;; (equals (fatherOf (fatherOf ?x)) (grandfatherOf ?x)) orients fatherOf∘fatherOf →
  ;; grandfatherOf; a stored (parentChain (fatherOf (fatherOf Tom))) normalizes so a
  ;; query on the grandfatherOf normal form matches.
  (tu/with-terms [fatherOf grandfatherOf parentChain Tom]
    (v/assert kb (list 'equals (list fatherOf (list fatherOf '?x)) (list grandfatherOf '?x))
              'CxUniverse)
    (v/assert kb (list parentChain (list fatherOf (list fatherOf Tom))) 'CxUniverse)
    (testing "the stored term meets a query at the grandfatherOf normal form"
      (is (seq (v/sentexes-matching kb (list parentChain (list grandfatherOf Tom)) 'CxUniverse))))
    (testing "a query on the pre-normal form still matches — the goal normalizes too"
      (is (seq (v/sentexes-matching kb (list parentChain (list fatherOf (list fatherOf Tom)))
                                    'CxUniverse))))
    (testing "ask binds through the normal form"
      (is (= [{'?y Tom}]
             (v/ask kb (list parentChain (list grandfatherOf '?y)) '?ctx))))))

(tu/deftest-kb schematic-rewrite-is-belief-following
  ;; Every rewrite is a JTMS-justified twin, so retracting the equation collects it and
  ;; the original revives — the same discipline ground migration has.
  (tu/with-terms [fatherOf grandfatherOf parentChain Tom]
    (let [he (v/assert kb (list 'equals (list fatherOf (list fatherOf '?x))
                                (list grandfatherOf '?x))
                       'CxUniverse)]
      (v/assert kb (list parentChain (list fatherOf (list fatherOf Tom))) 'CxUniverse)
      (is (seq (v/sentexes-matching kb (list parentChain (list grandfatherOf Tom)) 'CxUniverse)))
      (testing "retracting the equation drops the twin and revives the original"
        (v/retract! kb he)
        (is (empty? (v/sentexes-matching kb (list parentChain (list grandfatherOf Tom)) 'CxUniverse)))
        (is (seq (v/sentexes-matching kb (list parentChain (list fatherOf (list fatherOf Tom)))
                                      'CxUniverse)))))))

(tu/deftest-kb schematic-rewrite-terminates-on-a-cascade
  ;; The reduction order guarantees termination whatever the nesting depth: fatherOf^6
  ;; Tom reduces to grandfatherOf^3 Tom, and normalization does not hang.
  (tu/with-terms [fatherOf grandfatherOf ancestry Tom]
    (v/assert kb (list 'equals (list fatherOf (list fatherOf '?x)) (list grandfatherOf '?x))
              'CxUniverse)
    (v/assert kb (list ancestry (nest fatherOf Tom 6)) 'CxUniverse)
    (is (seq (v/sentexes-matching kb (list ancestry (nest grandfatherOf Tom 3)) 'CxUniverse)))))

(tu/deftest-kb schematic-rewrite-is-order-independent
  ;; Both migration paths converge on the same normal form: a fact asserted BEFORE the
  ;; equation is migrated when the rule arrives (migrate-matching); one asserted AFTER
  ;; is migrated on its own assert (migrate-sentex).  Two disjoint term sets exercise
  ;; each order in one KB.
  (tu/with-terms [pa gpa chaina TomA  pb gpb chainb TomB]
    (testing "rule then fact — the fact migrates when it arrives"
      (v/assert kb (list 'equals (list pa (list pa '?x)) (list gpa '?x)) 'CxUniverse)
      (v/assert kb (list chaina (list pa (list pa TomA))) 'CxUniverse)
      (is (seq (v/sentexes-matching kb (list chaina (list gpa TomA)) 'CxUniverse))))
    (testing "fact then rule — the stored fact migrates when the rule arrives"
      (v/assert kb (list chainb (list pb (list pb TomB))) 'CxUniverse)
      (v/assert kb (list 'equals (list pb (list pb '?x)) (list gpb '?x)) 'CxUniverse)
      (is (seq (v/sentexes-matching kb (list chainb (list gpb TomB)) 'CxUniverse))))))

(tu/deftest-kb prove-and-backward-normalize-the-goal
  ;; Parity: prove/backward now rewrite the top goal like query/ask, so a schematic
  ;; normal form — and a merged (retired) spelling — is answered there too, closing the
  ;; path-dependent-answer gap.
  (tu/with-terms [fatherOf grandfatherOf parentChain Tom  bornIn Keep Retire Hawaii]
    (v/assert kb (list 'equals (list fatherOf (list fatherOf '?x)) (list grandfatherOf '?x))
              'CxUniverse)
    (v/assert kb (list parentChain (list fatherOf (list fatherOf Tom))) 'CxUniverse)
    (testing "prove answers the grandfatherOf normal form"
      (is (seq (v/prove kb (list parentChain (list grandfatherOf Tom)) 'CxUniverse))))
    (testing "backward answers the pre-normal form — the goal normalizes"
      (is (seq (v/prove kb (list parentChain (list fatherOf (list fatherOf Tom)))
                        'CxUniverse))))
    ;; merged-spelling equality parity: rewriteOf makes Retire the deprecated spelling
    (v/assert kb (list bornIn Retire Hawaii) 'CxUniverse)
    (v/assert kb (list 'rewriteOf Keep Retire) 'CxUniverse)
    (testing "prove answers a goal under the retired spelling (goal rewrites to the rep)"
      (is (= [{'?c Hawaii}] (v/prove kb (list bornIn Retire '?c) 'CxUniverse))))))

(tu/deftest-kb schematic-rewrite-orients-equal-size-by-precedence
  ;; KBO orients an equal-size pair by the symbol precedence (where the old size-only
  ;; rule refused).  The direction is content-fixed, so both facts normalize to one
  ;; canonical form and collapse to a single believed sentex.
  (tu/with-terms [ff gg wrap Tom]
    (v/assert kb (list 'equals (list ff (list gg '?x)) (list gg (list ff '?x)))
              'CxUniverse)
    (v/assert kb (list wrap (list ff (list gg Tom))) 'CxUniverse)
    (v/assert kb (list wrap (list gg (list ff Tom))) 'CxUniverse)
    (is (= 1 (count (distinct (map :sentence
                                   (v/sentexes-matching kb (list wrap '?t) 'CxUniverse)))))
        "the two equal-size-related facts collapse to one normal form")))

(tu/deftest-kb schematic-rewrite-composes-with-symbol-merge
  ;; rewrite-term is symbol congruence THEN schematic normalization, so a schematic
  ;; term containing a merged symbol normalizes both in one pass — congruence and
  ;; rewriting compose.
  (tu/with-terms [fatherOf grandfatherOf parentChain Tom Thomas]
    (v/assert kb (list 'equals (list fatherOf (list fatherOf '?x)) (list grandfatherOf '?x))
              'CxUniverse)
    (v/assert kb (list parentChain (list fatherOf (list fatherOf Tom))) 'CxUniverse)
    (v/assert kb (list 'equals Tom Thomas) 'CxUniverse)      ; a symbol merge
    (let [rep (v/representative kb Tom)]
      (is (seq (v/sentexes-matching kb (list parentChain (list grandfatherOf rep)) 'CxUniverse))
          "the fact normalizes under both the merge (Tom→rep) and the rewrite (∘→gp)"))))

(tu/deftest-kb retracting-one-schematic-rule-leaves-the-other
  ;; The rule cache is belief-following per equation handle: dropping one rule stops
  ;; its normalization while another's stands.
  (tu/with-terms [pp gpp qq ggqq wrap Tom]
    (let [r1 (v/assert kb (list 'equals (list pp (list pp '?x)) (list gpp '?x)) 'CxUniverse)]
      (v/assert kb (list 'equals (list qq (list qq '?x)) (list ggqq '?x)) 'CxUniverse)
      (v/assert kb (list wrap (list pp (list pp Tom))) 'CxUniverse)
      (v/assert kb (list wrap (list qq (list qq Tom))) 'CxUniverse)
      (is (seq (v/sentexes-matching kb (list wrap (list gpp Tom)) 'CxUniverse)))
      (is (seq (v/sentexes-matching kb (list wrap (list ggqq Tom)) 'CxUniverse)))
      (testing "retracting the pp-rule stops its normalization but leaves the qq-rule's"
        (v/retract! kb r1)
        (is (empty? (v/sentexes-matching kb (list wrap (list gpp Tom)) 'CxUniverse)))
        (is (seq (v/sentexes-matching kb (list wrap (list ggqq Tom)) 'CxUniverse)))))))

(tu/deftest-kb conflicting-schematic-rules-surface-non-confluence
  ;; Two equations with the same LHS but different RHS disagree about a shared term.
  ;; Detection, not completion: nothing is dropped (the normal form stays
  ;; deterministic), but the conflict is surfaced in the violations ledger.
  (tu/with-terms [ff gg hh]
    (v/assert kb (list 'equals (list ff (list ff '?x)) (list gg '?x)) 'CxUniverse)
    (v/clear-violations! kb)
    (v/assert kb (list 'equals (list ff (list ff '?x)) (list hh '?x)) 'CxUniverse)
    (let [nc (filter #(= :non-confluent (:violation %)) (v/violations kb))]
      (is (seq nc) "the second equation conflicts with the first at their shared LHS")
      (is (every? :message nc)))))

(tu/deftest-kb disjoint-schematic-rules-report-no-conflict
  ;; Rules over different predicates never overlap, so no non-confluence is reported.
  (tu/with-terms [ff gg pp qq]
    (v/assert kb (list 'equals (list ff (list ff '?x)) (list gg '?x)) 'CxUniverse)
    (v/clear-violations! kb)
    (v/assert kb (list 'equals (list pp (list pp '?x)) (list qq '?x)) 'CxUniverse)
    (is (not-any? #(= :non-confluent (:violation %)) (v/violations kb)))))

(tu/deftest-kb permutative-schematic-equation-is-refused
  ;; A permutative equation has no terminating orientation under any term order, so it
  ;; is refused before anything is stored (KBO's honest limit — AC-rewriting is a
  ;; separate, larger mechanism).
  (tu/with-terms [rel]
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo #"orient"
         (v/assert kb (list 'equals (list rel '?x '?y) (list rel '?y '?x)) 'CxUniverse)))))

;; ---- the rule order is content, whatever the memo does ------------------

(defn- by-role
  "`form` with each temporary replaced by the role it plays, so two runs over disjoint
  gensym'd vocabularies compare as one shape."
  [m form]
  (if (sequential? form) (apply list (map #(by-role m %) form)) (get m form form)))

(tu/deftest-kb overlapping-schematic-rules-normalize-alike-either-order
  ;; Two equations sharing an LHS both apply to `ff∘ff`, so which one wins decides the
  ;; stored normal form.  `tax/rewrite-rules` orders by content, so the winner is a
  ;; function of the pair rather than of which equation was asserted first — the property
  ;; the memoized order has to preserve, since a memo keyed on anything the writer set
  ;; does not move would hand back the order the *first* read happened to see.
  ;;
  ;; Two disjoint term sets spelled alike, each loaded in one arrival order, compared
  ;; through `by-role` so the gensym'd names do not stand in the way.
  (tu/with-terms [ffa gga hha wrapa TomA  ffb ggb hhb wrapb TomB]
    (letfn [(landed [wrap m]
              (->> (v/sentexes-matching kb (list wrap '?t) 'CxUniverse)
                   (map #(by-role m (:sentence %)))
                   set))]
      (testing "the gg-equation first"
        (v/assert kb (list 'equals (list ffa (list ffa '?x)) (list gga '?x)) 'CxUniverse)
        (v/assert kb (list 'equals (list ffa (list ffa '?x)) (list hha '?x)) 'CxUniverse)
        (v/assert kb (list wrapa (list ffa (list ffa TomA))) 'CxUniverse))
      (testing "the hh-equation first"
        (v/assert kb (list 'equals (list ffb (list ffb '?x)) (list hhb '?x)) 'CxUniverse)
        (v/assert kb (list 'equals (list ffb (list ffb '?x)) (list ggb '?x)) 'CxUniverse)
        (v/assert kb (list wrapb (list ffb (list ffb TomB))) 'CxUniverse))
      (let [a (landed wrapa {ffa 'FF gga 'GG hha 'HH wrapa 'WRAP TomA 'TOM})
            b (landed wrapb {ffb 'FF ggb 'GG hhb 'HH wrapb 'WRAP TomB 'TOM})]
        (is (seq a) "the fact is stored under some normal form")
        (is (= a b) "and it is the same normal form in either arrival order")))))

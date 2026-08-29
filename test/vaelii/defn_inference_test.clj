;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.defn-inference-test
  "Query-time definitional *inference* — the piece `defns-test` assumed and vaelii did
  not have.  Two behaviours this suite pins, both TDD-red until the build lands:

  1. **Evaluative `defnSufficient`.**  A sufficient condition built from *computed*
     predicates (`integer`, `lessThan`, or any `add-evaluatable` check) must admit a
     member by **evaluating the condition at query time** — not only by a forward rule
     firing on an already-*believed* condition.  Computed conditions are never stored
     sentexes (see `evaluatable-test`), so the forward rule never fires and the member
     is never derived today.  This is the wall the `-212` predAll demo hit.

  2. **Admittance precedence + fast-fail over the genl lattice.**  A `defnSufficient`
     never admits a member that fails any `defnNecessary` of the collection or its
     genls (necessary wins).  The admittance walk checks each defn **once** on success
     and **short-circuits** on the first failing necessary — checking the most general
     necessary before descending to a spec's sufficient, and never re-checking a defn
     reachable by two genl paths.

  Call-counts are observed the honest way: each defn's condition is an `add-evaluatable`
  predicate backed by a counter atom, so the count is a side effect of the real
  admittance walk, not a peek into its internals.  See SCOPE-defn-inference.md."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- counted!
  "Register `pred` on `kb` as a 1-ary evaluatable check that increments `cnt` on every
  call and returns `ret`.  The counter is how we watch the admittance walk touch a defn."
  [kb pred cnt ret]
  (v/add-evaluatable kb pred (fn [_x] (swap! cnt inc) ret)))

;; ---- 1. evaluative defnSufficient: prove on query by evaluating the condition ----

(tu/deftest-kb sufficient-admits-by-evaluating-a-computed-condition
  ;; The core build.  `qualifies` is computed, never a stored fact, so the forward
  ;; rule (implies (qualifies ?x) (widget ?x)) has nothing to fire on.  Admittance
  ;; must EVALUATE the sufficient condition against the queried member.
  (tu/with-terms [widget qualifies]
    (v/add-evaluatable kb qualifies (fn [n] (> n 40)))
    (v/assert kb (list 'defnSufficient widget (list qualifies '?x)) 'CxUniverse)
    (is (v/ask? kb (list widget 42) 'CxUniverse)
        "42 qualifies, so evaluating the sufficient condition admits it — no stored membership needed")
    (is (not (v/ask? kb (list widget 10) 'CxUniverse))
        "10 does not qualify, so it is not admitted")))

(tu/deftest-kb sufficient-conjunction-of-computed-predicates-mirrors-negative-integer
  ;; The `-212` shape exactly: (and (integer ?x) (lessThan ?x 0)) as a defnSufficient,
  ;; both conjuncts computed.  `negative_integer` inherits this once the inference lands.
  (tu/with-terms [negnum isInt below0]
    (v/add-evaluatable kb isInt  integer?)
    (v/add-evaluatable kb below0 (fn [n] (neg? n)))
    (v/assert kb (list 'defnSufficient negnum
                       (list 'and (list isInt '?x) (list below0 '?x)))
              'CxUniverse)
    (is (v/ask? kb (list negnum -212) 'CxUniverse)
        "-212 is an integer below zero, so the evaluated sufficient condition admits it from the bare literal")
    (is (not (v/ask? kb (list negnum 7) 'CxUniverse))
        "7 is an integer but not below zero")))

;; ---- 2. precedence: a failing defnNecessary vetoes a satisfied defnSufficient ----

(tu/deftest-kb a-failing-necessary-vetoes-a-satisfied-sufficient
  ;; "when defnNecessary and defnSufficient fight, who wins?" — the necessary.
  (tu/with-terms [widget suff nec]
    (v/add-evaluatable kb suff (fn [_] true))
    (v/add-evaluatable kb nec  (fn [_] false))
    (v/assert kb (list 'defnSufficient widget (list suff '?x)) 'CxUniverse)
    (v/assert kb (list 'defnNecessary  widget (list nec  '?x)) 'CxUniverse)
    (is (not (v/ask? kb (list widget 7) 'CxUniverse))
        "the sufficient condition holds, but the failed necessary denies membership")))

(tu/deftest-kb every-genl-necessary-must-pass
  ;; admittance at the spec must satisfy the genl's necessary too (all genls checked).
  (tu/with-terms [animal dog dogSuff animalNec]
    (v/add-evaluatable kb dogSuff   (fn [_] true))
    (v/add-evaluatable kb animalNec (fn [_] false))       ; the genl's necessary fails
    (v/assert kb (list 'genl dog animal) 'CxUniverse)
    (v/assert kb (list 'defnSufficient dog    (list dogSuff   '?x)) 'CxUniverse)
    (v/assert kb (list 'defnNecessary  animal (list animalNec '?x)) 'CxUniverse)
    (is (not (v/ask? kb (list dog 7) 'CxUniverse))
        "dog's sufficient holds, but animal's necessary fails — a dog must be an animal")))

;; ---- 3. the genl diamond: dedup on admit, short-circuit on reject ----

(defn- diamond!
  "Build the diamond dbottom ⊏ {dmid_a,dmid_b} ⊏ dtop with a defnNecessary on all four and a
  defnSufficient on dbottom, each condition a counted evaluatable.  Returns the counters."
  [kb dtop dmid_a dmid_b dbottom topNec midANec midBNec bottomNec bottomSuff
   {:keys [top mida midb bottomn]}]
  (let [ct  (atom 0) ca (atom 0) cb (atom 0) cbn (atom 0) cbs (atom 0)]
    (counted! kb topNec     ct  top)
    (counted! kb midANec    ca  mida)
    (counted! kb midBNec    cb  midb)
    (counted! kb bottomNec  cbn bottomn)
    (counted! kb bottomSuff cbs true)
    (v/assert kb (list 'genl dbottom dmid_a) 'CxUniverse)
    (v/assert kb (list 'genl dbottom dmid_b) 'CxUniverse)
    (v/assert kb (list 'genl dmid_a dtop) 'CxUniverse)
    (v/assert kb (list 'genl dmid_b dtop) 'CxUniverse)
    (v/assert kb (list 'defnNecessary  dtop     (list topNec     '?x)) 'CxUniverse)
    (v/assert kb (list 'defnNecessary  dmid_a    (list midANec    '?x)) 'CxUniverse)
    (v/assert kb (list 'defnNecessary  dmid_b    (list midBNec    '?x)) 'CxUniverse)
    (v/assert kb (list 'defnNecessary  dbottom  (list bottomNec  '?x)) 'CxUniverse)
    (v/assert kb (list 'defnSufficient dbottom  (list bottomSuff '?x)) 'CxUniverse)
    {:top ct :mida ca :midb cb :bottomn cbn :bottomsuff cbs}))

(tu/deftest-kb diamond-admitted-evaluates-each-defn-exactly-once
  (tu/with-terms [dtop dmid_a dmid_b dbottom
                  topNec midANec midBNec bottomNec bottomSuff]
    (let [c (diamond! kb dtop dmid_a dmid_b dbottom
                      topNec midANec midBNec bottomNec bottomSuff
                      {:top true :mida true :midb true :bottomn true})]
      (is (v/ask? kb (list dbottom 42) 'CxUniverse)
          "42 satisfies dbottom's sufficient and every necessary in the diamond")
      (is (= 1 @(:bottomsuff c)) "dbottom's defnSufficient evaluated once")
      (is (= 1 @(:top c))     "dtop's defnNecessary evaluated once — deduped across the two genl paths")
      (is (= 1 @(:mida c))    "dmid_a's defnNecessary once")
      (is (= 1 @(:midb c))    "dmid_b's defnNecessary once")
      (is (= 1 @(:bottomn c)) "dbottom's defnNecessary once"))))

(tu/deftest-kb diamond-rejected-at-top-short-circuits-before-the-sides
  (tu/with-terms [dtop dmid_a dmid_b dbottom
                  topNec midANec midBNec bottomNec bottomSuff]
    (let [c (diamond! kb dtop dmid_a dmid_b dbottom
                      topNec midANec midBNec bottomNec bottomSuff
                      {:top false :mida true :midb true :bottomn true})] ; dtop's necessary fails
      (is (not (v/ask? kb (list dbottom 42) 'CxUniverse))
          "dtop's necessary fails, so 42 is not a dbottom")
      (is (= 1 @(:top c))   "dtop's defnNecessary checked exactly once — not >=1, no re-check on the fail path")
      (is (= 0 @(:mida c))  "dmid_a not checked — fast-fail short-circuits before the sides")
      (is (= 0 @(:midb c))  "dmid_b not checked")
      (is (= 0 @(:bottomsuff c)) "dbottom's sufficient not even tried once the top necessary fails"))))

;; ---- 4. characterization: pin what asking a defn collection of a literal does TODAY ----

(tu/deftest-kb pin-baseline-a-computed-sufficient-does-not-admit-a-literal-yet
  ;; Pace: "what currently happens when you ask (?pred 212)? pin it with a test, with a
  ;; comment about defns."  This assertion was pinned against the PRE-evaluative baseline
  ;; (a computed defnSufficient never fired forward, so the literal was not admitted) and
  ;; was designed to FLIP once `sufficient-admits-by-evaluating-a-computed-condition` went
  ;; green.  Phase A (query-time evaluative defnSufficient) is exactly that change, so it
  ;; is flipped here in the same commit: 12 is now admitted by EVALUATING `(under 12)`
  ;; against the queried literal, no stored membership and no forward firing needed.
  (tu/with-terms [small under]
    (v/add-evaluatable kb under (fn [n] (< n 100)))
    (v/assert kb (list 'defnSufficient small (list under '?x)) 'CxUniverse)
    (is (v/ask? kb (list small 12) 'CxUniverse)
        "POST-Phase-A: the computed sufficient condition (under 12) is evaluated at query time and admits literal 12; no forward defn rule fires, no membership is stored.")))

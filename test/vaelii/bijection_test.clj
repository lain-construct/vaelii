;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.bijection-test
  "`bijection`, the two-directions composite mark shipped in CxCore: no engine code,
  two CxCore forward rules derive `(functional P)` and `(functionalInArg P 1)`, each a
  real mark the engine enforces in turn — `equivalence_relation`'s pattern, over the
  functional family.

  Behaviourally that is one-to-one: a shared first argument merges-or-refuses its two
  second-argument fillers (the `functional` half), and a shared second argument does
  the same to its two first-argument fillers (the `functionalInArg 1` half).  The
  merge/refuse rule itself is `functional`'s and is tested exhaustively in
  `functional-in-arg-test`; what is tested here is that the SHIPPED declaration wires
  both directions, and that the wiring is belief-following — retracting the one
  declaration drops both derived marks.

  Four dimensions beyond the wiring, each one a derived mark could lose without the
  wiring tests noticing: both arrival orders (the declaration before the pair, and after
  it), the merge and the refusal, the reach up the predicate hierarchy, and the
  decontextualization that makes the declaration the whole KB's claim.

  A CxCore-loaded KB throughout, like `relation-properties-test`: the shipped
  declarations are what is tested, not a hand-built fixture that could drift from the
  file."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.core-context :as core-context]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh #(doto (tu/fresh) (core-context/load-into))))

(defn- ex-type
  "The `:type` on the ex-info a thunk throws, or nil if it does not throw."
  [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))

(def ^:private U 'CxUniverse)

;;; ── the shipped declaration ───────────────────────────────────────────

(tu/deftest-kb cxcore-declares-bijection
  (testing "the term carries its comment sentex like any other CxCore entry"
    (is (= 1 (count (core-context/comment-of kb 'bijection))))
    (is (string? (first (core-context/comment-of kb 'bijection)))))
  (testing "and the classification half: a bijection is a binary_predicate"
    (tu/with-terms [capitalCityOf]
      (v/assert kb (list 'bijection capitalCityOf) U)
      (is (v/ask? kb (list 'binary_predicate capitalCityOf) U)))))

;;; ── the two marks, derived — no engine code ───────────────────────────

(tu/deftest-kb a-bijection-derives-functional-and-functional-in-arg-1
  (tu/with-terms [capitalCityOf]
    (v/assert kb (list 'bijection capitalCityOf) U)
    (testing "the two marks are derived"
      (is (v/ask? kb (list 'functional capitalCityOf) U))
      (is (v/ask? kb (list 'functionalInArg capitalCityOf 1) U)))))

(tu/deftest-kb retracting-the-bijection-declaration-drops-the-two-marks
  (tu/with-terms [capitalCityOf]
    (let [decl (v/assert kb (list 'bijection capitalCityOf) U)]
      (is (v/ask? kb (list 'functional capitalCityOf) U))
      (v/retract! kb decl)
      (testing "the derived marks rested on the declaration and go with it"
        (is (not (v/ask? kb (list 'functional capitalCityOf) U)))
        (is (not (v/ask? kb (list 'functionalInArg capitalCityOf 1) U)))))))

;;; ── each derived mark is enforced in turn, behaviourally ──────────────

(tu/deftest-kb a-bijection-merges-two-symbol-fillers-in-either-direction
  (tu/with-terms [capitalCityOf]
    (v/assert kb (list 'bijection capitalCityOf) U)
    (testing "a shared first argument merges its two symbol fillers — the functional half"
      (tu/with-terms [Freedonia]
        (let [[lo hi] (sort [(tu/tmp-ind "Fredville") (tu/tmp-ind "Fredville")])]
          (v/assert kb (list capitalCityOf Freedonia lo) U)
          (v/assert kb (list capitalCityOf Freedonia hi) U)
          (is (v/same-class? kb lo hi)
              "two names for one capital are one thing, as under (functional P)"))))
    (testing "a shared second argument merges its two — the functionalInArg 1 half"
      (tu/with-terms [Fredopolis]
        (let [[lo hi] (sort [(tu/tmp-ind "Sylvania") (tu/tmp-ind "Sylvania")])]
          (v/assert kb (list capitalCityOf lo Fredopolis) U)
          (v/assert kb (list capitalCityOf hi Fredopolis) U)
          (is (v/same-class? kb lo hi)
              "two names for one country are one thing, via (functionalInArg P 1)"))))))

(tu/deftest-kb a-bijection-refuses-two-unmergeable-fillers-in-either-direction
  (tu/with-terms [pRel Ruritania]
    (v/assert kb (list 'bijection pRel) U)
    (testing "a second number at argument 2 for one argument 1 is refused"
      (v/assert kb (list pRel Ruritania 1980) U)
      (is (= :functional (ex-type #(v/assert kb (list pRel Ruritania 1990) U)))
          "no merge can make 1980 and 1990 one thing"))
    (testing "and a second number at argument 1 for one argument 2 is refused the same"
      (tu/with-terms [Zenda]
        (v/assert kb (list pRel 7 Zenda) U)
        (is (= :functional (ex-type #(v/assert kb (list pRel 8 Zenda) U)))
            "the mirrored refusal, via the derived (functionalInArg P 1)")))))

;;; ── the declaration reaches back over content already stored ──────────

(tu/deftest-kb a-bijection-declared-after-an-unmergeable-pair-convicts-that-pair
  ;; The arrival order the mark family gets wrong when a spelling reaches the sweep
  ;; through only some of its readers (#45): the pair is stored first and the
  ;; declaration second, so nothing refuses at the entry point and what has to convict
  ;; is the retroactive pass.  Both halves are derived here rather than written, so the
  ;; pass runs against a conclusion of a rule.
  (tu/with-terms [pRel Ruritania]
    (v/assert kb (list pRel Ruritania 1980) U)
    (v/assert kb (list pRel Ruritania 1990) U)
    (v/assert kb (list 'bijection pRel) U)
    (is (= [:functional] (mapv :violation (v/violations kb)))
        "the stored pair sharing argument 1 is convicted by the derived (functional P)")))

(tu/deftest-kb a-late-bijection-convicts-a-stored-pair-sharing-argument-2
  (tu/with-terms [pRev Zenda]
    (v/assert kb (list pRev 7 Zenda) U)
    (v/assert kb (list pRev 8 Zenda) U)
    (v/assert kb (list 'bijection pRev) U)
    (is (= [:functional] (mapv :violation (v/violations kb)))
        "the mirrored conviction, by the derived (functionalInArg P 1)")))

(tu/deftest-kb a-late-bijection-merges-two-mergeable-fillers-in-either-direction
  (testing "a stored pair sharing argument 1"
    (tu/with-terms [pRel Freedonia]
      (let [[lo hi] (sort [(tu/tmp-ind "Fredville") (tu/tmp-ind "Fredville")])]
        (v/assert kb (list pRel Freedonia lo) U)
        (v/assert kb (list pRel Freedonia hi) U)
        (v/assert kb (list 'bijection pRel) U)
        (is (v/same-class? kb lo hi)))))
  (testing "and a stored pair sharing argument 2"
    (tu/with-terms [pRev Fredopolis]
      (let [[lo hi] (sort [(tu/tmp-ind "Sylvania") (tu/tmp-ind "Sylvania")])]
        (v/assert kb (list pRev lo Fredopolis) U)
        (v/assert kb (list pRev hi Fredopolis) U)
        (v/assert kb (list 'bijection pRev) U)
        (is (v/same-class? kb lo hi))))))

;;; ── the two derived marks descend the predicate hierarchy ─────────────

(tu/deftest-kb a-bijection-on-a-super-predicate-convicts-a-sub-predicate-pair
  ;; Both derived marks are read up the predicate hierarchy, as every constraint mark
  ;; is, so the declaration is written once at the general predicate.  The query does
  ;; not descend — `(functional fatherOf)` is false — and the enforcement does, which is
  ;; the distinction taxonomy.md draws between a mark's classification and its reach.
  (tu/with-terms [parentOf fatherOf Ann Bob]
    (v/assert kb (list 'bijection parentOf) U)
    (v/assert kb (list 'genl fatherOf parentOf) U)
    (is (not (v/ask? kb (list 'functional fatherOf) U))
        "the sub-predicate is not itself classified functional")
    (v/assert kb (list fatherOf Ann 1980) U)
    (is (= :functional (ex-type #(v/assert kb (list fatherOf Ann 1990) U)))
        "and is enforced anyway, at argument 2")
    (v/assert kb (list fatherOf 7 Bob) U)
    (is (= :functional (ex-type #(v/assert kb (list fatherOf 8 Bob) U)))
        "and at argument 1")))

;;; ── the declaration is decontextualized ───────────────────────────────

(tu/deftest-kb a-bijection-stated-in-one-theory-is-the-whole-kb-s-claim
  ;; `bijection` is a `decontextualized_predicate`, so the declaration is the KB's claim
  ;; about the predicate rather than the theory's — and the two marks derived from it
  ;; reach CxUniverse with it.
  (tu/with-terms [pRel CxStory]
    (v/assert kb (list 'genlCx CxStory U) U)
    (v/assert kb (list 'bijection pRel) CxStory)
    (is (v/ask? kb (list 'bijection pRel) U))
    (is (v/ask? kb (list 'functional pRel) U))
    (is (v/ask? kb (list 'functionalInArg pRel 1) U))))

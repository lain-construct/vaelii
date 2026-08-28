;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.order-independence-test
  "The definitional checks — `functional`, `antiSymmetric`, `disjoint` — hold the
  order-independence invariant on two of its three axes and miss the third.

  The invariant is the project's own, stated in `special/equate-existing`:

      A declaration has to reach the facts already stored exactly as it reaches the
      facts that follow ... an answer that depended on whether the schema or the facts
      were loaded first would be an answer about the file.

  Three arrivals can complete a clash, because a clash needs three things present: the
  declaration, both facts, and a path that makes the two facts visible together.
  Whichever arrives last, the conclusion should be the same.

  - **The declaration arrives last** — handled, by `equate-existing`.
  - **The predicate edge arrives last** (`genl sub super`, which makes two `fatherOf`
    fillers two `parentOf` values) — handled, by the `genl`-arrival twin.
  - **The context edge arrives last** (`genlCx a b`, which makes a context able to see
    facts stored in another) — **not handled.**

  And the same gap read from the other side: a context that could see both facts *from
  the start* never evaluates the constraint either, because the check runs once, in the
  asserting context, at assert time.

  This namespace is deliberately **red**. The `control-` tests pass and exist to prove
  the instrument is live — without them a green \"no contradiction\" result cannot be
  told from a probe that never engaged the check at all, which is exactly how the first
  draft of the disjointness case fooled its author. Everything else asserts the
  invariant and fails today. See the issue this namespace accompanies.

  Nothing here is a proposal about *what* the fixed behaviour should be. Whether a
  clash seen from a vantage becomes a represented contradiction, a derived equality, or
  a refusal is a design decision for vaelii-admin; these tests take the position only
  that the answer must not depend on the order the three ingredients arrived in."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.checks :as checks]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(def ^:private U 'CxUniverse)

(defmacro ^:private with-entailing
  "Assertive argument types on — what makes a `disjoint` membership clash bite."
  [& body]
  `(binding [checks/*assertive-arg-types?* true] ~@body))

(defn- a-type
  "Declare `t` a type: an edge to `thing`, which is what makes a membership in it
  mintable at all. Without this a `disjoint` pair is inert and every test about it
  passes for the wrong reason."
  [kb t ctx]
  (v/assert kb (list 'genl t 'thing) ctx))

(defn- a-context [kb ctx] (v/assert kb (list 'genlCx ctx U) U))

(defn- siblings!
  "Two contexts under CxUniverse and blind to each other."
  [kb & cs]
  (doseq [c cs] (a-context kb c)))

;; ---- the premise: the facts really are jointly readable ------------------
;; Every test below turns on this. If the two facts were not visible together from the
;; lower context there would be no clash to miss, and the engine's silence would be
;; correct rather than incomplete.

(tu/deftest-kb the-two-facts-are-jointly-visible-from-the-context-below
  (tu/with-terms [motherOf Tom A B CxLeft CxRight CxBottom]
    (siblings! kb CxLeft CxRight CxBottom)
    (doseq [s [CxLeft CxRight]]
      (v/assert kb (list 'genlCx CxBottom s) U))
    (v/assert kb (list motherOf Tom A) CxLeft)
    (v/assert kb (list motherOf Tom B) CxRight)
    (let [from (fn [ctx] (set (map #(get % '?v)
                                   (v/query kb (list motherOf Tom '?v) ctx))))]
      (is (= #{A B} (from CxBottom))
          "the vantage below sees both fillers")
      (is (= #{A} (from CxLeft))
          "and neither sibling sees the other's, so each is individually consistent"))))

;; ---- controls: the invariant working, on the two axes it covers ----------

(tu/deftest-kb control-functional-clashes-within-one-context
  (testing "two symbols merge"
    (tu/with-terms [motherOf Tom]
      (let [[lo hi] (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])]
        (v/assert kb (list 'functional motherOf) U)
        (v/assert kb (list motherOf Tom lo) U)
        (v/assert kb (list motherOf Tom hi) U)
        (is (v/same-class? kb lo hi)))))
  (testing "two numbers are refused outright"
    (tu/with-neutral-kb [kb2 tu/isolated-fresh]
      (tu/with-terms [birthYear Tom]
        (v/assert kb2 (list 'functional birthYear) U)
        (v/assert kb2 (list birthYear Tom 1980) U)
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/assert kb2 (list birthYear Tom 1990) U)))))))

(tu/deftest-kb control-the-declaration-arriving-last-still-merges
  ;; Axis 1, and the one `equate-existing` was written for: the facts are stored first
  ;; and the `(functional P)` declaration lands on top of them.
  (tu/with-terms [motherOf Tom]
    (let [[lo hi] (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])]
      (v/assert kb (list motherOf Tom lo) U)
      (v/assert kb (list motherOf Tom hi) U)
      (is (not (v/same-class? kb lo hi)) "nothing is declared yet")
      (v/assert kb (list 'functional motherOf) U)
      (is (v/same-class? kb lo hi)
          "the declaration reaches the facts already stored"))))

(tu/deftest-kb control-the-predicate-edge-arriving-last-still-merges
  ;; Axis 2. `(functional parentOf)` is declared and both fillers are stored, but
  ;; `fatherOf` is not yet beneath `parentOf`, so they are not yet two `parentOf`
  ;; values. The `genl` edge is the last ingredient and its arrival re-derives.
  (tu/with-terms [parentOf fatherOf Tom A B]
    (v/assert kb (list 'functional parentOf) U)
    (v/assert kb (list fatherOf Tom A) U)
    (v/assert kb (list fatherOf Tom B) U)
    (is (not (v/same-class? kb A B))
        "no edge yet, so these are not two values of the marked predicate")
    (v/assert kb (list 'genl fatherOf parentOf) U)
    (is (v/same-class? kb A B)
        "the edge is the last ingredient and the merge follows it")))

(tu/deftest-kb control-antisymmetric-merges-within-one-context
  (tu/with-terms [ranks X Y]
    (v/assert kb (list 'antiSymmetric ranks) U)
    (v/assert kb (list ranks X Y) U)
    (v/assert kb (list ranks Y X) U)
    (is (v/same-class? kb X Y)
        "a believed converse under antiSymmetric derives the equality")))

(tu/deftest-kb control-disjoint-refuses-within-one-context
  (tu/with-terms [animal rock Rex]
    (with-entailing
      (a-type kb animal U)
      (a-type kb rock U)
      (v/assert kb (list 'disjoint animal rock) U)
      (v/assert kb (list animal Rex) U)
      (is (thrown? clojure.lang.ExceptionInfo (v/assert kb (list rock Rex) U))
          "the second membership is refused — if this passes, every disjoint test
           below is passing for the wrong reason"))))

;; ---- axis 3: the context edge arriving last -----------------------------
;; Pace's construction. Assert the conflicting facts while the two contexts are
;; disjoint, then add the edge that lets one see the other.

(tu/deftest-kb functional-a-context-edge-arriving-last-should-complete-the-clash
  (tu/with-terms [motherOf Tom A B CxMorningStar CxEveningStar]
    (siblings! kb CxMorningStar CxEveningStar)
    (v/assert kb (list 'functional motherOf) U)
    (v/assert kb (list motherOf Tom A) CxMorningStar)
    (v/assert kb (list motherOf Tom B) CxEveningStar)
    (is (not (v/same-class? kb A B))
        "before the edge the two contexts are blind to each other")
    (v/assert kb (list 'genlCx CxMorningStar CxEveningStar) U)
    (testing "the facts are now jointly visible from CxMorningStar"
      (is (= #{A B} (set (map #(get % '?v)
                              (v/query kb (list motherOf Tom '?v) CxMorningStar))))))
    (testing "so the clash is complete, exactly as it is when a genl edge lands last"
      (is (some? (v/handle-of kb (list 'equals A B) CxMorningStar))
          "VIOLATION: the context edge completed the clash and nothing re-derived"))))

(tu/deftest-kb functional-an-unmergeable-clash-across-contexts-should-be-represented
  ;; The two-numbers case. Within one context this is a hard refusal; across contexts
  ;; there is nothing to refuse — both facts are already stored and each is fine where
  ;; it stands — so the vantage that sees both is where it has to show up.
  (tu/with-terms [birthYear Tom CxMorningStar CxEveningStar]
    (siblings! kb CxMorningStar CxEveningStar)
    (v/assert kb (list 'functional birthYear) U)
    (v/assert kb (list birthYear Tom 1980) CxMorningStar)
    (v/assert kb (list birthYear Tom 1990) CxEveningStar)
    (v/assert kb (list 'genlCx CxMorningStar CxEveningStar) U)
    (is (= #{1980 1990} (set (map #(get % '?v)
                                  (v/query kb (list birthYear Tom '?v) CxMorningStar))))
        "both fillers read back from the context below")
    (is (seq (v/contradictions kb))
        "VIOLATION: no merge can make 1980 and 1990 one thing, and no contradiction
         is recorded either — the clash is neither resolved nor represented")))

(tu/deftest-kb antisymmetric-a-context-edge-arriving-last-should-complete-the-clash
  (tu/with-terms [ranks X Y CxMorningStar CxEveningStar]
    (siblings! kb CxMorningStar CxEveningStar)
    (v/assert kb (list 'antiSymmetric ranks) U)
    (v/assert kb (list ranks X Y) CxMorningStar)
    (v/assert kb (list ranks Y X) CxEveningStar)
    (v/assert kb (list 'genlCx CxMorningStar CxEveningStar) U)
    ;; bound first: `clojure.test` prints the asserted form with its arguments
    ;; evaluated, so a bare `(is (v/same-class? kb X Y))` dumps the whole KB record into
    ;; the report and buries the one bit that matters.
    (let [merged? (boolean (v/same-class? kb X Y))]
      (is merged?
          "VIOLATION: the converse became visible and no equality was derived"))))

(tu/deftest-kb disjoint-a-context-edge-arriving-last-should-complete-the-clash
  (tu/with-terms [animal rock Rex CxMorningStar CxEveningStar]
    (with-entailing
      (siblings! kb CxMorningStar CxEveningStar)
      (a-type kb animal U)
      (a-type kb rock U)
      (v/assert kb (list 'disjoint animal rock) U)
      (v/assert kb (list animal Rex) CxMorningStar)
      (v/assert kb (list rock Rex) CxEveningStar)
      (v/assert kb (list 'genlCx CxMorningStar CxEveningStar) U)
      (is (and (v/ask? kb (list animal Rex) CxMorningStar)
               (v/ask? kb (list rock Rex) CxMorningStar))
          "both memberships read back from the context below")
      (is (seq (v/contradictions kb))
          "VIOLATION: Rex is an animal and a rock from one vantage, and nothing says so"))))

;; ---- the same gap from the other side: wired up front -------------------
;; Here no edge arrives late at all. The lower context could see both facts from the
;; moment each was asserted; the check simply never runs from there.

(tu/deftest-kb functional-a-vantage-below-two-blind-siblings-should-see-the-clash
  (tu/with-terms [motherOf Tom A B CxLeft CxRight CxBottom]
    (siblings! kb CxLeft CxRight CxBottom)
    (doseq [s [CxLeft CxRight]]
      (v/assert kb (list 'genlCx CxBottom s) U))
    (v/assert kb (list 'functional motherOf) U)
    (v/assert kb (list motherOf Tom A) CxLeft)
    (v/assert kb (list motherOf Tom B) CxRight)
    (testing "neither sibling concludes anything, which is correct"
      (is (nil? (v/handle-of kb (list 'equals A B) CxLeft))))
    (is (some? (v/handle-of kb (list 'equals A B) CxBottom))
        "VIOLATION: CxBottom sees both fillers and derives nothing from them")))

(tu/deftest-kb a-clash-no-context-can-see-is-correctly-not-a-clash
  ;; The converse, and the reason none of the above can be fixed by simply checking
  ;; globally. Two mutually blind leaves with nothing beneath them: no vantage exists
  ;; from which both facts are present, so there is nothing to report and reporting
  ;; something would be the bug.
  ;;
  ;; NOTE: this test passes today, but **vacuously** — with no cross-context detection
  ;; at all it cannot distinguish correct behaviour from the absent feature. It becomes
  ;; load-bearing only once the tests above are green.
  (tu/with-terms [motherOf Tom A B CxLeft CxRight]
    (siblings! kb CxLeft CxRight)
    (v/assert kb (list 'functional motherOf) U)
    (v/assert kb (list motherOf Tom A) CxLeft)
    (v/assert kb (list motherOf Tom B) CxRight)
    (is (not (v/same-class? kb A B))
        "no context sees both, so the clash does not exist to be had")
    (is (empty? (v/contradictions kb)))))
